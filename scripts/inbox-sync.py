#!/usr/bin/env python3
"""Keep the `inbox` label on the pull requests that are waiting for a first review.

The inbox workflow runs this from its trusted checkout: for one pull request when it is opened,
reopened, marked ready for review, turned back into a draft or closed, and for every open pull
request every fifteen minutes. Nothing from a pull request is checked out or run. Everything is read from
GitHub's API, and the only thing written is the label.

A pull request can be in the inbox when it is open, is not a draft, is not a batch, and carries
none of `batch queue`, `building` and `awaiting-author`. A batch is a pull request from a branch
named `batch/...`, in this repository or a fork. It leaves the inbox at the first review after it
went in, by someone with triage access or more. Any submitted review counts, whether it approves,
requests changes or only comments. Reviews by the pull request's author or by a bot do not.

Opening, reopening or marking a pull request ready puts it in the inbox, whatever happened to it
before. Otherwise a pull request without the label gets it only if nobody with triage access has
reviewed it and no person has taken the label off it. A maintainer who removes `inbox` by hand is
not overruled, and one who puts it back asks for another look: it stays until the next review.

Reviews on pull requests from forks only get a read-only token, so the workflow cannot act on
them as they are submitted. The sweep picks them up instead. It reads every open pull request
through GraphQL, a few requests in all, whose allowance is separate from the REST one that the
batch queue counts on. Before it puts a pull request in the inbox it reads that pull request
again, so that a review or a close that came in meanwhile is not missed. Access is looked up
through REST, once a run for each reviewer.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys

INBOX = "inbox"
# Labels that mean a maintainer has already decided what happens next.
DECIDED = ("batch queue", "building", "awaiting-author")
PREFIX = "batch/"
# Events that put a pull request in the inbox whatever happened to it before.
ENTRY = ("opened", "reopened", "ready_for_review")
# Repository roles whose review takes a pull request out of the inbox. The REST API reports
# maintain as write and triage as read under `permission`, so `role_name` is the one to read.
ROLES = ("admin", "maintain", "write", "triage")

# The latest 50 reviews and 100 label changes are enough for any pull request here.
FIELDS = """
  number state isDraft headRefName
  author { login }
  labels(first: 100) { nodes { name } }
  reviews(last: 50) { nodes { state submittedAt author { __typename login } } }
  timelineItems(last: 100, itemTypes: [LABELED_EVENT, UNLABELED_EVENT]) {
    nodes {
      __typename
      ... on LabeledEvent { createdAt label { name } actor { __typename login } }
      ... on UnlabeledEvent { createdAt label { name } actor { __typename login } }
    }
  }
"""
EVERY = """query($owner: String!, $name: String!, $after: String) {
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: 100, after: $after) {
      pageInfo { hasNextPage endCursor }
      nodes { %s }
    }
  }
}""" % FIELDS
ONE = """query($owner: String!, $name: String!, $number: Int!) {
  repository(owner: $owner, name: $name) { pullRequest(number: $number) { %s } }
}""" % FIELDS


class Refused(Exception):
    """Something is wrong with the repository that this script should not paper over."""


class GitHub:
    """GitHub's API through `gh`. With `dry_run`, label changes are printed, not sent."""

    def __init__(self, repo, dry_run=False):
        self.repo, self.dry_run = repo, dry_run
        self.owner, _, self.name = repo.partition("/")
        self.calls, self.remaining, self.access, self.failed = 0, None, {}, False

    def run(self, args, payload=None):
        data = json.dumps(payload).encode() if payload is not None else None
        done = subprocess.run(["gh", "api", *args], input=data, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE)
        self.calls += 1
        return done

    def call(self, method, path, payload=None):
        """One REST request. Returns (HTTP status, decoded body or None)."""
        args = ["--include", "--method", method, f"repos/{self.repo}/{path}"]
        if payload is not None:
            args += ["--input", "-"]
        done = self.run(args, payload)
        head, _, body = done.stdout.decode("utf-8", "replace").replace("\r\n", "\n").partition("\n\n")
        try:
            status = int(head.split()[1])
        except (IndexError, ValueError):
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            raise RuntimeError(f"no answer from GitHub for {method} {path}") from None
        for line in head.splitlines()[1:]:
            name, _, value = line.partition(":")
            if name.strip().lower() == "x-ratelimit-remaining" and value.strip().isdigit():
                self.remaining = int(value)
        return status, (json.loads(body) if body.strip() else None)

    def graphql(self, query, **variables):
        done = self.run(["graphql", "--input", "-"], {"query": query, "variables": variables})
        try:
            answer = json.loads(done.stdout)
        except json.JSONDecodeError:
            answer = None
        if not isinstance(answer, dict) or answer.get("errors") or done.returncode != 0:
            sys.stderr.write(done.stderr.decode("utf-8", "replace"))
            found = (answer or {}).get("errors") if isinstance(answer, dict) else None
            raise RuntimeError(f"GraphQL query failed: {json.dumps(found) if found else 'no answer'}")
        return answer["data"]

    def pulls(self):
        """Every open pull request."""
        found, after = [], None
        while True:
            page = self.graphql(EVERY, owner=self.owner, name=self.name, after=after)
            page = page["repository"]["pullRequests"]
            found += [pull(node) for node in page["nodes"]]
            if not page["pageInfo"]["hasNextPage"]:
                return found
            after = page["pageInfo"]["endCursor"]

    def pull(self, number):
        """One pull request, open or not, or None if there is no such pull request."""
        node = self.graphql(ONE, owner=self.owner, name=self.name, number=number)
        node = node["repository"]["pullRequest"]
        return pull(node) if node else None

    def can_triage(self, login):
        """Whether `login` has triage access or more to this repository."""
        if login not in self.access:
            status, found = self.call("GET", f"collaborators/{login}/permission")
            if status == 404:
                self.access[login] = False
            elif status != 200:
                raise RuntimeError(f"could not read the access {login} has to {self.repo}: {status}")
            else:
                self.access[login] = (found.get("role_name") in ROLES
                                      or found.get("permission") in ("admin", "write"))
        return self.access[login]

    def label_exists(self):
        status, _ = self.call("GET", f"labels/{INBOX}")
        if status not in (200, 404):
            raise RuntimeError(f"GET labels/{INBOX} answered {status}")
        return status == 200

    def label(self, number, add):
        verb = "add" if add else "remove"
        if self.dry_run:
            print(f"would {verb} {INBOX} on #{number}")
            return
        if add:
            status, _ = self.call("POST", f"issues/{number}/labels", {"labels": [INBOX]})
        else:
            status, _ = self.call("DELETE", f"issues/{number}/labels/{INBOX}")
        # Taking off a label that someone else has just taken off answers 404.
        if status not in (200, 201) and not (status == 404 and not add):
            raise RuntimeError(f"could not {verb} {INBOX} on #{number}: {status}")


def when(text):
    return datetime.datetime.fromisoformat(text.replace("Z", "+00:00"))


def person(actor):
    """The login of a person, or None for a bot or a deleted account."""
    if not actor or actor.get("__typename") == "Bot":
        return None
    return actor.get("login")


def pull(node):
    """What this script needs to know about a pull request, from GraphQL's answer."""
    # Label changes come oldest first, so the last of each kind is the latest.
    added = removed_by = None
    for item in node["timelineItems"]["nodes"]:
        if (item.get("label") or {}).get("name") != INBOX:
            continue
        if item["__typename"] == "LabeledEvent":
            added = when(item["createdAt"])
        else:
            removed_by = person(item.get("actor"))
    reviews = []
    for review in node["reviews"]["nodes"]:
        login = person(review.get("author"))
        if login and review.get("submittedAt") and review.get("state") != "PENDING":
            reviews.append({"login": login, "at": when(review["submittedAt"])})
    return {
        "number": node["number"], "open": node["state"] == "OPEN", "draft": node["isDraft"],
        "ref": node["headRefName"], "author": (node.get("author") or {}).get("login"),
        "labels": {label["name"] for label in node["labels"]["nodes"]},
        "reviews": reviews, "added": added, "removed_by": removed_by,
    }


def unavailable(pr):
    """Why the pull request cannot be in the inbox at all, or None if it can."""
    if pr["draft"]:
        return "it is a draft"
    if pr["ref"].startswith(PREFIX):
        return "it is a batch"
    decided = [label for label in DECIDED if label in pr["labels"]]
    if decided:
        return "it is labelled " + " and ".join(f"`{label}`" for label in decided)
    return None


def reviewer(gh, pr, since=None):
    """Someone with triage access who reviewed the pull request after `since`, or None.

    Every reviewer's access is looked up. Their `authorAssociation` would be cheaper, but GitHub
    reports a private member of the organisation as a mere contributor to a token that cannot see
    the membership, and the workflow's token is one of those.
    """
    for review in pr["reviews"]:
        if review["login"] == pr["author"]:
            continue
        if since and review["at"] <= since:
            continue
        if gh.can_triage(review["login"]):
            return review["login"]
    return None


def decide(gh, pr, event=None):
    """What to do with the label: ("add" or "remove" or None, and why)."""
    has = INBOX in pr["labels"]
    if not pr["open"]:
        return ("remove" if has else None), "it is closed"
    why = unavailable(pr)
    if why:
        return ("remove" if has else None), why
    if event in ENTRY:
        return (None if has else "add"), "it was " + {"opened": "opened", "reopened": "reopened",
                                                       "ready_for_review": "marked ready"}[event]
    # When the label is on, only reviews after it went on count. Without the label, any does.
    who = reviewer(gh, pr, pr["added"] if has else None)
    if has:
        return ("remove", f"{who} reviewed it") if who else (None, "it is waiting for a review")
    if who:
        return None, f"{who} has reviewed it"
    if pr["removed_by"]:
        return None, f"{pr['removed_by']} took it out of the inbox"
    return "add", "it is waiting for a review"


def sync(gh, number=None, event=None):
    """Bring the label up to date on one pull request, or on all open ones. Returns a log."""
    log = []
    if not gh.label_exists():
        if not gh.dry_run:
            raise Refused(f"There is no `{INBOX}` label in {gh.repo}. Was it renamed?")
        log.append(f"there is no `{INBOX}` label yet, so a real run would stop here")
    if number is None:
        pulls = gh.pulls()
    else:
        found = gh.pull(number)
        if found is None:
            raise Refused(f"There is no pull request #{number} in {gh.repo}.")
        pulls = [found]
    for i, pr in enumerate(pulls):
        try:
            action, why = decide(gh, pr, event)
            if action == "add" and number is None:
                # The sweep read this pull request a while ago. A review, a close or a new label
                # since then would otherwise be missed, and a review older than the label never
                # counts again.
                pr = pulls[i] = gh.pull(pr["number"]) or pr
                action, why = decide(gh, pr, event)
            if action:
                gh.label(pr["number"], action == "add")
                pr["labels"] = (pr["labels"] | {INBOX}) if action == "add" else (pr["labels"] - {INBOX})
                log.append(f"#{pr['number']}: {'put in' if action == 'add' else 'taken out of'} "
                           f"the inbox, because {why}")
            elif number is not None:
                log.append(f"#{pr['number']}: left as it was, because {why}")
        except RuntimeError as error:
            # One pull request that cannot be read or labelled should not hold up the rest.
            gh.failed = True
            log.append(f"#{pr['number']}: skipped, because {error}")
    if number is None:
        waiting = sum(INBOX in pr["labels"] and pr["open"] for pr in pulls)
        log.append(f"{waiting} of {len(pulls)} open pull requests are in the inbox")
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", type=int, help="look at this pull request only")
    parser.add_argument("--event", help="the pull_request_target action that started the run")
    parser.add_argument("--dry-run", action="store_true", help="read everything, change nothing")
    parser.add_argument("--summary", type=Path, help="append what was done to this file")
    args = parser.parse_args()

    gh = GitHub(args.repo, args.dry_run)
    failure = None
    try:
        log = sync(gh, args.pr, args.event)
        failure = 1 if gh.failed else None
    except (Refused, RuntimeError) as error:
        log, failure = [str(error)], 1
    left = f"; {gh.remaining} REST requests left this hour" if gh.remaining is not None else ""
    log.append(f"{gh.calls} requests to GitHub{left}")
    text = "".join(f"- {line}\n" for line in log)
    sys.stdout.write(text)
    if args.summary:
        with args.summary.open("a") as handle:
            handle.write(text)
    sys.exit(failure)


if __name__ == "__main__":
    main()
