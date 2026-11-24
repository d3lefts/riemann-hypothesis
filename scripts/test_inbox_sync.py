#!/usr/bin/env python3
"""Inbox label checks against an in-memory stand-in for GitHub; no network calls."""
import contextlib
import datetime
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import unittest

SCRIPT = Path(__file__).with_name("inbox-sync.py")
spec = importlib.util.spec_from_file_location("inbox_sync", SCRIPT)
inbox = importlib.util.module_from_spec(spec)
spec.loader.exec_module(inbox)

INBOX = inbox.INBOX
T0 = datetime.datetime(2026, 11, 23, 3, 0, 0, tzinfo=datetime.timezone.utc)


def at(minutes):
    """A GraphQL time stamp, `minutes` after T0."""
    return (T0 + datetime.timedelta(minutes=minutes)).strftime("%Y-%m-%dT%H:%M:%SZ")


def user(login):
    return {"__typename": "User", "login": login}


BOT = {"__typename": "Bot", "login": "github-actions"}


def node(number, *, author="alice", draft=False, ref=None, labels=(), reviews=(), events=(),
         state="OPEN"):
    """A pull request as GraphQL describes it.

    `reviews` holds (login, minutes) and `events` holds (kind, label, minutes, actor), where kind
    is "on" or "off" and actor is a login or BOT.
    """
    return {
        "number": number, "state": state, "isDraft": draft, "headRefName": ref or f"topic-{number}",
        "author": {"login": author},
        "labels": {"nodes": [{"name": name} for name in labels]},
        "reviews": {"nodes": [
            {"state": "COMMENTED", "submittedAt": at(minutes), "author": user(login)}
            for login, minutes in reviews]},
        "timelineItems": {"nodes": [
            {"__typename": "LabeledEvent" if kind == "on" else "UnlabeledEvent",
             "createdAt": at(minutes), "label": {"name": name},
             "actor": actor if isinstance(actor, dict) else user(actor)}
            for kind, name, minutes, actor in events]},
    }


class Fake(inbox.GitHub):
    """Just enough of GitHub's REST and GraphQL APIs."""

    def __init__(self, nodes=(), roles=None, label=True, dry_run=False):
        super().__init__("o/r", dry_run)
        self.nodes = {n["number"]: n for n in nodes}
        self.roles = roles or {}
        self.has_label, self.writes, self.lookups = label, [], []
        # What a later read of one pull request finds, when it changed after the sweep's read.
        self.later = {}
        self.broken = set()

    def call(self, method, path, payload=None):
        self.calls += 1
        if method == "GET" and path == f"labels/{INBOX}":
            return (200, {"name": INBOX}) if self.has_label else (404, None)
        if method == "GET" and path.startswith("collaborators/"):
            login = path.split("/")[1]
            self.lookups.append(login)
            if login in self.broken:
                return 502, None
            if login not in self.roles:
                return 404, None
            role = self.roles[login]
            permission = {"maintain": "write", "triage": "read"}.get(role, role)
            return 200, {"permission": permission, "role_name": role}
        if method == "POST":
            number = int(path.split("/")[1])
            self.writes.append(("add", number))
            return 200, []
        if method == "DELETE":
            number = int(path.split("/")[1])
            self.writes.append(("remove", number))
            return 200, []
        raise AssertionError(f"unexpected {method} {path}")

    def graphql(self, query, **variables):
        self.calls += 1
        if "number" in variables:
            number = variables["number"]
            return {"repository": {"pullRequest": self.later.get(number, self.nodes.get(number))}}
        # Two to a page, so that the pages are followed.
        open_ = [n for n in self.nodes.values() if n["state"] == "OPEN"]
        start = int(variables["after"] or 0)
        page = open_[start:start + 2]
        more = start + 2 < len(open_)
        return {"repository": {"pullRequests": {
            "nodes": page, "pageInfo": {"hasNextPage": more, "endCursor": str(start + 2)}}}}


def sweep(gh):
    return inbox.sync(gh)


class Normalising(unittest.TestCase):
    def test_reads_the_latest_label_changes_and_skips_bots_and_pending_reviews(self):
        found = node(1, labels=[INBOX, "small"], events=[
            ("on", INBOX, 1, BOT), ("off", INBOX, 2, "maint"), ("on", INBOX, 3, "maint"),
            ("on", "small", 4, BOT), ("off", INBOX, 5, BOT)])
        found["reviews"]["nodes"] += [
            {"state": "PENDING", "submittedAt": None, "author": user("maint")},
            {"state": "COMMENTED", "submittedAt": at(6),
             "author": {"__typename": "Bot", "login": "copilot"}},
            {"state": "APPROVED", "submittedAt": at(7), "author": None}]
        pr = inbox.pull(found)
        self.assertEqual(pr["added"], T0 + datetime.timedelta(minutes=3))
        # The latest removal was the workflow's own, so no person took it out.
        self.assertIsNone(pr["removed_by"])
        self.assertEqual(pr["reviews"], [])
        self.assertEqual(pr["labels"], {INBOX, "small"})


class Sweep(unittest.TestCase):
    def test_new_pull_request_goes_in(self):
        gh = Fake([node(1)])
        log = sweep(gh)
        self.assertEqual(gh.writes, [("add", 1)])
        self.assertIn("1 of 1 open pull requests are in the inbox", log)

    def test_drafts_batches_and_decided_pull_requests_stay_out(self):
        gh = Fake([node(1, draft=True), node(2, ref="batch/citations"),
                   node(3, labels=["batch queue"]), node(4, labels=["building"]),
                   node(5, labels=["awaiting-author"]), node(6, state="CLOSED")])
        sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_drafts_batches_and_decided_pull_requests_come_out(self):
        gh = Fake([node(1, draft=True, labels=[INBOX]), node(2, ref="batch/x", labels=[INBOX]),
                   node(3, labels=[INBOX, "batch queue"])])
        sweep(gh)
        self.assertEqual(gh.writes, [("remove", 1), ("remove", 2), ("remove", 3)])

    def test_first_review_after_the_label_takes_it_out(self):
        gh = Fake([node(1, labels=[INBOX], events=[("on", INBOX, 1, BOT)],
                        reviews=[("maint", 2)])], roles={"maint": "triage"})
        sweep(gh)
        self.assertEqual(gh.writes, [("remove", 1)])

    def test_review_before_the_label_went_back_on_does_not(self):
        # A maintainer reviewed, then put the label back by hand to ask for another look.
        gh = Fake([node(1, labels=[INBOX], events=[("on", INBOX, 1, BOT), ("off", INBOX, 3, BOT),
                                                   ("on", INBOX, 4, "maint")],
                        reviews=[("maint", 2)])], roles={"maint": "write"})
        sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_reviews_by_the_author_or_without_triage_access_do_not_count(self):
        gh = Fake([node(1, author="alice", labels=[INBOX], events=[("on", INBOX, 1, BOT)],
                        reviews=[("alice", 2), ("reader", 3), ("stranger", 4)])],
                  roles={"alice": "write", "reader": "read"})
        sweep(gh)
        self.assertEqual(gh.writes, [])
        # Alice wrote the pull request, so her access is never looked up.
        self.assertEqual(gh.lookups, ["reader", "stranger"])

    def test_every_role_from_triage_up_counts(self):
        roles = ["triage", "write", "maintain", "admin"]
        gh = Fake([node(i, labels=[INBOX], events=[("on", INBOX, 1, BOT)],
                        reviews=[(role, 2)]) for i, role in enumerate(roles, 1)],
                  roles={role: role for role in roles})
        sweep(gh)
        self.assertEqual(gh.writes, [("remove", i) for i in range(1, 5)])

    def test_access_is_looked_up_once_a_run(self):
        gh = Fake([node(i, labels=[INBOX], events=[("on", INBOX, 1, BOT)],
                        reviews=[("maint", 2)]) for i in range(1, 4)],
                  roles={"maint": "triage"})
        sweep(gh)
        self.assertEqual(gh.lookups, ["maint"])

    def test_reviewed_pull_request_without_the_label_is_not_put_back(self):
        gh = Fake([node(1, events=[("on", INBOX, 1, BOT), ("off", INBOX, 3, BOT)],
                        reviews=[("maint", 2)])], roles={"maint": "triage"})
        sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_label_a_person_took_off_stays_off(self):
        gh = Fake([node(1, events=[("on", INBOX, 1, BOT), ("off", INBOX, 2, "maint")])])
        sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_label_the_workflow_took_off_goes_back_once_the_reason_is_gone(self):
        # Taken out as a draft, then marked ready while the workflow was not running.
        gh = Fake([node(1, events=[("on", INBOX, 1, BOT), ("off", INBOX, 2, BOT)])])
        sweep(gh)
        self.assertEqual(gh.writes, [("add", 1)])

    def test_review_that_lands_during_the_sweep_keeps_it_out(self):
        gh = Fake([node(1)], roles={"maint": "triage"})
        gh.later[1] = node(1, reviews=[("maint", 1)])
        sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_close_during_the_sweep_keeps_it_out(self):
        gh = Fake([node(1)])
        gh.later[1] = node(1, state="MERGED")
        log = sweep(gh)
        self.assertEqual(gh.writes, [])
        self.assertIn("0 of 1 open pull requests are in the inbox", log)

    def test_one_failed_lookup_does_not_stop_the_sweep(self):
        gh = Fake([node(1, labels=[INBOX], events=[("on", INBOX, 1, BOT)], reviews=[("flaky", 2)]),
                   node(2)])
        gh.broken.add("flaky")
        log = sweep(gh)
        self.assertEqual(gh.writes, [("add", 2)])
        self.assertTrue(gh.failed)
        self.assertTrue(any(line.startswith("#1: skipped") for line in log))

    def test_every_page_is_read(self):
        gh = Fake([node(i) for i in range(1, 6)])
        log = sweep(gh)
        self.assertEqual(gh.writes, [("add", i) for i in range(1, 6)])
        self.assertIn("5 of 5 open pull requests are in the inbox", log)


class Events(unittest.TestCase):
    def test_marking_ready_puts_a_reviewed_pull_request_back(self):
        gh = Fake([node(1, events=[("on", INBOX, 1, BOT), ("off", INBOX, 3, "maint")],
                        reviews=[("maint", 2)])], roles={"maint": "triage"})
        log = inbox.sync(gh, 1, "ready_for_review")
        self.assertEqual(gh.writes, [("add", 1)])
        self.assertEqual(log, ["#1: put in the inbox, because it was marked ready"])

    def test_opening_a_draft_does_nothing(self):
        gh = Fake([node(1, draft=True)])
        log = inbox.sync(gh, 1, "opened")
        self.assertEqual(gh.writes, [])
        self.assertEqual(log, ["#1: left as it was, because it is a draft"])

    def test_turning_into_a_draft_takes_it_out(self):
        gh = Fake([node(1, draft=True, labels=[INBOX])])
        inbox.sync(gh, 1, "converted_to_draft")
        self.assertEqual(gh.writes, [("remove", 1)])

    def test_reopening_a_queued_pull_request_leaves_it_out(self):
        gh = Fake([node(1, labels=["batch queue"])])
        inbox.sync(gh, 1, "reopened")
        self.assertEqual(gh.writes, [])

    def test_closing_takes_it_out(self):
        gh = Fake([node(1, state="MERGED", labels=[INBOX]), node(2, state="CLOSED")])
        inbox.sync(gh, 1, "closed")
        inbox.sync(gh, 2, "closed")
        self.assertEqual(gh.writes, [("remove", 1)])

    def test_an_event_for_a_pull_request_already_in_the_inbox_changes_nothing(self):
        gh = Fake([node(1, labels=[INBOX])])
        inbox.sync(gh, 1, "opened")
        self.assertEqual(gh.writes, [])


class Failures(unittest.TestCase):
    def test_missing_label_stops_a_real_run(self):
        gh = Fake([node(1)], label=False)
        with self.assertRaises(inbox.Refused):
            sweep(gh)
        self.assertEqual(gh.writes, [])

    def test_missing_label_is_reported_by_a_dry_run(self):
        gh = Fake([node(1)], label=False, dry_run=True)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            log = sweep(gh)
        self.assertEqual(gh.writes, [])
        self.assertEqual(out.getvalue(), f"would add {INBOX} on #1\n")
        self.assertTrue(log[0].startswith("there is no `inbox` label yet"))

    def test_unknown_pull_request_is_refused(self):
        with self.assertRaises(inbox.Refused):
            inbox.sync(Fake([]), 7, "opened")


class Gh(unittest.TestCase):
    """The real GitHub class, with `gh` itself stood in for."""

    def answering(self, stdout, code=0):
        gh = inbox.GitHub("o/r")
        gh.run = lambda args, payload=None: subprocess.CompletedProcess(args, code, stdout, b"oops")
        return gh

    def test_rest_status_body_and_allowance_are_read(self):
        gh = self.answering(b"HTTP/2.0 200 OK\r\nX-Ratelimit-Remaining: 812\r\n\r\n{\"name\": \"inbox\"}")
        self.assertEqual(gh.call("GET", "labels/inbox"), (200, {"name": "inbox"}))
        self.assertEqual(gh.remaining, 812)

    def test_rest_error_status_is_returned(self):
        gh = self.answering(b"HTTP/2.0 404 Not Found\r\n\r\n{\"message\": \"Not Found\"}", code=1)
        self.assertFalse(gh.label_exists())

    def test_rest_without_an_answer_raises(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(RuntimeError):
            self.answering(b"", code=1).call("GET", "labels/inbox")

    def test_graphql_errors_raise_even_with_data(self):
        body = json.dumps({"data": {"repository": None}, "errors": [{"message": "bad"}]}).encode()
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(RuntimeError) as caught:
            self.answering(body, code=1).pull(1)
        self.assertIn("bad", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
