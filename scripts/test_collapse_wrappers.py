import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("collapse_wrappers.py")


class TransitiveCaller(unittest.TestCase):
    def test_transitive_use_survives_regeneration(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            src.mkdir()
            sources = {
                "Core": "module\n@[expose] public section\ntheorem original : True := by trivial\n",
                "Alias": "module\npublic import Core\n@[expose] public section\ntheorem N.aliasProof : True := original\n",
                "Bridge": "module\npublic import Alias\n@[expose] public section\ndef marker : Nat := 1\n",
                "Consumer": "module\nimport Bridge\nexample : True := N.aliasProof\n",
                "DirectOnly": "module\npublic import Core\n@[expose] public section\ntheorem localProof : True := original\n",
                "DirectUser": "module\nimport DirectOnly\nexample : True := localProof\n",
                "Unrelated": "module\n-- unrelated mention of localProof\n",
            }
            for name, source in sources.items():
                (src / f"{name}.lean").write_text(source, encoding="utf-8")
            subprocess.run(["git", "init", "-q", directory], check=True)
            subprocess.run(["git", "-C", directory, "add", "src"], check=True)
            subprocess.run([sys.executable, str(SCRIPT), directory], check=True)
            self.assertTrue((src / "Alias.lean").exists())
            self.assertFalse((src / "DirectOnly.lean").exists())
            self.assertIn("_root_.original", (src / "DirectUser.lean").read_text())
            if os.environ.get("LEAN"):
                for name in ["Core", "Alias", "Bridge", "Consumer", "DirectUser", "Unrelated"]:
                    subprocess.run(
                        [os.environ["LEAN"], "-o", f"{name}.olean", f"{name}.lean"],
                        cwd=src, env={**os.environ, "LEAN_PATH": str(src)}, check=True,
                    )


if __name__ == "__main__":
    unittest.main()
