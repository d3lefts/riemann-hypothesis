import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("collapse_wrappers.py")


class WrapperCollapse(unittest.TestCase):
    def test_regeneration_preserves_references(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "src"
            src.mkdir()
            sources = {
                "Core": "module\n@[expose] public section\ntheorem original : True := by trivial\ntheorem eqOriginal : (0 : Nat) = 0 := rfl\n",
                "Alias": "module\npublic import Core\n@[expose] public section\ntheorem N.aliasProof : True := original\n",
                "Bridge": "module\npublic import Alias\n@[expose] public section\ndef marker : Nat := 1\n",
                "Consumer": "module\nimport Bridge\nexample : True := N.aliasProof\n",
                "DirectOnly": "module\npublic import Core\n@[expose] public section\ntheorem localProof : True := original\n",
                "DirectUser": "module\nimport DirectOnly\nexample : True := localProof\n",
                "Bracketed": "module\npublic import Core\n@[expose] public section\ntheorem Pair.component : True := original\n",
                "BracketUser": "module\nimport Bracketed\nexample : True ∧ True := ⟨Pair.component, Pair.component⟩\n",
                "Equality": "module\npublic import Core\n@[expose] public section\ntheorem N.equalProof : (0 : Nat) = 0 := eqOriginal\n",
                "Projection": "module\nimport Equality\nexample : (0 : Nat) = 0 := N.equalProof.symm\n",
                "Unrelated": "module\n-- unrelated mention of localProof\n",
            }
            for name, source in sources.items():
                (src / f"{name}.lean").write_text(source, encoding="utf-8")
            subprocess.run(["git", "init", "-q", directory], check=True)
            subprocess.run(["git", "-C", directory, "add", "src"], check=True)
            subprocess.run([sys.executable, str(SCRIPT), directory], check=True)
            self.assertTrue((src / "Alias.lean").exists())
            self.assertFalse((src / "DirectOnly.lean").exists())
            self.assertTrue((src / "Bracketed.lean").exists())
            self.assertTrue((src / "Equality.lean").exists())
            self.assertIn("_root_.original", (src / "DirectUser.lean").read_text())
            if os.environ.get("LEAN"):
                # The fixture lists dependencies before their callers.
                for name in sources:
                    if not (src / f"{name}.lean").exists():
                        continue
                    subprocess.run(
                        [os.environ["LEAN"], "-o", f"{name}.olean", f"{name}.lean"],
                        cwd=src, env={**os.environ, "LEAN_PATH": str(src)}, check=True,
                    )


if __name__ == "__main__":
    unittest.main()
