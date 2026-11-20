"""Compile the actual solver and check its scalar and per-mode legacy keys."""
import ast
from pathlib import Path
import unittest

class ReceiverCompile(unittest.TestCase):
    def test_solver_compiles_and_retains_legacy_keys(self):
        path=Path(__file__).with_name("ksw668_f8_tt_multipole.py")
        source=path.read_text()
        compile(source,str(path),"exec")
        tree=ast.parse(source)
        required={"E4_legacy","E4_tangent_legacy","mode_E4_legacy","mode_E4_tangent_legacy"}
        self.assertTrue(any(required <= {k.arg for k in n.keywords}
                            for n in ast.walk(tree) if isinstance(n,ast.Call)))

if __name__ == "__main__":
    unittest.main()
