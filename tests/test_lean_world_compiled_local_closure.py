"""Offline source-pinned local Lean import DAG/cache negative controls."""
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
from lean_world_compiled_local_closure import compile_order,compile_deps,closure_key,ClosureError

class LocalCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        (self.root/"Helper").mkdir()
        (self.root/"Helper/Basic.lean").write_text("def helper := 1\n")
        (self.root/"Main.lean").write_text(
            "import Helper.Basic\ntheorem okay : True := trivial\n")
        self.sources=[{"path":"Main.lean","sha256":"a"*64},
                      {"path":"Helper/Basic.lean","sha256":"b"*64}]
    def test_topological_imports(self):
        self.assertEqual(compile_order(self.root,self.sources,"Main.lean"),
                         ["Helper/Basic.lean"])
    def test_compile_once_reuse_verified_olean(self):
        def simulated(argv,root,env,timeout,memory):
            Path(argv[3]).write_bytes(b"olean fixture")
            return 0
        kwargs=dict(lean="lean",lean_version="Lean 4.33.1",
                    repo="owner/repo",revision="a"*40,
                    external_digest="b"*64,
                    cache_dir=self.root/"cache",runner=simulated)
        initial=compile_deps(self.root,self.sources,"Main.lean",**kwargs)
        reused=compile_deps(self.root,self.sources,"Main.lean",**kwargs)
        self.assertFalse(initial["cache_reused"])
        self.assertTrue(reused["cache_reused"])
        self.assertEqual(initial["compiled_modules"],1)
    def test_changed_source_rekeys(self):
        old=closure_key(sources=self.sources,repo="owner/repo",
                        revision="a"*40,lean_version="Lean 4.33.1",
                        target="Main.lean",external_digest="c"*64)
        changed=[dict(x) for x in self.sources]
        changed[1]["sha256"]="e"*64
        new=closure_key(sources=changed,repo="owner/repo",
                        revision="a"*40,lean_version="Lean 4.33.1",
                        target="Main.lean",external_digest="c"*64)
        self.assertNotEqual(old,new)
    def test_cyclic_local_dependencies_fail_closed(self):
        (self.root/"Helper/Basic.lean").write_text("import Main\n")
        with self.assertRaisesRegex(ClosureError,"cyclic"):
            compile_order(self.root,self.sources,"Main.lean")

if __name__=="__main__":unittest.main()
