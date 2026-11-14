"""Independent negative and randomized tests for first-link proof-carrying censuses."""
from __future__ import annotations
import copy
import random
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import ibrahim_fln_certificates as cert
import ibrahim_fln_reference_analysis as ref


class FirstLinkCertificateTests(unittest.TestCase):
    def test_paper_figure_verified_trace_and_basin(self):
        graph={'A':'B','B':'C','C':'A','D':'C','E':'C','F':'E','G':'E'}
        result=cert.check_graph_certificate(graph,cert.certify_graph(graph))
        self.assertEqual(len(result['outcomes']),7)
        self.assertEqual(result['basin_sizes'],{('cycle',('A','B','C')):7})
        self.assertEqual(result['partition_size'],7)

    def test_missing_target_dead_end_and_cycle_are_distinct(self):
        graph={'a':'unknown','b':None,'c':'c'}
        out=cert.check_graph_certificate(graph,cert.certify_graph(graph))['outcomes']
        self.assertEqual(out['a'],('unresolved_target',('unknown',)))
        self.assertEqual(out['b'],('dead_end',('b',)))
        self.assertEqual(out['c'],('cycle',('c',)))

    def test_forged_terminal_transition_digest_and_missing_start_rejected(self):
        graph={'a':'b','b':'a','c':None}
        base=cert.certify_graph(graph)
        manipulations=[]
        t=copy.deepcopy(base);t['traces'][0]['kind']='dead_end';t['traces'][0]['terminal']='b';t['traces'][0].pop('entry_index');t['traces'][0].pop('cycle');manipulations.append(t)
        t=copy.deepcopy(base);t['traces'][0]['trace']=['a','c'];manipulations.append(t)
        t=copy.deepcopy(base);t['traces'][0]['cycle']=['b','a'];manipulations.append(t)
        t=copy.deepcopy(base);t['traces'].pop();manipulations.append(t)
        t=copy.deepcopy(base);t['graph_sha256']='0'*64;manipulations.append(t)
        for bad in manipulations:
            with self.subTest(bad=bad),self.assertRaises((ValueError,TypeError)):
                cert.check_graph_certificate(graph,bad)

    def test_revision_cone_certificate_and_negative_controls(self):
        old={'a':'b','b':'c','c':'c','x':'x','y':'x'}
        new=dict(old,b='x')
        r=cert.certify_reverse_edit_cone(old,new)
        self.assertEqual(cert.check_reverse_edit_cone(old,new,r),{'a','b'})
        bad=copy.deepcopy(r);bad['paths_to_edit']['a']=['a','c','b']
        with self.assertRaises(ValueError):cert.check_reverse_edit_cone(old,new,bad)
        bad=copy.deepcopy(r);bad['paths_to_edit'].pop('a')
        with self.assertRaises(ValueError):cert.check_reverse_edit_cone(old,new,bad)
        with self.assertRaises(ValueError):cert.certify_reverse_edit_cone(old,{'z':'z'})

    def test_5000_random_graphs_and_revisions_independent_oracles(self):
        rng=random.Random(1505)
        for n in range(1,11):
            nodes=[f'v{i}' for i in range(n)]
            for _ in range(500):
                old={v:rng.choice(nodes+[None,'absent']) for v in nodes}
                certificate=cert.certify_graph(old)
                got=cert.check_graph_certificate(old,certificate)
                expected,_=ref.terminal_census(old)
                self.assertEqual(got['outcomes'],expected)
                new={v:rng.choice(nodes+[None,'absent']) for v in nodes}
                cone=cert.certify_reverse_edit_cone(old,new)
                reach=cert.check_reverse_edit_cone(old,new,cone)
                self.assertEqual(reach,ref.reverse_edited_closure(old,{v for v in nodes if old[v]!=new[v]}))
                self.assertTrue(ref.compare_same_carrier(old,new)['outside_bound_unaffected'])

if __name__=='__main__':unittest.main()
