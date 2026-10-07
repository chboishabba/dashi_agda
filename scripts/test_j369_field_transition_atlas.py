#!/usr/bin/env python3
import importlib.util, tempfile, unittest
from pathlib import Path

SCRIPT=Path(__file__).with_name('j369_field_transition_atlas.py')
spec=importlib.util.spec_from_file_location('atlas',SCRIPT)
atlas=importlib.util.module_from_spec(spec);spec.loader.exec_module(atlas)

class AtlasTest(unittest.TestCase):
    def test_prime_power_and_bracket_196830(self):
        self.assertEqual(atlas.prime_power(196831),(196831,1))
        self.assertEqual(atlas.bracket_prime_powers(196830),(196817,196831))

    def test_ticket_numeric_candidates(self):
        self.assertEqual(atlas.frobenius_orbit_count(2,2),3)
        self.assertEqual(atlas.frobenius_orbit_count(3,2),6)
        self.assertEqual(atlas.frobenius_orbit_count(2,4),6)
        self.assertEqual(atlas.frobenius_orbit_count(4,2),10)
        self.assertEqual(atlas.frobenius_orbit_count(5,2),15)
        self.assertEqual(atlas.frobenius_orbit_count(3,4),24)
        self.assertEqual(atlas.frobenius_orbit_count(4,3),24)
        self.assertEqual(atlas.prime_power(81),(3,4))
        self.assertEqual(atlas.prime_power(243),(3,5))
        self.assertEqual(atlas.prime_power(729),(3,6))
        self.assertEqual(atlas.prime_power(811),(811,1))

    def test_mass18_slice_is_1330_nodes_and_edges(self):
        ss=atlas.legacy_states_exact_mass(18); self.assertEqual(len(ss),1330)
        S=set(ss); edges=[(s,atlas.legacy_first_enabled_step(s)) for s in ss]
        self.assertEqual(len(edges),1330); self.assertTrue(all(t in S for _,t in edges))

    def test_transition_semantics_match_agda_priority(self):
        self.assertEqual(atlas.legacy_first_enabled_step((1,1,0,0)),(0,1,1,0))
        self.assertEqual(atlas.legacy_first_enabled_step((0,1,1,0)),(0,1,0,1))
        self.assertEqual(atlas.legacy_first_enabled_step((0,1,0,1)),(1,1,0,0))
        self.assertEqual(atlas.legacy_first_enabled_step((0,1,0,0)),(1,0,0,0))

    def test_generated_table_covers_authoritative_carriers(self):
        rows=atlas.field_bracket_rows(atlas.CARRIERS)
        self.assertEqual([r['n'] for r in rows],list(atlas.CARRIERS))
        r=next(x for x in rows if x['n']==80)
        self.assertEqual((r['below'],r['above'],r['multiplicative_upper']),(79,81,81))
        r=next(x for x in rows if x['n']==196830)
        self.assertEqual((r['below'],r['above'],r['multiplicative_upper']),(196817,196831,196831))

    def test_full_generation_firewall_and_plots(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td); m=atlas.generate(out,18,37)
            self.assertEqual((m['legacy_nodes'],m['legacy_edges'],m['grid_rows']),(1330,1330,36))
            self.assertEqual(m['grid_displacement_vector_count'],233)
            self.assertFalse(m['recognition_claimed']); self.assertFalse(m['t5_subfield_object_shape_inferred'])
            for name in ('fieldBracketTable.csv','fieldCandidates.csv','atlasManifest.json','fieldRelationGraph.svg','legacyMass18TransitionGraph.svg','legacyMass18EdgeDensity.svg','legacyMass18Transitions.csv','OggSSPFiniteFieldBracketGenerated.agda'):
                self.assertTrue((out/name).exists(),name)

if __name__=='__main__':unittest.main()
