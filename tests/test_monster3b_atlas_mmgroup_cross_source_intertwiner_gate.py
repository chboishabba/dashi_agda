#!/usr/bin/env python3
"""Exact GF3 regression for original-source ATLAS / Monster manifest gate.

Synthetic Monster coordinates are NEGATIVE/INTERFACE fixtures only:
they never authenticate MonsterSubgroups words or a quotient isomorphism.
"""
import json
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_atlas_mmgroup_cross_source_intertwiner_gate as G

ROOT=Path(__file__).resolve().parents[1]

class OriginalAtlasGate(unittest.TestCase):
 def test_original_same_source_pair(self):
  out=G.check_pair(G.atlas(ROOT),G.atlas(ROOT))
  self.assertEqual(out["intertwiner_dimension"],1)
  self.assertEqual(out["T_rank"],12)
  self.assertEqual(out["T_rows_F3"],G.eye())
  self.assertFalse(out["original_generator_word_correspondence_authenticated"])
  self.assertFalse(out["actual_Monster_Hom_promoted"])
 def test_swapped_generator_failure(self):
  c,d=G.atlas(ROOT)
  self.assertEqual(G.check_pair((c,d),(d,c))["status"],"REJECTED_TARGET_RELATIONS")
  self.assertEqual(len(G.kernel([(c,d),(d,c)])),0)
 def test_trivial_target_failure(self):
  c,d=G.atlas(ROOT)
  self.assertEqual(G.check_pair((c,d),(G.eye(),G.eye()))["status"],"REJECTED_TARGET_RELATIONS")
  self.assertEqual(len(G.kernel([(c,G.eye()),(d,G.eye())])),0)
 def test_mismatched_phase(self):
  c,d=G.atlas(ROOT)
  self.assertEqual(G.mul(c,c),G.neg(G.eye()))
  self.assertEqual(G.powm(d,3),G.eye())
  self.assertNotEqual(G.mul(c,c),G.eye())
 def test_synthetic_manifest_matrix_columns(self):
  c,d=G.atlas(ROOT)
  def make(m,name,phase):
   cols=G.transpose(m)
   return dict(name=name,central_image=phase,
       translation_images=[dict(a=col[:6],b=col[6:]) for col in cols[:6]],
       modulation_images=[dict(a=col[:6],b=col[6:]) for col in cols[6:]])
  lifts=[make(c,"g3b",-1),make(d,"h3b",1)]
  # These are C,D disguised as an input shape, NOT actual Monster elements.
  generators={x["name"]:(G.monster_matrix(x),x["central_image"]%3) for x in lifts}
  a,phase=G.candidate_word(["g3b"],generators)
  b,phaseb=G.candidate_word(["h3b"],generators)
  self.assertEqual((phase,phaseb),(2,1))
  out=G.check_pair((c,d),(a,b))
  self.assertEqual(out["status"],"ALGEBRAIC_CANDIDATE_ONLY")
  self.assertFalse(out["original_generator_word_correspondence_authenticated"])
 def test_invalid_trit_coordinate(self):
  item={"translation_images":[dict(a=[0]*6,b=[0]*6) for _ in range(6)],
        "modulation_images":[dict(a=[0]*6,b=[0]*6) for _ in range(6)]}
  item["translation_images"][0]["a"][0]=3
  with self.assertRaises(ValueError):G.monster_matrix(item)
 def test_unknown_word_rejected(self):
  with self.assertRaises(ValueError):G.candidate_word(["invented"],{"g3b":(G.eye(),1)})
 def test_missing_generator_image_rejected(self):
  with self.assertRaises(ValueError):G.monster_matrix({"translation_images":[],"modulation_images":[]})
 def test_original_seven_relator(self):
  c,d=G.atlas(ROOT)
  self.assertTrue(G.source_relations(c,d))
  r=G.atlas_relator(c,d)
  self.assertEqual(G.powm(r,7),G.eye())
  self.assertNotEqual(r,G.eye())
 def test_seven_relator_rejects_false_identity(self):
  c,d=G.atlas(ROOT)
  self.assertFalse(G.source_relations(c,G.eye()))
 def test_gf3_inverse(self):
  c,d=G.atlas(ROOT)
  for m in (c,d):
   mi=G.inverse(m)
   self.assertEqual(G.mul(m,mi),G.eye())
   self.assertEqual(G.mul(mi,m),G.eye())
 def test_no_provenance_promotion(self):
  self.assertFalse(G.test(ROOT)["independent_Monster_generator_words_proven"])

if __name__=="__main__":unittest.main()
