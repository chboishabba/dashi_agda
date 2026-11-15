module DASHI.Mathematics.Complexity.Karp21PNFSignedTriangleSameObjectExact where

------------------------------------------------------------------------
-- FIRST-APPLICABLE SOURCE OWNER: the literal PNF signed triangle from
-- DASHI.Interop.PNFSignedResidualDelta0Exact (Fan Chung 1997 is the
-- earlier graph-spectral source, not owner of DASHI's PNF graph).
--
-- This is a SAME-OBJECT 3-edge finite graph projection:
--    0--1: partial (+1)
--    1--2: noTypedMeet (+3)
--    2--0: contradiction (-9)
-- Each integer weight is derived from the canonical PNF cell receipt
-- and the source module's magnitude/sign lemmas; it is not an invented
-- spectral analogue. The edge list is undirected for Karp's evaluator,
-- while the *PNF* cell still retains its directed typed provenance.
--
-- 4*Cut_PNF(b) = spin(b)^T Delta0_PNF spin(b).
-- This equality holds only on this explicit finite graph and binary
-- spin selection. It does NOT convert PNF semantic truth or higher
-- Hodge authority into a Karp NP-completeness certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Interop.PNFSignedResidualDelta0Exact as PNF
import DASHI.Interop.PNFHodgeResidualTopology as Hodge
import DASHI.Interop.PNFSpectralFieldGraph as PNFGraph
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap

pnfWeight01 : ℤ
pnfWeight01 = + (PNFGraph.magnitude
  (Hodge.graphWeight Hodge.canonicalResidualOneCell))

pnfWeight12 : ℤ
pnfWeight12 = + (PNFGraph.magnitude
  (Hodge.graphWeight Hodge.canonicalTransportOneCell))

pnfWeight20 : ℤ
pnfWeight20 = - (+ (PNFGraph.magnitude
  (Hodge.graphWeight Hodge.canonicalContradictionOneCell)))

pnfWeight01IsOne : pnfWeight01 ≡ + 1
pnfWeight01IsOne = cong (+_) PNF.edge01MagnitudeIsOne

pnfWeight12IsThree : pnfWeight12 ≡ + 3
pnfWeight12IsThree = cong (+_) PNF.edge12MagnitudeIsThree

pnfWeight20IsNegativeNine : pnfWeight20 ≡ - (+ 9)
pnfWeight20IsNegativeNine =
  cong (λ magnitude → - (+ magnitude))
    PNF.edge20MagnitudeIsNine

pnfFiniteEdges : List (Cut.SignedUndirectedEdge 3)
pnfFiniteEdges =
  Cut.edge Fin.zero (Fin.suc Fin.zero) (λ ()) pnfWeight01 ∷
  Cut.edge (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero))
    (λ ()) pnfWeight12 ∷
  Cut.edge (Fin.suc (Fin.suc Fin.zero)) Fin.zero
    (λ ()) pnfWeight20 ∷
  []

pnfLabels : Bool → Bool → Bool → Vec.Vec Bool 3
pnfLabels a b c = a Vec.∷ b Vec.∷ c Vec.∷ Vec.[]

pnfSpinField : Bool → Bool → Bool → PNF.TriangleField
pnfSpinField a b c =
  PNF.triangleField (Lap.spin a) (Lap.spin b) (Lap.spin c)

pnfCutQuadraticEqualsOriginalEnergy :
  (a b c : Bool) →
  Lap.signedLaplacianQuadratic
    pnfFiniteEdges (pnfLabels a b c) ≡
  PNF.signedEdgeEnergy (pnfSpinField a b c)
pnfCutQuadraticEqualsOriginalEnergy true true true
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy true true false
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy true false true
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy true false false
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy false true true
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy false true false
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy false false true
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl
pnfCutQuadraticEqualsOriginalEnergy false false false
  rewrite pnfWeight01IsOne | pnfWeight12IsThree
        | pnfWeight20IsNegativeNine = refl

pnfLiteralSignedDelta0CutIdentity :
  (a b c : Bool) →
  (+ 4) * Cut.edgeListCutValue
    pnfFiniteEdges (pnfLabels a b c)
  ≡
  PNF.dot (pnfSpinField a b c)
    (PNF.signedResidualDelta0 (pnfSpinField a b c))
pnfLiteralSignedDelta0CutIdentity a b c =
  trans
    (Lap.karpCutEqualsSignedLaplacianQuadratic
      pnfFiniteEdges (pnfLabels a b c))
    (trans
      (pnfCutQuadraticEqualsOriginalEnergy a b c)
      (sym (PNF.signedIncidenceEnergyIdentity
        (pnfSpinField a b c))))
