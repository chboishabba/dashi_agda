module DASHI.Geometry.QuinticThreefoldCandidate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.CalabiYau369CompactFibreBridge as Dimension

------------------------------------------------------------------------
-- Selected first computational target. This is the Fermat-style quintic
-- candidate in projective four-space. The record selects the model and its
-- required receipts; it does not manufacture smoothness, compactness, Hodge
-- data, a Ricci-flat metric, or physical compactification authority.
------------------------------------------------------------------------

record CompactCalabiYauCandidate : Set where
  constructor compactCalabiYauCandidate
  field
    modelLabel ambientSpace definingEquation : String
    ambientComplexDimension hypersurfaceComplexDimension : Nat
    dimensionReading : Dimension.Dimension369
    projectiveCompactnessExpected : Bool
    smoothnessAuthoritySupplied : Bool
    compactnessAuthoritySupplied : Bool
    calabiYauAuthoritySupplied : Bool
    candidateReceipt : String

open CompactCalabiYauCandidate public

quinticThreefoldCandidate : CompactCalabiYauCandidate
quinticThreefoldCandidate =
  compactCalabiYauCandidate
    "Fermat quintic threefold"
    "complex projective four-space CP^4"
    "z0^5 + z1^5 + z2^5 + z3^5 + z4^5 = 0"
    4
    3
    Dimension.canonicalDimension369
    true
    false
    false
    false
    "selected as the first explicit compact Calabi-Yau producer target"

quinticComplexDimensionIsThree :
  hypersurfaceComplexDimension quinticThreefoldCandidate ≡ 3
quinticComplexDimensionIsThree = refl

record QuinticPromotionBoundary : Set where
  constructor quinticPromotionBoundary
  field
    equationAloneProvesSmoothCompactCalabiYau : Bool
    equationAloneProvesSmoothCompactCalabiYauIsFalse :
      equationAloneProvesSmoothCompactCalabiYau ≡ false
    candidateSelectionProvesRicciFlatMetric : Bool
    candidateSelectionProvesRicciFlatMetricIsFalse :
      candidateSelectionProvesRicciFlatMetric ≡ false
    candidateSelectionProvesParticlePhysics : Bool
    candidateSelectionProvesParticlePhysicsIsFalse :
      candidateSelectionProvesParticlePhysics ≡ false

canonicalQuinticPromotionBoundary : QuinticPromotionBoundary
canonicalQuinticPromotionBoundary =
  quinticPromotionBoundary false refl false refl false refl
