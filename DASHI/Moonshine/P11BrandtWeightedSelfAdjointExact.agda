module DASHI.Moonshine.P11BrandtWeightedSelfAdjointExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Giulio Codogni and Guido Maria Lido,
-- "Spectral theory of isogeny graphs", Journal of Number Theory 286 (2026),
-- 131--184.
-- DOI: 10.1016/j.jnt.2026.02.006.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the earlier four coordinate-basis checks to full weighted
-- self-adjointness for arbitrary integer vectors on the p=11, ell=2 Brandt
-- module.  The weights are not fitted here: they are the automorphism-derived
-- cleared reciprocal masses constructed in P11BrandtAutomorphismWeightExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact as Weight

module Ring = NR IntRS.ring
open Ring using (Κ; _⊕_; _⊗_; _⊜_; solve)

weightedSelfAdjointPolynomial :
  (x y z w : ℤ) →
  ((+ 2) *ℤ (((+ 3) *ℤ y) *ℤ z))
    +ℤ ((+ 3) *ℤ ((((+ 2) *ℤ x) +ℤ y) *ℤ w))
  ≡
  ((+ 2) *ℤ (x *ℤ ((+ 3) *ℤ w)))
    +ℤ ((+ 3) *ℤ (y *ℤ (((+ 2) *ℤ z) +ℤ w)))
weightedSelfAdjointPolynomial x y z w =
  Ring.solve 4
    (λ x y z w →
      ( ((Κ (+ 2)) ⊗ (((Κ (+ 3)) ⊗ y) ⊗ z))
          ⊕ ((Κ (+ 3)) ⊗ ((((Κ (+ 2)) ⊗ x) ⊕ y) ⊗ w))
      , ((Κ (+ 2)) ⊗ (x ⊗ ((Κ (+ 3)) ⊗ w)))
          ⊕ ((Κ (+ 3)) ⊗ (y ⊗ (((Κ (+ 2)) ⊗ z) ⊕ w))) ))
    refl x y z w

weightedSelfAdjoint :
  (u v : P11.IntPair) →
  Spectral.weightedPairing (P11.matrixAction u) v
  ≡ Spectral.weightedPairing u (P11.matrixAction v)
weightedSelfAdjoint (P11.intPair x y) (P11.intPair z w) =
  weightedSelfAdjointPolynomial x y z w

leftWeightIsGeometric :
  Spectral.weightJ0 ≡ + (Weight.clearedReciprocalWeight Geo.jZeroSS)
leftWeightIsGeometric = refl

rightWeightIsGeometric :
  Spectral.weightJ1 ≡ + (Weight.clearedReciprocalWeight Geo.j1728SS)
rightWeightIsGeometric = refl

record P11WeightedSelfAdjointBoundary : Set where
  field
    arbitraryVectorWeightedSelfAdjointnessProved : Bool
    arbitraryVectorWeightedSelfAdjointnessProvedIsTrue :
      arbitraryVectorWeightedSelfAdjointnessProved ≡ true

    automorphismDerivedWeightsConsumed : Bool
    automorphismDerivedWeightsConsumedIsTrue :
      automorphismDerivedWeightsConsumed ≡ true

    arbitraryCharacteristicGeneralizationConstructedHere : Bool
    arbitraryCharacteristicGeneralizationConstructedHereIsFalse :
      arbitraryCharacteristicGeneralizationConstructedHere ≡ false

canonicalP11WeightedSelfAdjointBoundary : P11WeightedSelfAdjointBoundary
canonicalP11WeightedSelfAdjointBoundary =
  record
    { arbitraryVectorWeightedSelfAdjointnessProved = true
    ; arbitraryVectorWeightedSelfAdjointnessProvedIsTrue = refl
    ; automorphismDerivedWeightsConsumed = true
    ; automorphismDerivedWeightsConsumedIsTrue = refl
    ; arbitraryCharacteristicGeneralizationConstructedHere = false
    ; arbitraryCharacteristicGeneralizationConstructedHereIsFalse = refl
    }
