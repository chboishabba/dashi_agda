module DASHI.Physics.Closure.NSTriadKNExternalSharedModeWeightedFluxRound113Exact where

------------------------------------------------------------------------
-- ROUND113 / EXACT WEIGHTED SHARED-MODE FLUX IDENTITY
--
-- The Round112 make-or-break question is whether cross-triad quartic terms can
-- be paired across a shared mode/output fibre with OPPOSITE transfer.  If they
-- can, then critical weights enter only through a multiplier difference:
--
--   w_left T + w_right (-T) = (w_left - w_right) T.
--
-- This is the exact discrete integration-by-parts/commutator algebra needed
-- before any absolute value is taken.  The theorem below is physical-carrier
-- agnostic on purpose: Round113 isolates the one same-object hypothesis the NS
-- reindexing must prove, namely antisymmetry of the paired cross-triad transfer.
--
-- Important boundary:
-- * reality conjugation does NOT provide this hypothesis (Round112 proves the
--   corresponding Waleffe transfer is invariant under reality pairing);
-- * a shared residual carrier alone does NOT provide it;
-- * once antisymmetry is established for the actual reindexed quartic term, the
--   multiplier-difference conclusion is exact and costs no cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring

weightedPair :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
weightedPair wLeft wRight leftTransfer rightTransfer =
  C3.complexAdd
    (C3.complexMultiply wLeft leftTransfer)
    (C3.complexMultiply wRight rightTransfer)

weightDifferenceTimes :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
weightDifferenceTimes wLeft wRight transfer =
  C3.complexMultiply (C3.complexSubtract wLeft wRight) transfer

weightedAntisymmetricPairIsMultiplierDifference :
  ∀ {r} {F : C3.RealField r}
    (wLeft wRight transfer : C3.Complex F) →
  weightedPair wLeft wRight transfer (C3.complexNegate transfer)
  ≡ weightDifferenceTimes wLeft wRight transfer
weightedAntisymmetricPairIsMultiplierDifference {F = F} wLeft wRight transfer =
  R.solve 3
    (λ wl wr t →
      ((wl R.⊗ t) R.⊕ (wr R.⊗ (R.⊝ t)))
      R.⊜
      ((wl R.⊕ (R.⊝ wr)) R.⊗ t))
    refl wLeft wRight transfer
  where module R = Ring.Solver F

record SharedModeAntisymmetricFlux
    {r} (F : C3.RealField r) : Set r where
  field
    leftWeight : C3.Complex F
    rightWeight : C3.Complex F
    leftTransfer : C3.Complex F
    rightTransfer : C3.Complex F
    reverseIsNegative :
      rightTransfer ≡ C3.complexNegate leftTransfer

open SharedModeAntisymmetricFlux public

weightedFlux :
  ∀ {r} {F : C3.RealField r} →
  SharedModeAntisymmetricFlux F → C3.Complex F
weightedFlux flux =
  weightedPair
    (leftWeight flux)
    (rightWeight flux)
    (leftTransfer flux)
    (rightTransfer flux)

multiplierDifferenceFlux :
  ∀ {r} {F : C3.RealField r} →
  SharedModeAntisymmetricFlux F → C3.Complex F
multiplierDifferenceFlux flux =
  weightDifferenceTimes
    (leftWeight flux)
    (rightWeight flux)
    (leftTransfer flux)

sharedModeAntisymmetricFluxProducesExactMultiplierDifference :
  ∀ {r} {F : C3.RealField r}
    (flux : SharedModeAntisymmetricFlux F) →
  weightedFlux flux ≡ multiplierDifferenceFlux flux
sharedModeAntisymmetricFluxProducesExactMultiplierDifference flux
  rewrite reverseIsNegative flux =
  weightedAntisymmetricPairIsMultiplierDifference
    (leftWeight flux) (rightWeight flux) (leftTransfer flux)

------------------------------------------------------------------------
-- The symmetric comparison is included to make the Round112 reality result
-- impossible to misread.  If the paired transfer has the SAME sign, the
-- weighted contribution is a weight SUM, not a commutator difference.
------------------------------------------------------------------------

weightSumTimes :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
weightSumTimes wLeft wRight transfer =
  C3.complexMultiply (C3.complexAdd wLeft wRight) transfer

weightedSymmetricPairIsWeightSum :
  ∀ {r} {F : C3.RealField r}
    (wLeft wRight transfer : C3.Complex F) →
  weightedPair wLeft wRight transfer transfer
  ≡ weightSumTimes wLeft wRight transfer
weightedSymmetricPairIsWeightSum {F = F} wLeft wRight transfer =
  R.solve 3
    (λ wl wr t →
      ((wl R.⊗ t) R.⊕ (wr R.⊗ t))
      R.⊜
      ((wl R.⊕ wr) R.⊗ t))
    refl wLeft wRight transfer
  where module R = Ring.Solver F

round113AntisymmetricSharedModePairGivesMultiplierDifference : Bool
round113AntisymmetricSharedModePairGivesMultiplierDifference = true

round113RealitySymmetryAloneGivesMultiplierDifference : Bool
round113RealitySymmetryAloneGivesMultiplierDifference = false

round113PhysicalCrossTriadAntisymmetricReindexWeldClosed : Bool
round113PhysicalCrossTriadAntisymmetricReindexWeldClosed = false

round113AntisymmetricSharedModePairGivesMultiplierDifferenceIsTrue :
  round113AntisymmetricSharedModePairGivesMultiplierDifference ≡ true
round113AntisymmetricSharedModePairGivesMultiplierDifferenceIsTrue = refl

round113RealitySymmetryAloneGivesMultiplierDifferenceIsFalse :
  round113RealitySymmetryAloneGivesMultiplierDifference ≡ false
round113RealitySymmetryAloneGivesMultiplierDifferenceIsFalse = refl

round113PhysicalCrossTriadAntisymmetricReindexWeldClosedIsFalse :
  round113PhysicalCrossTriadAntisymmetricReindexWeldClosed ≡ false
round113PhysicalCrossTriadAntisymmetricReindexWeldClosedIsFalse = refl
