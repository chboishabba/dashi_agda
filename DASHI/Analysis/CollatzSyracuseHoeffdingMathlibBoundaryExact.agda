module DASHI.Analysis.CollatzSyracuseHoeffdingMathlibBoundaryExact where

------------------------------------------------------------------------
-- MATHLIB HOEFFDING DONOR / DASHI SAME-OBJECT ADAPTER FRONTIER
--
-- External theorem owner:
--   leanprover-community/mathlib4
--   Mathlib/Probability/Moments/SubGaussian.lean
--   ProbabilityTheory.measure_sum_ge_le_of_iIndepFun
--
-- Mathlib already owns the analytic concentration theorem.  DASHI therefore
-- does not rebrand Hoeffding as a new Collatz theorem.  The remaining work is
-- the exact adapter from the already-proved finite uniform BinaryWord carrier
-- to Mathlib's independent centered coordinate functions, followed by the
-- deterministic inclusion of the bad parity-drift event into the chosen
-- upper-tail event.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record MathlibHoeffdingSourceReceipt : Set where
  constructor mathlib-hoeffding-source-receipt
  field
    repository : String
    sourceFile : String
    namespace : String
    theoremName : String
    theoremRole : String

canonicalMathlibHoeffdingSourceReceipt : MathlibHoeffdingSourceReceipt
canonicalMathlibHoeffdingSourceReceipt =
  mathlib-hoeffding-source-receipt
    "leanprover-community/mathlib4"
    "Mathlib/Probability/Moments/SubGaussian.lean"
    "ProbabilityTheory"
    "measure_sum_ge_le_of_iIndepFun"
    "Hoeffding inequality for sums of independent sub-Gaussian random variables"

record FiniteWordHoeffdingAdapter (m : Nat) : Set₁ where
  field
    -- Same-object carrier identification, not cardinality matching.
    WordCarrier : Set
    uniformWordCarrierIsDASHIBinaryWord : Set

    -- Coordinate layer required by the Mathlib theorem.
    CoordinateIndex : Set
    centeredCoordinate : CoordinateIndex → WordCarrier → Set
    coordinateMeasurability : Set
    coordinateIndependence : Set
    centeredCoordinateBounds : Set
    centeredCoordinateMeanZero : Set

    -- Deterministic event comparison required for the actual Collatz consumer.
    BadParityDriftEvent : WordCarrier → Set
    HoeffdingUpperTailEvent : WordCarrier → Set
    badImpliesHoeffdingTail :
      (word : WordCarrier) →
      BadParityDriftEvent word →
      HoeffdingUpperTailEvent word

    -- Cross-prover theorem realization receipt.
    mathlibHoeffdingInstantiated : Set

open FiniteWordHoeffdingAdapter public

data MathlibTheoremAutomaticallyImportsToAgda : Set where
data UniformCardinalityAutomaticallyCreatesIndependence : Set where
data HoeffdingAutomaticallyProvesUniversalCollatz : Set where

mathlibTheoremDoesNotBecomeAgdaKernelProof :
  MathlibTheoremAutomaticallyImportsToAgda → ⊥
mathlibTheoremDoesNotBecomeAgdaKernelProof ()

cardinalityDoesNotCreateIndependence :
  UniformCardinalityAutomaticallyCreatesIndependence → ⊥
cardinalityDoesNotCreateIndependence ()

hoeffdingDoesNotProveUniversalCollatz :
  HoeffdingAutomaticallyProvesUniversalCollatz → ⊥
hoeffdingDoesNotProveUniversalCollatz ()

record HoeffdingBoundary : Set where
  constructor hoeffdingBoundary
  field
    mathlibAnalyticTheoremExists : Bool
    directFiniteWordLawOwnedInAgda : Bool
    exactBadWordEventOwnedInAgda : Bool
    coordinateIndependenceAdapterPaid : Bool
    badEventInclusionAdapterPaid : Bool
    crossProverKernelWeldPaid : Bool
    universalStoppingPaid : Bool

canonicalHoeffdingBoundary : HoeffdingBoundary
canonicalHoeffdingBoundary =
  hoeffdingBoundary
    true true true
    false false false false
