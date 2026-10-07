module DASHI.ComputerScience.TekumDASHIRoundingBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.ComputerScience.TekumEfficientNearestRoundingExact as Efficient
import DASHI.ComputerScience.TekumNearestNoDoubleRoundingExact as NoDouble
import DASHI.ComputerScience.TekumProposition5FiniteNearestNoGoExact as HunholdNoGo
import DASHI.ComputerScience.TekumRawNearestCorrectionExact as Raw

------------------------------------------------------------------------
-- Independent DASHI rounding truth boundary.
--
-- Historical Hunhold/raw flags are not reinterpreted.  This owner records the
-- new exact-nearest programme and its max-cut: semantic relation + tie policy
-- exist; exhaustive exact discovery refutes raw-local efficiency and refutes
-- no-double-rounding under the intrinsic lower-source-code tie rule.
------------------------------------------------------------------------

data NoDoubleOutcome : Set where
  noDoubleProved : NoDoubleOutcome
  noDoubleRefuted : NoDoubleOutcome
  noDoubleOpen : NoDoubleOutcome

isPaid : NoDoubleOutcome → Bool
isPaid noDoubleProved = true
isPaid noDoubleRefuted = false
isPaid noDoubleOpen = false

isRefuted : NoDoubleOutcome → Bool
isRefuted noDoubleProved = false
isRefuted noDoubleRefuted = true
isRefuted noDoubleOpen = false

record TekumDASHIRoundingBoundary : Set where
  constructor tekumDASHIRoundingBoundary
  field
    hunholdRawTruncationNearestRefuted : Bool
    dashiExactNearestSemanticsPresent : Bool
    nearestExistencePaid : Bool
    canonicalTieRulePaid : Bool
    rawCorrectionRadiusCharacterized : Bool
    efficientNearestImplementationPaid : Bool
    efficientNearestEqualsSemanticOraclePaid : Bool
    nearestNoDoubleRoundingPaid : Bool
    nearestNoDoubleRoundingRefuted : Bool
    noDoubleOutcome : NoDoubleOutcome
    paidMatchesOutcome : nearestNoDoubleRoundingPaid ≡ isPaid noDoubleOutcome
    refutedMatchesOutcome : nearestNoDoubleRoundingRefuted ≡ isRefuted noDoubleOutcome
open TekumDASHIRoundingBoundary public

canonicalTekumDASHIRoundingBoundary : TekumDASHIRoundingBoundary
canonicalTekumDASHIRoundingBoundary =
  tekumDASHIRoundingBoundary
    true   -- Hunhold raw nearestness already refuted
    true   -- exact rational set-valued DASHI semantics present
    false  -- general Agda finite-minimum witness construction still separate
    true   -- lower source-code tie policy is explicitly formalized
    true   -- exact 10→8/12→10 radius census + radius-one kernel falsifier
    false  -- raw-local efficient implementation refuted/fail-closed
    false  -- therefore no efficient=oracle theorem
    false  -- no-double theorem does not survive
    true   -- exact exhaustive 12→10→8 counterexample + same-object owner
    noDoubleRefuted refl refl

nearestNoDoubleMutualExclusion :
  ∀ (boundary : TekumDASHIRoundingBoundary) →
  nearestNoDoubleRoundingPaid boundary ≡ true →
  nearestNoDoubleRoundingRefuted boundary ≡ true →
  ⊥
nearestNoDoubleMutualExclusion
  (tekumDASHIRoundingBoundary h s e t r i q paid refuted noDoubleProved refl refl)
  refl ()
nearestNoDoubleMutualExclusion
  (tekumDASHIRoundingBoundary h s e t r i q paid refuted noDoubleRefuted refl refl)
  () refl
nearestNoDoubleMutualExclusion
  (tekumDASHIRoundingBoundary h s e t r i q paid refuted noDoubleOpen refl refl)
  () ()

hunholdFiniteRepairStillRefuted :
  ¬ HunholdNoGo.RawTruncationNearestOnFiniteClosure
hunholdFiniteRepairStillRefuted =
  HunholdNoGo.finiteClosureDoesNotRepairProposition5

rawRadiusOneStillRefuted :
  ¬ Raw.UniformRadiusOneRawCorrection
rawRadiusOneStillRefuted = Efficient.uniformLocalCorrectionNotEstablished

noDoubleSameObjectWitnessPresent :
  NoDouble.DashiNearestNoDoubleRoundingCounterexample
noDoubleSameObjectWitnessPresent =
  NoDouble.dashiNearestNoDoubleRoundingCounterexample
