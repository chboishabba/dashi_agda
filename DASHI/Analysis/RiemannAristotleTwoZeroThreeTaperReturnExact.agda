module DASHI.Analysis.RiemannAristotleTwoZeroThreeTaperReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CROSS-PROVER RETURN: inhabited two-zero / three-taper Lean theorem.
--
-- This file records the theorem surface now owned by the separate Aristotle
-- Lean project after the shared-window/certified-carrier return.  It does NOT
-- transport the Lean proof term into Agda and does NOT derive RH.
--
-- Lean now owns, for three literal zeros with strictly ordered positive height
-- moduli, an explicitly constructed triple of continuous, compactly supported,
-- nonnegative tapers and a positive small-radius threshold such that:
--
--   * the target survives exact elimination of two selected nuisance responses;
--   * the residual norm-square is strictly positive;
--   * adding the two nuisance responses before elimination changes nothing.
--
-- The proof route is determinant-based:
--
--   point-window 3x3 nonsingularity
--     -> positive-width narrow-window determinant
--     -> nonzero leading determinant
--     -> small-radius literal determinant != 0
--     -> exact double Gram-Schmidt elimination.
--
-- Equal height moduli remain a genuine degeneracy.  The projected far-tail
-- budget B_far remains open.
------------------------------------------------------------------------

data CrossProverOwner : Set where
  leanAristotleOwner openObligation : CrossProverOwner

record TwoZeroThreeTaperReturn : Set where
  constructor two-zero-three-taper-return
  field
    theoremName : String
    owner : CrossProverOwner
    machineCheckedInOwner : Bool
    transportedIntoAgda : Bool

    constructedPositiveTaperTriple : Bool
    constructedPositiveTaperTripleIsTrue : constructedPositiveTaperTriple ≡ true

    twoSelectedNuisancesEliminatedExactly : Bool
    twoSelectedNuisancesEliminatedExactlyIsTrue :
      twoSelectedNuisancesEliminatedExactly ≡ true

    targetResidualNonzero : Bool
    targetResidualNonzeroIsTrue : targetResidualNonzero ≡ true

    targetResidualNormSqPositive : Bool
    targetResidualNormSqPositiveIsTrue : targetResidualNormSqPositive ≡ true

    equalHeightDegeneracyRemoved : Bool
    equalHeightDegeneracyRemovedIsFalse : equalHeightDegeneracyRemoved ≡ false

    projectedFarTailBudgetClosed : Bool
    projectedFarTailBudgetClosedIsFalse : projectedFarTailBudgetClosed ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    boundedReading : String

open TwoZeroThreeTaperReturn public

canonicalTwoZeroThreeTaperReturn : TwoZeroThreeTaperReturn
canonicalTwoZeroThreeTaperReturn =
  two-zero-three-taper-return
    "LiteralWeilThreeWindowNarrowInstance.exists_taper_triple_two_zero_admission"
    leanAristotleOwner true false
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Lean owns an inhabited exact two-selected-zero Schur elimination using three constructed narrow tapers. The remaining analytic frontier is the projected far-tail budget; this status object is provenance, not an Agda proof of the Lean theorem."

------------------------------------------------------------------------
-- Structural reading of the remaining cutset.
------------------------------------------------------------------------

record TwoZeroFarTailFrontier : Set where
  constructor two-zero-far-tail-frontier
  field
    selectedCarrierSize : Nat
    selectedCarrierSizeIsTwo : selectedCarrierSize ≡ 2
    exactSelectedEliminationOwned : Bool
    exactSelectedEliminationOwnedIsTrue : exactSelectedEliminationOwned ≡ true
    localSelectedResidualDebt : Bool
    localSelectedResidualDebtIsFalse : localSelectedResidualDebt ≡ false
    farProjectedTailBudgetRequired : Bool
    farProjectedTailBudgetRequiredIsTrue : farProjectedTailBudgetRequired ≡ true
    absoluteMajorantRouteRevived : Bool
    absoluteMajorantRouteRevivedIsFalse : absoluteMajorantRouteRevived ≡ false
    boundedReading : String

open TwoZeroFarTailFrontier public

canonicalTwoZeroFarTailFrontier : TwoZeroFarTailFrontier
canonicalTwoZeroFarTailFrontier =
  two-zero-far-tail-frontier
    2 refl
    true refl
    false refl
    true refl
    false refl
    "After exact elimination the two selected nuisance directions contribute no residual debt. The unresolved payment is the projected remainder of the literal unselected carrier plus the prime/Gamma channels; the old absolute W(t)-majorant no-go is not bypassed merely by eliminating two zeros."
