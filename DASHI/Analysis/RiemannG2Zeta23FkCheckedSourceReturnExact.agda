module DASHI.Analysis.RiemannG2Zeta23FkCheckedSourceReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CHECKED-SOURCE RETURN: literal Zeta23 f_k test family
--
-- Source audited from the supplied Zeta23 checkout.
--
-- Zeta23/Defs.lean defines
--   f_k(u) = phi(u) * exp(-(i * tau_k * u)).
--
-- Zeta23/Hypotheses/GzGp.lean proves on that same literal f_k:
--   paperFT_fk : paperFT (f_k) z = phiHat (z - tau_k)
--   fk_contDiff : ContDiff R 2 (f_k)
--   fk_tsupport : tsupport (f_k) subset [-L/2,L/2].
--
-- XiPrime/ExplicitFormula/TestWeight.lean then packages:
--   fk_hasCompactSupport
--   fk_continuous
-- and uses those exact f_k tests in the source explicit-formula lane.
--
-- This owner records that theorem surface and its BIDI consequence only.
-- It does not transport Lean proof terms into Agda and does not identify the
-- Lean function carrier with the abstract Agda Weil/Mellin Test carrier.
------------------------------------------------------------------------

data CrossProverAuthority : Set where
  checkedLeanSource openAgdaAttachment : CrossProverAuthority

record Zeta23FkCheckedSourceReturn : Set where
  constructor zeta23-fk-checked-source-return
  field
    sourcePackage : String
    authority : CrossProverAuthority
    leanProofTermsPresent : Bool
    transportedIntoAgda : Bool

    literalFkDefinitionOwned : Bool
    literalFkDefinitionOwnedIsTrue : literalFkDefinitionOwned ≡ true

    sameFkPaperFTShiftOwned : Bool
    sameFkPaperFTShiftOwnedIsTrue : sameFkPaperFTShiftOwned ≡ true

    sameFkContDiffTwoOwned : Bool
    sameFkContDiffTwoOwnedIsTrue : sameFkContDiffTwoOwned ≡ true

    sameFkSupportWindowOwned : Bool
    sameFkSupportWindowOwnedIsTrue : sameFkSupportWindowOwned ≡ true

    sameFkCompactSupportOwned : Bool
    sameFkCompactSupportOwnedIsTrue : sameFkCompactSupportOwned ≡ true

    sameFkContinuityOwned : Bool
    sameFkContinuityOwnedIsTrue : sameFkContinuityOwned ≡ true

    sameFkUsedByExplicitFormulaLane : Bool
    sameFkUsedByExplicitFormulaLaneIsTrue : sameFkUsedByExplicitFormulaLane ≡ true

    canonicalAgdaMellinTestIdentityOwned : Bool
    canonicalAgdaMellinTestIdentityOwnedIsFalse :
      canonicalAgdaMellinTestIdentityOwned ≡ false

    sourceReferences : String
    highestAlphaReading : String

open Zeta23FkCheckedSourceReturn public

canonicalZeta23FkCheckedSourceReturn : Zeta23FkCheckedSourceReturn
canonicalZeta23FkCheckedSourceReturn =
  zeta23-fk-checked-source-return
    "supplied Zeta23 checkout"
    checkedLeanSource
    true
    false
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Zeta23/Defs.lean; Zeta23/Hypotheses/GzGp.lean; Zeta23/XiPrime/ExplicitFormula/TestWeight.lean"
    "The source-side H_A test family is already substantially closed: the literal target-character action f_k is defined, paperFT_fk proves the exact frequency translation on the same f_k, and the same test has C^2, support, compact-support and continuity witnesses used by the explicit-formula lane. Do not search for another modulation operator or rebuild its analytic prerequisites. The live payment is cross-prover/same-object attachment of this concrete source test family to the canonical Agda Weil/Mellin Test and transport of the checked source theorems into the proof-relevant H_A consumer."

------------------------------------------------------------------------
-- Search pruning.
------------------------------------------------------------------------

data FkSourceSearchAction : Set where
  searchForAnotherModulationOperator
  reproveSourcePaperFTShift
  reproveSourceContDiff
  reproveSourceCompactSupport
  attachConcreteFkFamilyToCanonicalAgdaTest
  transportCheckedSourceTheorems
  : FkSourceSearchAction

FkSourceRelevant : FkSourceSearchAction → Set
FkSourceRelevant searchForAnotherModulationOperator = ⊥
FkSourceRelevant reproveSourcePaperFTShift = ⊥
FkSourceRelevant reproveSourceContDiff = ⊥
FkSourceRelevant reproveSourceCompactSupport = ⊥
FkSourceRelevant attachConcreteFkFamilyToCanonicalAgdaTest = ⊤
FkSourceRelevant transportCheckedSourceTheorems = ⊤

anotherModulationSearchPruned :
  FkSourceRelevant searchForAnotherModulationOperator → ⊥
anotherModulationSearchPruned x = x

sourceShiftReproofPruned :
  FkSourceRelevant reproveSourcePaperFTShift → ⊥
sourceShiftReproofPruned x = x

sourceContDiffReproofPruned :
  FkSourceRelevant reproveSourceContDiff → ⊥
sourceContDiffReproofPruned x = x

sourceCompactSupportReproofPruned :
  FkSourceRelevant reproveSourceCompactSupport → ⊥
sourceCompactSupportReproofPruned x = x

record Zeta23FkCheckedSourceBoundary : Set where
  constructor zeta23-fk-checked-source-boundary
  field
    sourceActionStillMathematicallyOpen : Bool
    sourceActionStillMathematicallyOpenIsFalse : sourceActionStillMathematicallyOpen ≡ false

    sourceTransformShiftStillMathematicallyOpen : Bool
    sourceTransformShiftStillMathematicallyOpenIsFalse :
      sourceTransformShiftStillMathematicallyOpen ≡ false

    sourceAdmissibilityPrerequisitesStillMathematicallyOpen : Bool
    sourceAdmissibilityPrerequisitesStillMathematicallyOpenIsFalse :
      sourceAdmissibilityPrerequisitesStillMathematicallyOpen ≡ false

    agdaSameObjectAttachmentStillOpen : Bool
    agdaSameObjectAttachmentStillOpenIsTrue : agdaSameObjectAttachmentStillOpen ≡ true

    leanProofTransportStillOpen : Bool
    leanProofTransportStillOpenIsTrue : leanProofTransportStillOpen ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalZeta23FkCheckedSourceBoundary : Zeta23FkCheckedSourceBoundary
canonicalZeta23FkCheckedSourceBoundary =
  zeta23-fk-checked-source-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
