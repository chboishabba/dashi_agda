module DASHI.Physics.YangMills.YangMillsClayPinnedLiteralCompilerExact where

------------------------------------------------------------------------
-- PINNED PHYSICAL CONSTRUCTION -> LITERAL CLAY SOLUTION
--
-- The only extra endpoint input beyond the pinned A/B/C construction is the
-- interacting/nontriviality theorem on the SAME continuum measure/Schwinger
-- family.  No new physical objects are introduced here.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as T78
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

record PinnedInteractingContinuum
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) : Set₁ where
  field
    nontrivialQuantumYangMills : ∀ G →
      Top.IsNontrivialQuantumYangMills S G
        (Pinned.continuumMeasure (Pinned.continuum pinned) G)
        (Pinned.schwinger (Pinned.continuum pinned) G)

    nontrivialityPreservedInLimit : ∀ G →
      Top.NontrivialityPreservedInLimit S G
        (Pinned.continuumMeasure (Pinned.continuum pinned) G)

open PinnedInteractingContinuum public

compileInteractingContinuum :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  PinnedInteractingContinuum pinned →
  Five.InteractingContinuumNontriviality
    (Pinned.asLiteralYangMillsConstruction pinned)
compileInteractingContinuum pinned interacting = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      nontrivialQuantumYangMills interacting
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      nontrivialityPreservedInLimit interacting
  }

literalClayEvidenceFromPinned :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  PinnedInteractingContinuum pinned →
  Top.LiteralClayEvidence
    (Pinned.asLiteralYangMillsConstruction pinned)
literalClayEvidenceFromPinned pinned interacting =
  Five.literalClayEvidenceFromFiveTheorems
    (Pinned.asLiteralYangMillsConstruction pinned)
    (Pinned.compileStructuralBase pinned)
    (Pinned.compileWeakCouplingRG pinned)
    (Pinned.compilePhysicalMassGap pinned)
    (Pinned.compileUnifiedContinuum pinned)
    (Pinned.compileLocalQFT pinned)
    (compileInteractingContinuum pinned interacting)

literalClaySolutionFromPinned :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  PinnedInteractingContinuum pinned →
  Clay.ClayYangMillsSolution
    (Top.literalClayVocabulary
      (Pinned.asLiteralYangMillsConstruction pinned))
literalClaySolutionFromPinned pinned interacting =
  Top.literalTopDownClaySolution
    (Pinned.asLiteralYangMillsConstruction pinned)
    (literalClayEvidenceFromPinned pinned interacting)


------------------------------------------------------------------------
-- Preferred three-theorem endpoint.
--
-- Nontriviality is NOT a fourth independent physical input.  Compile it from
-- the SAME-H physical gap and SAME-family local-QFT data through Round78's
-- standard Gaussian/free-field consequence.
------------------------------------------------------------------------

compileInteractingContinuumFromPinnedABC :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.StandardSameHGaussianNontrivialityConsequence
    (Pinned.asLiteralYangMillsConstruction pinned) →
  Five.InteractingContinuumNontriviality
    (Pinned.asLiteralYangMillsConstruction pinned)
compileInteractingContinuumFromPinnedABC pinned standard =
  T78.deriveInteracting standard
    (Pinned.compilePhysicalMassGap pinned)
    (Pinned.compileLocalQFT pinned)

literalClayEvidenceFromPinnedABC :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.StandardSameHGaussianNontrivialityConsequence
    (Pinned.asLiteralYangMillsConstruction pinned) →
  Top.LiteralClayEvidence
    (Pinned.asLiteralYangMillsConstruction pinned)
literalClayEvidenceFromPinnedABC pinned standard =
  Five.literalClayEvidenceFromFiveTheorems
    (Pinned.asLiteralYangMillsConstruction pinned)
    (Pinned.compileStructuralBase pinned)
    (Pinned.compileWeakCouplingRG pinned)
    (Pinned.compilePhysicalMassGap pinned)
    (Pinned.compileUnifiedContinuum pinned)
    (Pinned.compileLocalQFT pinned)
    (compileInteractingContinuumFromPinnedABC pinned standard)

literalClaySolutionFromPinnedABC :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.StandardSameHGaussianNontrivialityConsequence
    (Pinned.asLiteralYangMillsConstruction pinned) →
  Clay.ClayYangMillsSolution
    (Top.literalClayVocabulary
      (Pinned.asLiteralYangMillsConstruction pinned))
literalClaySolutionFromPinnedABC pinned standard =
  Top.literalTopDownClaySolution
    (Pinned.asLiteralYangMillsConstruction pinned)
    (literalClayEvidenceFromPinnedABC pinned standard)

pinnedABCNontrivialityCompilerLevel : ProofLevel
pinnedABCNontrivialityCompilerLevel = machineChecked

pinnedABCToLiteralClayCompilerLevel : ProofLevel
pinnedABCToLiteralClayCompilerLevel = machineChecked

------------------------------------------------------------------------
-- T78 projections are definitionally the same pinned construction.
------------------------------------------------------------------------

pinnedT78A :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.UVToContinuumYM
    (Pinned.asLiteralYangMillsConstruction pinned)
pinnedT78A = Pinned.compileT78A

pinnedT78B :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.SameHamiltonianPhysicalMassGap
    (Pinned.asLiteralYangMillsConstruction pinned)
pinnedT78B = Pinned.compileT78B

pinnedT78C :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S) →
  T78.SameFamilyLocalFieldsOPEStressWard
    (Pinned.asLiteralYangMillsConstruction pinned)
pinnedT78C = Pinned.compileT78C

pinnedLiteralClayCompilerLevel : ProofLevel
pinnedLiteralClayCompilerLevel = machineChecked

pinnedInteractingContinuumInputLevel : ProofLevel
pinnedInteractingContinuumInputLevel = conditional
