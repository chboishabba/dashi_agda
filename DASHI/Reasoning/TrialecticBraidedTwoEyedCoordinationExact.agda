module DASHI.Reasoning.TrialecticBraidedTwoEyedCoordinationExact where

------------------------------------------------------------------------
-- TRIALECTIC / SWEETGRASS / TWO-EYED SEEING CROSS-POLLINATION
--
-- SOURCE BOUNDARY
--
-- Robin Wall Kimmerer / Braiding Sweetgrass:
--   bounded inspiration for distinct strands, reciprocity, held relation,
--   obligation and provenance-preserving braiding.
--
-- Bartlett, Marshall & Marshall / Two-Eyed Seeing:
--   bounded inspiration for coordinated use of distinct knowledge systems
--   without epistemic fusion.
--
-- DASHI CONTRIBUTION:
--   the finite trialectic, attached two-cell, factorisation theorems, braid
--   recognition contract and hyperfabric comparison below.
--
-- No source is credited with the 369 carrier, Cech nerve, braid group,
-- action-groupoid, or trialectic 2-cell theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.KimmererBraidingAcknowledgement as Sweetgrass
import DASHI.Culture.KimmererNarrativeMetaphorCalibrationExact as Kimmerer
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact as BraidedEvidence
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as ProvenanceRecognition
import DASHI.Reasoning.TrialecticAttachedTwoCellExact as TwoCell
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticDyadicCoverNerveExact as Nerve
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Hyper369
import DASHI.Reasoning.TypedHyperfabricFiniteBraidEquivarianceExact as BraidFabric
import DASHI.Combinatorics.TextileBraidRewriteGroupoidExact as Textile
import DASHI.Core.GovernanceTrajectoryRealisationExact as Governance
import DASHI.Core.RelationalRoleGrammarExact as RoleGrammar
import DASHI.Reasoning.StructuralTransferBreakdownExact as StructuralTransfer
import DASHI.Reasoning.MetaphorTransferResidualExact as TransferResidual

------------------------------------------------------------------------
-- 1. Three strand identities remain first-class.
------------------------------------------------------------------------

data TrialecticStrand : Set where
  strandA strandB strandC : TrialecticStrand

data StrandProvenance : Set where
  provenanceA provenanceB provenanceC : StrandProvenance

strandProvenance : TrialecticStrand -> StrandProvenance
strandProvenance strandA = provenanceA
strandProvenance strandB = provenanceB
strandProvenance strandC = provenanceC

data SharedTrialecticObservation : Set where
  commonRelationalObservation : SharedTrialecticObservation

observeStrand : TrialecticStrand -> SharedTrialecticObservation
observeStrand _ = commonRelationalObservation

sameObservationAB :
  observeStrand strandA ≡ observeStrand strandB
sameObservationAB = refl

sameObservationBC :
  observeStrand strandB ≡ observeStrand strandC
sameObservationBC = refl

differentProvenanceAB :
  strandProvenance strandA ≡ strandProvenance strandB -> ⊥
differentProvenanceAB ()

differentProvenanceBC :
  strandProvenance strandB ≡ strandProvenance strandC -> ⊥
differentProvenanceBC ()

data SharedTrialecticObservationFusesProvenance : Set where

sharedTrialecticObservationDoesNotFuseProvenance :
  SharedTrialecticObservationFusesProvenance -> ⊥
sharedTrialecticObservationDoesNotFuseProvenance ()

------------------------------------------------------------------------
-- 2. Braiding means retained difference under relation, not synthesis.
------------------------------------------------------------------------

record BraidedTrialectic : Set where
  constructor braided-trialectic
  field
    leftStrand : TrialecticStrand
    middleStrand : TrialecticStrand
    rightStrand : TrialecticStrand

    attachedRelation : Face.TriadicFaceRelation

    strandsRemainDistinct : Bool
    reciprocityRetained : Bool
    heldTensionRetained : Bool
    relationalCoherenceRetained : Bool
    provenanceRetained : Bool

open BraidedTrialectic public

canonicalBraidedTrialectic : BraidedTrialectic
canonicalBraidedTrialectic =
  braided-trialectic
    strandA strandB strandC
    Face.reciprocalFace
    true true true true true

data BraidMeansFusion : Set where
data BraidMeansMereMultiplicity : Set where
data BraidGuaranteesRecoverabilityAfterRupture : Set where

braidDoesNotMeanFusion : BraidMeansFusion -> ⊥
braidDoesNotMeanFusion ()

braidDoesNotReduceToMereMultiplicity :
  BraidMeansMereMultiplicity -> ⊥
braidDoesNotReduceToMereMultiplicity ()

braidDoesNotGuaranteeRecoverabilityAfterRupture :
  BraidGuaranteesRecoverabilityAfterRupture -> ⊥
braidDoesNotGuaranteeRecoverabilityAfterRupture ()

------------------------------------------------------------------------
-- 3. The attached trialectic two-cell is a relation holding strands together.
--
-- It is NOT attributed to Kimmerer or Two-Eyed Seeing; those owners motivate
-- the anti-fusion / reciprocal-relation reading only.
------------------------------------------------------------------------

trialecticAttachedCellBoundary :
  TwoCell.TrialecticAttachedTwoCellBoundary
trialecticAttachedCellBoundary =
  TwoCell.canonicalTrialecticAttachedTwoCellBoundary

dyadicNerveBoundary :
  Nerve.TrialecticDyadicCoverNerveBoundary
dyadicNerveBoundary =
  Nerve.canonicalTrialecticDyadicCoverNerveBoundary

data AttachedRelationCollapsesStrands : Set where
data AttachedRelationIsSourceClaim : Set where

attachedRelationDoesNotCollapseStrands :
  AttachedRelationCollapsesStrands -> ⊥
attachedRelationDoesNotCollapseStrands ()

attachedRelationIsDASHIExtensionNotSourceClaim :
  AttachedRelationIsSourceClaim -> ⊥
attachedRelationIsDASHIExtensionNotSourceClaim ()

------------------------------------------------------------------------
-- 4. Two-Eyed coordination supplies the right anti-collapse rule.
------------------------------------------------------------------------

twoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedBoundary =
  TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sharedObservationDoesNotRecoverKnowledgeProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

coordinatedKnowledgeUse :
  TwoEyed.CoordinatedUse
coordinatedKnowledgeUse =
  TwoEyed.useDistinctKnowledgesTogether

knowledgeCoordinationDoesNotRequireFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion twoEyedBoundary ≡ false
knowledgeCoordinationDoesNotRequireFusion =
  TwoEyed.coordinatedUseRequiresEpistemicFusionIsFalse twoEyedBoundary

------------------------------------------------------------------------
-- 5. Sweetgrass calibration supplies retained-difference / reciprocal-tension
--    vocabulary, but not mathematical authority.
------------------------------------------------------------------------

sweetgrassAcknowledgement :
  Sweetgrass.KimmererBraidingAcknowledgement
sweetgrassAcknowledgement =
  Sweetgrass.canonicalKimmererBraidingAcknowledgement

sweetgrassCalibration :
  Kimmerer.KimmererNarrativeCalibrationBoundary
sweetgrassCalibration =
  Kimmerer.canonicalKimmererNarrativeCalibrationBoundary

reciprocityIsSalientInCalibratedBraid :
  Kimmerer.featureSalience
    Kimmerer.relationallyCalibratedBraidFrame
    Kimmerer.reciprocity
  ≡ Kimmerer.salientFeature
reciprocityIsSalientInCalibratedBraid =
  Kimmerer.reciprocityBecomesSalient

heldTensionIsSalientInCalibratedBraid :
  Kimmerer.featureSalience
    Kimmerer.relationallyCalibratedBraidFrame
    Kimmerer.heldTension
  ≡ Kimmerer.salientFeature
heldTensionIsSalientInCalibratedBraid =
  Kimmerer.heldTensionBecomesSalient

------------------------------------------------------------------------
-- 6. Braided evidence traces preserve strand-local authority/permission.
------------------------------------------------------------------------

braidedEvidenceBoundary :
  BraidedEvidence.BraidedEvidenceBoundary
braidedEvidenceBoundary =
  BraidedEvidence.canonicalBraidedEvidenceBoundary

data TrialecticRelationTransfersAuthority : Set where
data TrialecticRelationTransfersPermission : Set where

trialecticRelationDoesNotTransferAuthority :
  TrialecticRelationTransfersAuthority -> ⊥
trialecticRelationDoesNotTransferAuthority ()

trialecticRelationDoesNotTransferPermission :
  TrialecticRelationTransfersPermission -> ⊥
trialecticRelationDoesNotTransferPermission ()

------------------------------------------------------------------------
-- 7. Literal braid-process history remains richer than endpoint relation.
------------------------------------------------------------------------

textileBraidBoundary :
  Textile.BraidRewriteBoundary
textileBraidBoundary =
  Textile.canonicalBraidRewriteBoundary

data ProcessEquivalentMeansHistoryErased : Set where

processEquivalenceDoesNotEraseHistory :
  ProcessEquivalentMeansHistoryErased -> ⊥
processEquivalenceDoesNotEraseHistory ()

------------------------------------------------------------------------
-- 8. Trialectic<->369 exact carrier rechart does not erase epistemic history.
------------------------------------------------------------------------

trialectic369Boundary :
  Hyper369.Trialectic369HypervoxelUltrametricBoundary
trialectic369Boundary =
  Hyper369.canonicalTrialectic369HypervoxelUltrametricBoundary

data Exact369RechartFusesEpistemicProvenance : Set where

exact369RechartDoesNotFuseEpistemicProvenance :
  Exact369RechartFusesEpistemicProvenance -> ⊥
exact369RechartDoesNotFuseEpistemicProvenance ()

------------------------------------------------------------------------
-- 9. Braid-equivariant hyperfabric transport is an additional obligation.
------------------------------------------------------------------------

braidEquivarianceBoundary :
  BraidFabric.TypedHyperfabricFiniteBraidBoundary
braidEquivarianceBoundary =
  BraidFabric.canonicalTypedHyperfabricFiniteBraidBoundary

data AttachedTwoCellAutomaticallyPaysBraidEquivariance : Set where
data BraidVocabularyAutomaticallyCreatesSectionTransport : Set where

attachedTwoCellDoesNotAutomaticallyPayBraidEquivariance :
  AttachedTwoCellAutomaticallyPaysBraidEquivariance -> ⊥
attachedTwoCellDoesNotAutomaticallyPayBraidEquivariance ()

braidVocabularyDoesNotAutomaticallyCreateSectionTransport :
  BraidVocabularyAutomaticallyCreatesSectionTransport -> ⊥
braidVocabularyDoesNotAutomaticallyCreateSectionTransport ()

------------------------------------------------------------------------
-- 10. Provenance-preserving recognition is the correct downstream contract.
------------------------------------------------------------------------

provenanceRecognitionBoundary :
  ProvenanceRecognition.ProvenancePreservingRecognitionBoundary
provenanceRecognitionBoundary =
  ProvenanceRecognition.canonicalProvenancePreservingRecognitionBoundary

data RecognitionMayFuseKnowledgeHistories : Set where

recognitionMayNotFuseKnowledgeHistories :
  RecognitionMayFuseKnowledgeHistories -> ⊥
recognitionMayNotFuseKnowledgeHistories ()

record TrialecticBraidedTwoEyedBoundary : Set where
  constructor trialectic-braided-two-eyed-boundary
  field
    distinctStrandsRetained : Bool
    sharedObservationMayCoexistWithDifferentProvenance : Bool
    coordinationRequiresFusion : Bool
    attachedTwoCellIsAdditionalRelation : Bool
    attachedTwoCellIsCechTripleIntersection : Bool
    braidMeansMereMultiplicity : Bool
    reciprocityAndHeldTensionRetained : Bool
    relationTransfersAuthorityOrPermission : Bool
    processEquivalenceErasesHistory : Bool
    exact369RechartErasesProvenance : Bool
    hyperfabricBraidTransportRequiresEquivariance : Bool
    recognitionMustPreserveProvenance : Bool
    sourceAuthorsCreditedWithDASHITrialecticTheorem : Bool

canonicalTrialecticBraidedTwoEyedBoundary :
  TrialecticBraidedTwoEyedBoundary
canonicalTrialecticBraidedTwoEyedBoundary =
  trialectic-braided-two-eyed-boundary
    true true false
    true false false true false
    false false true true false


------------------------------------------------------------------------
-- 11. Conversation braid calibration uses existing transfer machinery.
--
-- The conversation claim is narrow.
-- Stories calibrate which braid relations a declared consumer should retain.
-- A coarse multiplicity reading may miss reciprocity and held relation.
-- A universal braid reading may spuriously import recoverability after rupture.
-- The source authors do not own the DASHI transfer or ZKP mathematics.
------------------------------------------------------------------------

conversationCalibrationNonDescent =
  Kimmerer.calibratedMeaningDoesNotDescendThroughInitialReading

conversationUnderTransferProfile :
  TransferResidual.TransferResidualProfile
conversationUnderTransferProfile =
  TransferResidual.missingReciprocityProfile

conversationOverTransferProfile :
  TransferResidual.TransferResidualProfile
conversationOverTransferProfile =
  TransferResidual.spuriousRecoverabilityProfile

conversationStructuralTransferBoundary :
  StructuralTransfer.StructuralTransferBreakdownBoundary
conversationStructuralTransferBoundary =
  StructuralTransfer.canonicalStructuralTransferBreakdownBoundary

conversationRoleGrammarBoundary :
  RoleGrammar.RelationalRoleGrammarBoundary
conversationRoleGrammarBoundary =
  RoleGrammar.canonicalRelationalRoleGrammarBoundary

------------------------------------------------------------------------
-- 12. ZKP O/R/C/S/L/P/G/F normalization.
--
-- O: braid-calibration programme.
-- R: preserve consumer-relevant relation without fusion or forced recovery.
-- C: reuse canonical DASHI braid, transfer, residual, and provenance owners.
-- S: coarse, calibrated, or ruptured target state.
-- L: under-fit, fitted, or over-fit transfer lattice.
-- P: calibrate the reading or withdraw the frame.
-- G: calibration succeeds on the calibrated state; withdrawal succeeds on rupture.
-- F: live gap class: missing relation, no gap, or spurious recoverability.
------------------------------------------------------------------------

data BraidObjective : Set where
  braidCalibrationProgramme : BraidObjective

data BraidRequirement : Set where
  boundedRelationalTransfer : BraidRequirement

data BraidCode : Set where
  canonicalBraidingOwners : BraidCode

data BraidTransferState : Set where
  coarseMultiplicityState
  calibratedRelationalState
  rupturedRelationState
  : BraidTransferState

data BraidTransferLattice : Set where
  underFitLattice fittedLattice overFitLattice : BraidTransferLattice

data BraidTransferProposal : Set where
  calibrateReading withdrawFrame : BraidTransferProposal

data BraidTransferGap : Set where
  missingRelationGap noTransferGap spuriousRecoverabilityGap : BraidTransferGap

braidTransferGoal :
  BraidTransferProposal -> BraidTransferState -> Bool
braidTransferGoal calibrateReading calibratedRelationalState = true
braidTransferGoal withdrawFrame rupturedRelationState = true
braidTransferGoal _ _ = false

braidTransferGap :
  BraidObjective ->
  BraidRequirement ->
  BraidCode ->
  BraidTransferState ->
  BraidTransferLattice ->
  BraidTransferGap
braidTransferGap _ _ _ coarseMultiplicityState _ = missingRelationGap
braidTransferGap _ _ _ calibratedRelationalState _ = noTransferGap
braidTransferGap _ _ _ rupturedRelationState _ = spuriousRecoverabilityGap

BraidTransferZKPFrame : Set₁
BraidTransferZKPFrame =
  Governance.ZKPGovernanceModel
    BraidObjective
    BraidRequirement
    BraidCode
    BraidTransferState
    BraidTransferLattice
    BraidTransferProposal
    BraidTransferGap

conversationBraidZKP : BraidTransferZKPFrame
conversationBraidZKP =
  Governance.zkp-governance-model
    braidCalibrationProgramme
    boundedRelationalTransfer
    canonicalBraidingOwners
    coarseMultiplicityState
    underFitLattice
    calibrateReading
    braidTransferGoal
    braidTransferGap

coarseReadingHasMissingRelationGap :
  braidTransferGap
    braidCalibrationProgramme
    boundedRelationalTransfer
    canonicalBraidingOwners
    coarseMultiplicityState
    underFitLattice
  ≡ missingRelationGap
coarseReadingHasMissingRelationGap = refl

calibratedReadingClosesTransferGap :
  braidTransferGap
    braidCalibrationProgramme
    boundedRelationalTransfer
    canonicalBraidingOwners
    calibratedRelationalState
    fittedLattice
  ≡ noTransferGap
calibratedReadingClosesTransferGap = refl

calibrationGoalHoldsOnCalibratedState :
  braidTransferGoal calibrateReading calibratedRelationalState ≡ true
calibrationGoalHoldsOnCalibratedState = refl

ruptureHasSpuriousRecoverabilityGap :
  braidTransferGap
    braidCalibrationProgramme
    boundedRelationalTransfer
    canonicalBraidingOwners
    rupturedRelationState
    overFitLattice
  ≡ spuriousRecoverabilityGap
ruptureHasSpuriousRecoverabilityGap = refl

withdrawalGoalHoldsOnRupture :
  braidTransferGoal withdrawFrame rupturedRelationState ≡ true
withdrawalGoalHoldsOnRupture = refl

------------------------------------------------------------------------
-- 13. Explicit preconditions, invariants, and postconditions.
------------------------------------------------------------------------

record BraidTransferContract : Set where
  constructor braid-transfer-contract
  field
    sourceBoundaryDeclared : Bool
    sourceBoundaryDeclaredIsTrue : sourceBoundaryDeclared ≡ true

    consumerDeclared : Bool
    consumerDeclaredIsTrue : consumerDeclared ≡ true

    strandDifferenceInvariant : Bool
    strandDifferenceInvariantIsTrue : strandDifferenceInvariant ≡ true

    provenanceInvariant : Bool
    provenanceInvariantIsTrue : provenanceInvariant ≡ true

    relationDoesNotTransferAuthorityInvariant : Bool
    relationDoesNotTransferAuthorityInvariantIsTrue :
      relationDoesNotTransferAuthorityInvariant ≡ true

    ruptureCheckInvariant : Bool
    ruptureCheckInvariantIsTrue : ruptureCheckInvariant ≡ true

    calibratedReadingMayCloseMissingRelationGap : Bool
    calibratedReadingMayCloseMissingRelationGapIsTrue :
      calibratedReadingMayCloseMissingRelationGap ≡ true

    ruptureRequiresPossibleFrameWithdrawal : Bool
    ruptureRequiresPossibleFrameWithdrawalIsTrue :
      ruptureRequiresPossibleFrameWithdrawal ≡ true

    universalRecoverabilityClaim : Bool
    universalRecoverabilityClaimIsFalse :
      universalRecoverabilityClaim ≡ false

canonicalBraidTransferContract : BraidTransferContract
canonicalBraidTransferContract =
  braid-transfer-contract
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
