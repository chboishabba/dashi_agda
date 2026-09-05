module DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as S
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as E

------------------------------------------------------------------------
-- SOURCE-vs-CONSTITUTIVE EVIDENCE BIDI
--
-- The experiment literature does not directly identify eta_C.  It provides
-- constraints that route first through source-state and transition matching.
------------------------------------------------------------------------

data EvidenceLeaf : Set where
  sourceCharacterisationLeaf : EvidenceLeaf
  transitionLockLeaf : EvidenceLeaf
  externalProbeLeaf : EvidenceLeaf
  backgroundClosureLeaf : EvidenceLeaf
  replicationLeaf : EvidenceLeaf
  constitutiveResidualLeaf : EvidenceLeaf
  boundedNoPromotionLeaf : EvidenceLeaf

record EvidenceClosureState : Set where
  constructor evidence-closure-state
  field
    sourceCharacterised : Bool
    transitionLocked : Bool
    externalProbeOwned : Bool
    backgroundsClosed : Bool
    replicated : Bool
    constitutiveResidualOwned : Bool

firstOpenEvidenceLeaf : EvidenceClosureState → EvidenceLeaf
firstOpenEvidenceLeaf (evidence-closure-state false t e b r c) = sourceCharacterisationLeaf
firstOpenEvidenceLeaf (evidence-closure-state true false e b r c) = transitionLockLeaf
firstOpenEvidenceLeaf (evidence-closure-state true true false b r c) = externalProbeLeaf
firstOpenEvidenceLeaf (evidence-closure-state true true true false r c) = backgroundClosureLeaf
firstOpenEvidenceLeaf (evidence-closure-state true true true true false c) = replicationLeaf
firstOpenEvidenceLeaf (evidence-closure-state true true true true true false) = constitutiveResidualLeaf
firstOpenEvidenceLeaf (evidence-closure-state true true true true true true) = boundedNoPromotionLeaf

------------------------------------------------------------------------
-- Current public-literature reading.
--
-- We own multiple null/artifact/transition-mismatch constraints, but they do
-- not provide a same-apparatus source reconstruction sufficient to solve eta_C.
------------------------------------------------------------------------

currentPublicConstraintState : EvidenceClosureState
currentPublicConstraintState = evidence-closure-state false false true false true false

currentFirstOpenEvidenceLeaf : EvidenceLeaf
currentFirstOpenEvidenceLeaf = firstOpenEvidenceLeaf currentPublicConstraintState

------------------------------------------------------------------------
-- Constraint interpretation.
------------------------------------------------------------------------

record ExperimentalConstraintInterpretation : Set where
  constructor experimental-constraint-interpretation
  field
    hathawayNullConstrainsPodkletnovLikeGeometry : Bool
    hathawayNullConstrainsPodkletnovLikeGeometryIsTrue :
      hathawayNullConstrainsPodkletnovLikeGeometry ≡ true

    hathawayNullProvesAllEtaCEqualOne : Bool
    hathawayNullProvesAllEtaCEqualOneIsFalse :
      hathawayNullProvesAllEtaCEqualOne ≡ false

    nasaArtifactWeakensUncontrolledPositiveSignals : Bool
    nasaArtifactWeakensUncontrolledPositiveSignalsIsTrue :
      nasaArtifactWeakensUncontrolledPositiveSignals ≡ true

    tajmarTransitionMismatchWeakensSimpleTcLockedModel : Bool
    tajmarTransitionMismatchWeakensSimpleTcLockedModelIsTrue :
      tajmarTransitionMismatchWeakensSimpleTcLockedModel ≡ true

    tajmarUpperBoundConstrainsLargeEnhancementModels : Bool
    tajmarUpperBoundConstrainsLargeEnhancementModelsIsTrue :
      tajmarUpperBoundConstrainsLargeEnhancementModels ≡ true

    literatureClosesNonzeroEtaC : Bool
    literatureClosesNonzeroEtaCIsFalse : literatureClosesNonzeroEtaC ≡ false

canonicalExperimentalConstraintInterpretation : ExperimentalConstraintInterpretation
canonicalExperimentalConstraintInterpretation = experimental-constraint-interpretation
  true refl
  false refl
  true refl
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- Strong firewall: a phase-dependent signal must be source-normalised.
------------------------------------------------------------------------

record SourceNormalisationBoundary : Set where
  constructor source-normalisation-boundary
  field
    phaseDependentSignalAloneDeterminesConstitutiveEnhancement : Bool
    phaseDependentSignalAloneDeterminesConstitutiveEnhancementIsFalse :
      phaseDependentSignalAloneDeterminesConstitutiveEnhancement ≡ false

    sourceNormalisedResidualRequired : Bool
    sourceNormalisedResidualRequiredIsTrue :
      sourceNormalisedResidualRequired ≡ true

    criticalTemperatureCoincidenceRequiredForSimpleTcLockedHypothesis : Bool
    criticalTemperatureCoincidenceRequiredForSimpleTcLockedHypothesisIsTrue :
      criticalTemperatureCoincidenceRequiredForSimpleTcLockedHypothesis ≡ true

canonicalSourceNormalisationBoundary : SourceNormalisationBoundary
canonicalSourceNormalisationBoundary = source-normalisation-boundary
  false refl
  true refl
  true refl
