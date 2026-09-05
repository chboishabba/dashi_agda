module DASHI.Core.TechnicalExternalisationDepthBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.OpenScienceKnowledgeReleaseBidiExact as O
import DASHI.Core.CriticalKnowledgeConcentrationBidiExact as K

------------------------------------------------------------------------
-- TECHNICAL EXTERNALISATION DEPTH
--
-- Publication is a weak binary feature.  This object measures how much of the
-- technical reasoning/implementation chain is deliberately made inspectable.
------------------------------------------------------------------------

data ExternalisationStage : Set where
  problemStatement
  physicalOrTechnicalModel
  algorithmOrDesignMethod
  implementationArchitecture
  benchmarkOrValidation
  failureModeOrLimitations
  dataOrSourceArtifact
  publicInterpretation
  : ExternalisationStage

record TechnicalExternalisationProfile : Set where
  constructor technical-externalisation-profile
  field
    personOrWork : String
    stages : List ExternalisationStage
    sourceReference : String
    boundedReading : String

open TechnicalExternalisationProfile public

record DeepExternalisation (profile : TechnicalExternalisationProfile) : Set where
  constructor deep-externalisation
  field
    modelExposed : ListMembership physicalOrTechnicalModel (stages profile)
    methodExposed : ListMembership algorithmOrDesignMethod (stages profile)
    validationExposed : ListMembership benchmarkOrValidation (stages profile)
    depthReference : String

open DeepExternalisation public

------------------------------------------------------------------------
-- Cross-pollination boundaries.
------------------------------------------------------------------------

record ExternalisationBoundary : Set where
  constructor externalisation-boundary
  field
    publicationAloneMeansDeepExternalisation : Bool
    publicationAloneMeansDeepExternalisationIsFalse :
      publicationAloneMeansDeepExternalisation ≡ false
    deepExternalisationMeansSourceCodeRelease : Bool
    deepExternalisationMeansSourceCodeReleaseIsFalse :
      deepExternalisationMeansSourceCodeRelease ≡ false
    deepExternalisationMeansAntiSecrecyBelief : Bool
    deepExternalisationMeansAntiSecrecyBeliefIsFalse :
      deepExternalisationMeansAntiSecrecyBelief ≡ false
    deepExternalisationMeansNoTacitKnowledgeRemains : Bool
    deepExternalisationMeansNoTacitKnowledgeRemainsIsFalse :
      deepExternalisationMeansNoTacitKnowledgeRemains ≡ false
    deepExternalisationCanBeMatchedControlFeature : Bool
    deepExternalisationCanBeMatchedControlFeatureIsTrue :
      deepExternalisationCanBeMatchedControlFeature ≡ true

canonicalExternalisationBoundary : ExternalisationBoundary
canonicalExternalisationBoundary = externalisation-boundary
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Reverse acquisition: if a roster is claimed to be selected for externalising
-- too much, require stage-specific evidence and controls.
------------------------------------------------------------------------

data ExternalisationAcquisitionTarget : Set where
  stageReceipt
  artifactReceipt
  limitationOrFailureReceipt
  matchedExternalisationControls
  observerOfExternalisationDepth
  : ExternalisationAcquisitionTarget

record ExternalisationReverseObligation : Set where
  constructor externalisation-reverse-obligation
  field
    personOrWork : String
    target : ExternalisationAcquisitionTarget
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open ExternalisationReverseObligation public
