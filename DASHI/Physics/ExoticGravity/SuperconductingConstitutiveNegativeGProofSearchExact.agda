module DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as Weld
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeProofSearchExact as ScopeSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CONSTITUTIVE NEGATIVE-G PROOF SEARCH
--
-- Reuse the existing enhancement router first.  A negative-effective-G
-- interpretation is downstream of source/geometry/background/eta_C closure,
-- never a shortcut around those coordinates.
------------------------------------------------------------------------

data ConstitutiveNegativeGStage : Set where
  sourceCurrentStage : ConstitutiveNegativeGStage
  sourceStressEnergyStage : ConstitutiveNegativeGStage
  geometryStage : ConstitutiveNegativeGStage
  phaseMatchedFieldStage : ConstitutiveNegativeGStage
  backgroundClosureStage : ConstitutiveNegativeGStage
  constitutiveRatioStage : ConstitutiveNegativeGStage
  coefficientSignStage : ConstitutiveNegativeGStage
  materialScopeStage : ConstitutiveNegativeGStage
  sameApparatusRegimeContrastStage : ConstitutiveNegativeGStage
  constitutiveNegativeGInterpretationStage : ConstitutiveNegativeGStage

stageForEnhancementLeaf : Split.EnhancementLeaf → ConstitutiveNegativeGStage
stageForEnhancementLeaf Split.sourceCurrentLeaf = sourceCurrentStage
stageForEnhancementLeaf Split.sourceStressEnergyLeaf = sourceStressEnergyStage
stageForEnhancementLeaf Split.geometryLeaf = geometryStage
stageForEnhancementLeaf Split.phaseMatchedFieldLeaf = phaseMatchedFieldStage
stageForEnhancementLeaf Split.backgroundClosureLeaf = backgroundClosureStage
stageForEnhancementLeaf Split.constitutiveRatioLeaf = constitutiveRatioStage
stageForEnhancementLeaf Split.closedEnhancementSplit = coefficientSignStage

firstStageForEnhancementState : Split.EnhancementClosureState → ConstitutiveNegativeGStage
firstStageForEnhancementState state =
  stageForEnhancementLeaf (Split.firstOpenEnhancementLeaf state)

currentConstitutiveNegativeGStage : ConstitutiveNegativeGStage
currentConstitutiveNegativeGStage =
  firstStageForEnhancementState Split.currentEnhancementFrontier

currentStageIsSourceCurrent :
  currentConstitutiveNegativeGStage ≡ sourceCurrentStage
currentStageIsSourceCurrent = refl

producerForStage : ConstitutiveNegativeGStage → Search.ProducerClass
producerForStage sourceCurrentStage = Search.empiricalEvidenceProducer
producerForStage sourceStressEnergyStage = Search.empiricalEvidenceProducer
producerForStage geometryStage = Search.identityProducer
producerForStage phaseMatchedFieldStage = Search.discriminatorProducer
producerForStage backgroundClosureStage = Search.empiricalEvidenceProducer
producerForStage constitutiveRatioStage = Search.discriminatorProducer
producerForStage coefficientSignStage = Search.discriminatorProducer
producerForStage materialScopeStage = Search.identityProducer
producerForStage sameApparatusRegimeContrastStage = Search.discriminatorProducer
producerForStage constitutiveNegativeGInterpretationStage = Search.contradictionProducer

------------------------------------------------------------------------
-- Post-enhancement gate.  Even after the older enhancement split is closed,
-- coefficient sign, scope, and regime contrast remain separate obligations.
------------------------------------------------------------------------

record PostEnhancementNegativeGGate : Set₁ where
  constructor post-enhancement-negative-g-gate
  field
    enhancementState : Split.EnhancementClosureState
    enhancementIsClosed :
      Split.firstOpenEnhancementLeaf enhancementState ≡ Split.closedEnhancementSplit

    coefficientSignReceipt : Weld.ConstitutiveNegativeGReceipt

    materialScopeSearchStage : ScopeSearch.ScopeSearchStage
    scopeStageIsMaterialContrast :
      materialScopeSearchStage ≡ ScopeSearch.materialSameApparatusRegimeContrast

    SameApparatusRegimeContrastReceipt : Set
    sameApparatusRegimeContrastReceipt : SameApparatusRegimeContrastReceipt

open PostEnhancementNegativeGGate public

record ConstitutiveNegativeGProofSearchBoundary : Set where
  constructor constitutive-negative-g-proof-search-boundary
  field
    negativeGInterpretationMaySkipSourceCurrent : Bool
    currentFirstStageIsSourceCurrent : Bool
    closedEnhancementSplitAutomaticallyMeansNegativeEffectiveG : Bool
    coefficientSignStillRequiredAfterEnhancementClosure : Bool
    materialScopeStillRequiredAfterEnhancementClosure : Bool
    sameApparatusRegimeContrastStillRequired : Bool
    interpretationIsDownstreamOfEtaC : Bool

canonicalConstitutiveNegativeGProofSearchBoundary :
  ConstitutiveNegativeGProofSearchBoundary
canonicalConstitutiveNegativeGProofSearchBoundary =
  constitutive-negative-g-proof-search-boundary
    false true false true true true true
