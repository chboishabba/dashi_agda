module DASHI.Governance.FormalisationGovernanceCapstoneExact where

------------------------------------------------------------------------
-- THREE-STOREY FORMALISATION GOVERNANCE CAPSTONE
--
-- LEVEL 0: material/social relation -> affordance -> capability -> functioning
-- LEVEL 1: observer/recognition/valuation/representation -> authority -> repair
-- LEVEL 2: source -> interpretation -> formal theorem -> scoped claim -> residual
--
-- "Capstone" here means regression composition only. It does not mean semantic
-- exhaustiveness; see KernelSemanticClosureBoundaryExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RelationalAffordanceCoreExact as Affordance
import DASHI.Core.PlumwoodMasterModelOperationFamilyExact as Plumwood
import DASHI.Core.McCallCategoryStrategyBoundaryExact as McCall
import DASHI.Core.ButlerPerformativeGenesisNonDescentExact as Butler
import DASHI.Core.InterpretiveFormalisationCoreExact as Formalisation
import DASHI.Core.VocabularyProvenanceExact as Vocabulary
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.Core.FormalisationAbuseLintExact as Lint
import DASHI.Core.FormalisationCompatibilityExact as Compatibility
import DASHI.Core.KernelSemanticClosureBoundaryExact as Closure
import DASHI.Core.FormalisationGovernanceSourceRegistryExact as Sources
import DASHI.Governance.CapabilityFunctioningNonDescentExact as Capability
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Governance.AuthorityRepairLegitimacySeparationExact as Repair

------------------------------------------------------------------------
-- Live non-collapse theorems.
------------------------------------------------------------------------

functioningDoesNotRecoverCapability :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Capability.functioning Capability.capabilitySignature → ⊥
functioningDoesNotRecoverCapability = Capability.functioningCannotRecoverCapability

capabilityDoesNotRecoverFunctioning :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Capability.capabilitySignature Capability.functioning → ⊥
capabilityDoesNotRecoverFunctioning = Capability.capabilityCannotRecoverFunctioning

recognitionDoesNotRecoverDistribution :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Fraser.recognition Fraser.distribution → ⊥
recognitionDoesNotRecoverDistribution = Fraser.recognitionCannotRecoverDistribution

distributionDoesNotRecoverRepresentation :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Fraser.distribution Fraser.representation → ⊥
distributionDoesNotRecoverRepresentation = Fraser.distributionCannotRecoverRepresentation

presentCategoryDoesNotRecoverGenesis :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Butler.presentCategory Butler.genesis → ⊥
presentCategoryDoesNotRecoverGenesis = Butler.presentCategoryCannotRecoverGenesis

scopedModificationDoesNotGuaranteeEffect :
  Repair.CanModify Repair.scopedButIneffective →
  Repair.Effective Repair.scopedButIneffective → ⊥
scopedModificationDoesNotGuaranteeEffect = Repair.canModifyDoesNotGuaranteeEffect

methodologicalTensionIsAdmissibleInformation :
  Compatibility.FormalisationCompatibility
methodologicalTensionIsAdmissibleInformation = Compatibility.methodologicalTension

kernelClosureIsNotSemanticExhaustiveness :
  Closure.semanticallyExhaustive Closure.criticalCapstoneStatus ≡ false
kernelClosureIsNotSemanticExhaustiveness = Closure.criticalCapstoneNotSemanticallyExhaustive

formalisationLintIsClean : Lint.CleanFormalisationLint Lint.canonicalRisk
formalisationLintIsClean = Lint.canonicalCleanLint

record ThreeStoreyBoundary : Set where
  constructor three-storey-boundary
  field
    affordanceEqualsFunctioning : Bool
    affordanceEqualsFunctioningIsFalse : affordanceEqualsFunctioning ≡ false
    recognitionEqualsDistribution : Bool
    recognitionEqualsDistributionIsFalse : recognitionEqualsDistribution ≡ false
    authorityEqualsEfficacy : Bool
    authorityEqualsEfficacyIsFalse : authorityEqualsEfficacy ≡ false
    efficacyEqualsLegitimacy : Bool
    efficacyEqualsLegitimacyIsFalse : efficacyEqualsLegitimacy ≡ false
    categoryEqualsGenesis : Bool
    categoryEqualsGenesisIsFalse : categoryEqualsGenesis ≡ false
    formalTheoremEqualsSourceMeaning : Bool
    formalTheoremEqualsSourceMeaningIsFalse : formalTheoremEqualsSourceMeaning ≡ false
    kernelClosureEqualsSemanticClosure : Bool
    kernelClosureEqualsSemanticClosureIsFalse : kernelClosureEqualsSemanticClosure ≡ false
    formalVocabularyTransfersEpistemicOwnership : Bool
    formalVocabularyTransfersEpistemicOwnershipIsFalse :
      formalVocabularyTransfersEpistemicOwnership ≡ false

canonicalThreeStoreyBoundary : ThreeStoreyBoundary
canonicalThreeStoreyBoundary =
  three-storey-boundary
    false refl false refl false refl false refl
    false refl false refl false refl false refl
