module DASHI.Cognition.PNF.KantApperceptionLearningBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as Hyperfabric
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.KantCriticalCompiler as Kant

------------------------------------------------------------------------
-- Unity of apperception as a synthesis index over versioned representations,
-- not a proof of an immortal or substantial soul.
------------------------------------------------------------------------

record SynthesisIndex : Set where
  field
    indexLabel : String
    revisionStable : Bool
    substantialSoulClaimed : Bool
    substantialSoulClaimedIsFalse :
      substantialSoulClaimed ≡ false

record UnifiedRepresentationFamily : Set₁ where
  field
    synthesisIndex : SynthesisIndex
    representations : List PNF.EventPNF
    versionedMemory : Memory.VersionedMemory
    jointlyAttributable : Bool
    temporalOrderingReceipt : String
    everyRepresentationExhaustsSubjectClaimed : Bool

record ApperceptionLearningBridge : Set₁ where
  field
    familyBefore familyAfter : UnifiedRepresentationFamily
    learningReceipt : Learning.LearningReceipt
    sharedSynthesisIndex : String
    beforeIndexMatches :
      SynthesisIndex.indexLabel
        (UnifiedRepresentationFamily.synthesisIndex familyBefore)
      ≡ sharedSynthesisIndex
    afterIndexMatches :
      SynthesisIndex.indexLabel
        (UnifiedRepresentationFamily.synthesisIndex familyAfter)
      ≡ sharedSynthesisIndex
    oldMemoryRetained : Bool
    semanticIdentityMayBeRevalued : Bool
    soulSubstancePromoted : Bool

record ReflectiveLearningCandidate : Set₁ where
  field
    observations : List PNF.EventPNF
    candidateRules : List String
    mode : Kant.JudgmentMode
    modeIsReflective : mode ≡ Kant.reflectiveJudgment
    learningKind : Learning.LearningKind
    promotionClaimed : Bool
    verificationRequired : Bool
    candidateReceipt : String

record KantianHyperfabricAudit : Set₁ where
  field
    left right : PNF.EventPNF
    residual : Residual.ResidualLevel
    interpretiveRoute : Hyperfabric.InterpretiveRoute
    routeAdmissible :
      Hyperfabric.AdmissibleInterpretiveRoute interpretiveRoute
    schemaMissing : Bool
    categoryInappropriate : Bool
    contextInsufficient : Bool
    totalityPresumed : Bool
    crossScopeComparisonAttempted : Bool
    stage8ObstructionCandidate : Trauma.Stage8PNFMemoryObstruction
    materialInherentlyIncoherentClaimed : Bool
    traumaDiagnosed : Bool

record KantApperceptionLearningAuthorityBoundary : Set where
  field
    synthesisIndexDistinctFromSoulObject : Bool
    versionedMemoryCrossPollinated : Bool
    learningMayChangeValuationWithoutChangingIndex : Bool
    reflectiveLearningProducesCandidateOnly : Bool
    failedSynthesisAutomaticallyMeansTrauma : Bool
    failedSynthesisAutomaticallyMeansMaterialIncoherence : Bool
    hyperfabricRouteCreatesClinicalAuthority : Bool
    boundaryNote : String

canonicalKantApperceptionLearningAuthorityBoundary :
  KantApperceptionLearningAuthorityBoundary
canonicalKantApperceptionLearningAuthorityBoundary = record
  { synthesisIndexDistinctFromSoulObject = true
  ; versionedMemoryCrossPollinated = true
  ; learningMayChangeValuationWithoutChangingIndex = true
  ; reflectiveLearningProducesCandidateOnly = true
  ; failedSynthesisAutomaticallyMeansTrauma = false
  ; failedSynthesisAutomaticallyMeansMaterialIncoherence = false
  ; hyperfabricRouteCreatesClinicalAuthority = false
  ; boundaryNote =
      "Apperceptive unity indexes jointly attributable, versioned representations; learning may revalue or reroute them without promoting a soul substance or clinical diagnosis."
  }
