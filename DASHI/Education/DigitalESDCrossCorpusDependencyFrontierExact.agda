module DASHI.Education.DigitalESDCrossCorpusDependencyFrontierExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as AliceInvalidation
import DASHI.Core.DependencyDerivedMinimalInvalidationBidiExact as Derived

------------------------------------------------------------------------
-- K04 METHODOLOGICAL dependency frontier, sourced from the existing
-- Alice selective invalidation strategy. This graph declares *candidate
-- interpretation* dependencies, not original author claims or recorded
-- study observations. No reviewed source revision is fabricated.
------------------------------------------------------------------------

data ResearchInterpretationArtifact : Set where
  originalFeedbackSurface : ResearchInterpretationArtifact
  studentVoiceAudit : ResearchInterpretationArtifact
  collectiveEfSAuthorityQuestion : ResearchInterpretationArtifact
  originalDataEcologySurface : ResearchInterpretationArtifact
  ecologicalContextAudit : ResearchInterpretationArtifact
  moreThanHumanEfSQuestion : ResearchInterpretationArtifact

data Depends :
  ResearchInterpretationArtifact → ResearchInterpretationArtifact → Set where
  feedbackCanChangeVoiceAudit :
    Depends originalFeedbackSurface studentVoiceAudit
  voiceCanChangeCollectiveQuestion :
    Depends studentVoiceAudit collectiveEfSAuthorityQuestion
  dataEcologyCanChangeContextAudit :
    Depends originalDataEcologySurface ecologicalContextAudit
  contextCanChangeEcologicalQuestion :
    Depends ecologicalContextAudit moreThanHumanEfSQuestion

feedbackReachesCollectiveQuestion :
  Closure.AffectedClosure
    Depends originalFeedbackSurface collectiveEfSAuthorityQuestion
feedbackReachesCollectiveQuestion =
  Closure.affectedStep feedbackCanChangeVoiceAudit
    (Closure.affectedStep voiceCanChangeCollectiveQuestion
      Closure.affectedRefl)

ecologyReachesMoreThanHumanQuestion :
  Closure.AffectedClosure
    Depends originalDataEcologySurface moreThanHumanEfSQuestion
ecologyReachesMoreThanHumanQuestion =
  Closure.affectedStep dataEcologyCanChangeContextAudit
    (Closure.affectedStep contextCanChangeEcologicalQuestion
      Closure.affectedRefl)

-- Neither source question is reachable from the other isolated candidate
-- dependency strand. This is a finite graph property, NOT evidence that
-- the scientific concepts never interact: an observed new edge must reopen.
collectiveCannotReachEcology :
  Closure.AffectedClosure
    Depends collectiveEfSAuthorityQuestion moreThanHumanEfSQuestion → ⊥
collectiveCannotReachEcology ()

voiceCannotReachEcology :
  Closure.AffectedClosure
    Depends studentVoiceAudit moreThanHumanEfSQuestion → ⊥
voiceCannotReachEcology
  (Closure.affectedStep voiceCanChangeCollectiveQuestion rest) =
    collectiveCannotReachEcology rest

feedbackDoesNotAutomaticallyDirtyEcology :
  Closure.AffectedClosure
    Depends originalFeedbackSurface moreThanHumanEfSQuestion → ⊥
feedbackDoesNotAutomaticallyDirtyEcology
  (Closure.affectedStep feedbackCanChangeVoiceAudit rest) =
    voiceCannotReachEcology rest

-- Actual generic Alice minimal-invalidation evidence remains independently
-- available in the original owner; do not reinterpret this finite example
-- as a completed source-reviewed temporal dependency graph.
originalAliceDerivedDiagnosticReceipt :
  Derived.DerivedInvalidatedAxis
    AliceInvalidation.aliceInvalidationProblem
originalAliceDerivedDiagnosticReceipt =
  AliceInvalidation.aliceDerivedDiagnosticInvalidation
