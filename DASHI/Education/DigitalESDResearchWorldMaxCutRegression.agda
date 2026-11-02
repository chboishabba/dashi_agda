module DASHI.Education.DigitalESDResearchWorldMaxCutRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDWorldSourceCoverageCensusExact as Registry
import DASHI.Education.DigitalESDResearchWorldCorpusCensusExact as Census
import DASHI.Education.DigitalESDCrossCorpusIntersectionalMemoryLensExact as Lens
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS
import DASHI.Biology.EducationCorpusSourceRegistry as Alice
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as Invalidation
import DASHI.Biology.AliceBrownSelectiveInvalidationParetoBidiExact as Pareto

-- Registered original/source candidates + separately counted study-profile
-- OCCURRENCES. None of the equalities claim DOI-deduplicated publications.
registeredTwentyFive :
  Registry.length Registry.worldSourceCoverageRows ≡ 25
registeredTwentyFive = Registry.combinedRegistryCount

fourteenPilotProfileOccurrences :
  Registry.length Census.pilotStudyProfiles ≡ 14
fourteenPilotProfileOccurrences = Census.pilotProfileOccurrenceCount

combinedThirtyNineOccurrences :
  Registry.length Census.combinedResearchOccurrences ≡ 39
combinedThirtyNineOccurrences = Census.expandedOccurrenceCount

fiveQuantitativeResultAudits :
  Registry.length Census.resultClaimRows ≡ 5
fiveQuantitativeResultAudits = Census.resultClaimRowCount

eightHeterogeneousPNFAudits :
  Registry.length Census.evidenceClaimRows ≡ 8
eightHeterogeneousPNFAudits = Census.evidenceClaimRowCount

-- Case/source equalities are *typed identities* rather than similarity in
-- author, DOI, principle label or source title.
voiceLensIsExactlyAliceVoice :
  Lens.aliceSource Lens.voiceCollectiveAuthority ≡ Alice.voiceAgencyPaper
voiceLensIsExactlyAliceVoice =
  Lens.aliceSourceIsExact Lens.voiceCollectiveAuthority

voiceLensIsExactlyEcoCOIL :
  Lens.efsSourceCase Lens.voiceCollectiveAuthority ≡ EfS.adefilaEcoCOIL
voiceLensIsExactlyEcoCOIL =
  Lens.efsCaseIsExact Lens.voiceCollectiveAuthority

ecologyLensIsExactlyOriginalDataEcology :
  Lens.aliceSource Lens.dataEcologyMoreThanHuman ≡ Alice.ecologyOfDataPaper
ecologyLensIsExactlyOriginalDataEcology =
  Lens.aliceSourceIsExact Lens.dataEcologyMoreThanHuman

accessibilityLensIsExactlyJepsenCooke :
  Lens.efsSourceCase Lens.aiFeedbackEffectiveAccess ≡ EfS.jepsenCookeAccessibility
accessibilityLensIsExactlyJepsenCooke =
  Lens.efsCaseIsExact Lens.aiFeedbackEffectiveAccess

-- The independent Alice selective invalidation example is preserved:
-- a survey/voice diagnostic update does not automatically dirty an unrelated
-- parent-observer candidate. It is not a demonstrated EfS review event.
aliceUnrelatedObserverStillUnaffected :
  Invalidation.Recursive.candidateClass Invalidation.Recursive.layer1
    (Invalidation.Recursive.liftCandidate Invalidation.aliceDerivedRecursiveStep
      Invalidation.Recursive.frame0)
  ≡ Pareto.Pareto.provablyUnaffected
aliceUnrelatedObserverStillUnaffected =
  Invalidation.aliceParentObserverCandidateStillUnaffected

-- None of the unreviewed source/claim copies are a source admission.
registryCandidateCannotPayReview :
  Registry.RegistryRowImpliesReviewedEvidence → ⊥
registryCandidateCannotPayReview = Registry.registryRowDoesNotProveReview

candidateLensCannotPayReview :
  Lens.CandidateCrossCorpusLensImpliesReviewedHyperedge → ⊥
candidateLensCannotPayReview = Lens.candidateLensNotReviewed

sourceProfileCannotPaySpan :
  Census.StudyProfileImpliesSourceSpanAdmission → ⊥
sourceProfileCannotPaySpan = Census.studyProfileDoesNotAdmitSpan
