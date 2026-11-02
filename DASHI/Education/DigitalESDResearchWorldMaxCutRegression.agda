module DASHI.Education.DigitalESDResearchWorldMaxCutRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDWorldSourceCoverageCensusExact as Registry
import DASHI.Education.DigitalESDResearchWorldCorpusCensusExact as Census
import DASHI.Education.DigitalESDAllSourceSupportHyperedgesExact as Genealogy
import DASHI.Education.DigitalESDCrossCorpusIntersectionalMemoryLensExact as Lens
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS
import DASHI.Biology.EducationCorpusSourceRegistry as Alice
import DASHI.Biology.HyperfabricIntersectionalBodyMemoryBridge as BodyMemory
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as Invalidation
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

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

allSixteenGenealogiesActuallyGenerated :
  Registry.length Genealogy.allSixteenSourceGenealogies ≡ 16
allSixteenGenealogiesActuallyGenerated =
  Genealogy.allSixteenCasesRetained

originalSourceSupportIncidencesFiftyFive :
  Genealogy.allSourceIncidenceCount ≡ 55
originalSourceSupportIncidencesFiftyFive =
  Genealogy.sourceGenealogyIncidencesAreFiftyFive

ecoCOILOriginalSupportsAreThree :
  Registry.length (Genealogy.caseSourceIncidences EfS.adefilaEcoCOIL) ≡ 3
ecoCOILOriginalSupportsAreThree = refl

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

bodyMemoryRetainsExistingCanonicalHyperfabric :
  Lens.bodyMemoryHyperfabric Lens.voiceCollectiveAuthority ≡
    BodyMemory.canonicalHyperfabricIntersectionalBodyMemoryBridge
bodyMemoryRetainsExistingCanonicalHyperfabric =
  Lens.bodyMemoryIsCanonical Lens.voiceCollectiveAuthority

-- The 1500-line original body-memory certificate is reused, not reconstructed.
bodyMemoryCertificateRemainsCandidate :
  BodyMemory.HyperfabricIntersectionalBodyMemoryCertificate
    (Lens.bodyMemoryHyperfabric Lens.voiceCollectiveAuthority)
bodyMemoryCertificateRemainsCandidate =
  Lens.bodyMemorySourceCertificate Lens.voiceCollectiveAuthority

-- The independent Alice selective invalidation example is preserved:
-- a survey/voice diagnostic update does not automatically dirty an unrelated
-- parent-observer candidate. It is not a demonstrated EfS review event.
aliceUnrelatedObserverStillUnaffected :
  Recursive.candidateClass Recursive.layer1
    (Recursive.liftCandidate Invalidation.aliceDerivedRecursiveStep
      Recursive.frame0)
  ≡ Pareto.provablyUnaffected
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
