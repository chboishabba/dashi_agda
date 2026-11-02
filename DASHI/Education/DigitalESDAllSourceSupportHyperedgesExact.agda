module DASHI.Education.DigitalESDAllSourceSupportHyperedgesExact where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.Empty using (⊥)

import DASHI.Biology.EducationCorpusSourceRegistry as Alice
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS
import DASHI.Education.DigitalESDWorldSourceCoverageCensusExact as Registry

------------------------------------------------------------------------
-- Stronger than a documentation crosswalk: for *every* case, preserve the
-- chosen canonical principle row and construct exact proof-bearing membership
-- cells for all ORIGINAL Alice/associates PaperReferences in sourceSupports.
--
-- Each is an attributed, CANDIDATE-ONLY source-genealogy incidence. It is
-- not an original paper claim, effect, source span, reviewed unit or admission.
------------------------------------------------------------------------

canonicalRowFor :
  Digital.TransferablePedagogicalPrinciple → Digital.TransferablePrincipleRow
canonicalRowFor Digital.situatedRelationalEngagement =
  Digital.situatedRelationalEngagementRow
canonicalRowFor Digital.feedbackAsRevisableSignal =
  Digital.feedbackAsRevisableSignalRow
canonicalRowFor Digital.constitutiveLearnerAgency =
  Digital.constitutiveLearnerAgencyRow
canonicalRowFor Digital.adaptiveSupportWithLocalChoice =
  Digital.adaptiveSupportWithLocalChoiceRow
canonicalRowFor Digital.pluralSituatedObservers =
  Digital.pluralSituatedObserversRow
canonicalRowFor Digital.contextualCustodianship =
  Digital.contextualCustodianshipRow
canonicalRowFor Digital.iterativeEvidenceReturnAndRecharting =
  Digital.iterativeEvidenceReturnAndRechartingRow

rowIsExactlyPrinciple :
  (p : Digital.TransferablePedagogicalPrinciple) →
  Digital.principle (canonicalRowFor p) ≡ p
rowIsExactlyPrinciple Digital.situatedRelationalEngagement = refl
rowIsExactlyPrinciple Digital.feedbackAsRevisableSignal = refl
rowIsExactlyPrinciple Digital.constitutiveLearnerAgency = refl
rowIsExactlyPrinciple Digital.adaptiveSupportWithLocalChoice = refl
rowIsExactlyPrinciple Digital.pluralSituatedObservers = refl
rowIsExactlyPrinciple Digital.contextualCustodianship = refl
rowIsExactlyPrinciple Digital.iterativeEvidenceReturnAndRecharting = refl

rowSourceIsBound :
  (p : Digital.TransferablePedagogicalPrinciple) →
  Digital.sourceBound (canonicalRowFor p) ≡ true
rowSourceIsBound Digital.situatedRelationalEngagement = refl
rowSourceIsBound Digital.feedbackAsRevisableSignal = refl
rowSourceIsBound Digital.constitutiveLearnerAgency = refl
rowSourceIsBound Digital.adaptiveSupportWithLocalChoice = refl
rowSourceIsBound Digital.pluralSituatedObservers = refl
rowSourceIsBound Digital.contextualCustodianship = refl
rowSourceIsBound Digital.iterativeEvidenceReturnAndRecharting = refl

rowStillCandidate :
  (p : Digital.TransferablePedagogicalPrinciple) →
  Digital.candidateOnly (canonicalRowFor p) ≡ true
rowStillCandidate Digital.situatedRelationalEngagement = refl
rowStillCandidate Digital.feedbackAsRevisableSignal = refl
rowStillCandidate Digital.constitutiveLearnerAgency = refl
rowStillCandidate Digital.adaptiveSupportWithLocalChoice = refl
rowStillCandidate Digital.pluralSituatedObservers = refl
rowStillCandidate Digital.contextualCustodianship = refl
rowStillCandidate Digital.iterativeEvidenceReturnAndRecharting = refl

principleOf :
  EfS.CrossPollinationCase → Digital.TransferablePedagogicalPrinciple
principleOf c =
  Prior.ReciprocalPedagogicalBridge.digitalPrinciple (EfS.candidateBridge c)

record CasePrincipleGenealogy (case : EfS.CrossPollinationCase) : Set where
  constructor case-principle-genealogy
  field
    canonicalRow : Digital.TransferablePrincipleRow
    rowEqualsExactCasePrinciple :
      Digital.principle canonicalRow ≡ principleOf case
    originalSupports : List Alice.PaperReference
    originalSupportsAreRow :
      originalSupports ≡ Digital.sourceSupports canonicalRow
    supportIsSourceBound : Digital.sourceBound canonicalRow ≡ true
    supportIsCandidateOnly : Digital.candidateOnly canonicalRow ≡ true
    efSLocatorRetained :
      Prior.EfSSource.exactLocator
        (Prior.ReciprocalPedagogicalBridge.source (EfS.candidateBridge case))
        ≡ Attr.canonicalURL (EfS.attributedSource case)

casePrincipleGenealogy :
  (c : EfS.CrossPollinationCase) → CasePrincipleGenealogy c
casePrincipleGenealogy c =
  case-principle-genealogy
    (canonicalRowFor (principleOf c))
    (rowIsExactlyPrinciple (principleOf c))
    (Digital.sourceSupports (canonicalRowFor (principleOf c)))
    refl
    (rowSourceIsBound (principleOf c))
    (rowStillCandidate (principleOf c))
    (EfS.sameLocator c)

-- Avoid paper-key or title string matching: a dependent witness says the
-- exact PaperReference is an element of the exact existing support list.
data AppearsIn (paper : Alice.PaperReference) :
  List Alice.PaperReference → Set where
  here : ∀ {tail} → AppearsIn paper (paper ∷ tail)
  there : ∀ {head tail} →
    AppearsIn paper tail → AppearsIn paper (head ∷ tail)

record ListedOriginalSupport (list : List Alice.PaperReference) : Set where
  constructor listed-original-support
  field
    paper : Alice.PaperReference
    membership : AppearsIn paper list

open ListedOriginalSupport public

enumerateOriginalSupports :
  (xs : List Alice.PaperReference) → List (ListedOriginalSupport xs)
enumerateOriginalSupports [] = []
enumerateOriginalSupports (x ∷ xs) =
  listed-original-support x here
    ∷ Registry.map
        (λ support →
          listed-original-support
            (paper support)
            (there (membership support)))
        (enumerateOriginalSupports xs)

record CaseSourceIncidence (case : EfS.CrossPollinationCase) : Set where
  constructor case-source-incidence
  field
    originalPaper : Alice.PaperReference
    originalPaperAppearsInCanonicalRow :
      AppearsIn originalPaper
        (Digital.sourceSupports (canonicalRowFor (principleOf case)))

open CaseSourceIncidence public

caseSourceIncidences :
  (c : EfS.CrossPollinationCase) → List (CaseSourceIncidence c)
caseSourceIncidences c =
  Registry.map
    (λ support →
      case-source-incidence (paper support) (membership support))
    (enumerateOriginalSupports
      (Digital.sourceSupports (canonicalRowFor (principleOf c))))

record CaseWithItsOriginalSources : Set where
  constructor case-with-its-original-sources
  field
    case : EfS.CrossPollinationCase
    originalGenealogy : CasePrincipleGenealogy case
    allSourceIncidences : List (CaseSourceIncidence case)
    casesHaveExactSupportCells :
      allSourceIncidences ≡ caseSourceIncidences case

caseWithOriginalSources : EfS.CrossPollinationCase → CaseWithItsOriginalSources
caseWithOriginalSources c =
  case-with-its-original-sources
    c
    (casePrincipleGenealogy c)
    (caseSourceIncidences c)
    refl

allSixteenSourceGenealogies : List CaseWithItsOriginalSources
allSixteenSourceGenealogies =
  Registry.map caseWithOriginalSources EfS.canonicalSourceCases

allSixteenCasesRetained :
  Registry.length allSixteenSourceGenealogies ≡ 16
allSixteenCasesRetained = refl

sum : List Nat → Nat
sum [] = zero
sum (n ∷ ns) = n + sum ns

allSourceIncidenceCount : Nat
allSourceIncidenceCount =
  sum (Registry.map
    (λ c → Registry.length (caseSourceIncidences c))
    EfS.canonicalSourceCases)

sourceGenealogyIncidencesAreFiftyFive :
  allSourceIncidenceCount ≡ 55
sourceGenealogyIncidencesAreFiftyFive = refl

-- No original author is credited with the later EfS source-join inference.
-- Actual per-claim source spans and independent reviews are still separate.
data CanonicalSourceSupportEqualsReviewedEvidence : Set where
data FiftyFivePathsEqualFiftyFiveEmpiricalStudies : Set where

sourceSupportNotReviewed :
  CanonicalSourceSupportEqualsReviewedEvidence → ⊥
sourceSupportNotReviewed ()

genealogyPathsNotEmpiricalStudyCounts :
  FiftyFivePathsEqualFiftyFiveEmpiricalStudies → ⊥
genealogyPathsNotEmpiricalStudyCounts ()
