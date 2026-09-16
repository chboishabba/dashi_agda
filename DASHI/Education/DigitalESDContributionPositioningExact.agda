module DASHI.Education.DigitalESDContributionPositioningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Scholarly
import DASHI.Education.DigitalESDReciprocalBraidExact as Braid
import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact as Governance
import DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact as Payment

------------------------------------------------------------------------
-- CONTRIBUTION POSITIONING AGAINST A CLOSE ANTECEDENT
--
-- This is a thin attribution/comparison adapter, not a novelty oracle. Chugh's
-- 2026 sustainability-paradox paper pays a close antecedent for the reverse
-- claim that digital education itself has environmental/social sustainability
-- costs and should be governed with lifecycle/procurement/circularity thinking.
--
-- The adapter records which current manuscript coordinates are not supplied by
-- that one antecedent. It does NOT conclude that those differences are globally
-- novel; that remains contingent on the completed structured search/screening.
------------------------------------------------------------------------

closeAntecedent : Scholarly.Attr.AttributedSource
closeAntecedent = Scholarly.chughSustainabilityParadoxSource

reciprocalFrameworkRetained = Braid.canonicalDigitalESDReciprocalBraid
methodologyRetained = Method.canonicalMethodologyBoundary
governanceTransferRetained = Governance.canonicalParticipantGovernanceContextTransferBoundary
paymentDependencyRetained = Payment.canonicalManuscriptDependencyPaymentBoundary

data ContributionCoordinate : Set where
  reverseSustainabilityParadox : ContributionCoordinate
  reciprocalESDCapacityIntegration : ContributionCoordinate
  adoptionPerformanceTransformationSeparation : ContributionCoordinate
  sourceRoleSameObjectPaymentDiscipline : ContributionCoordinate
  participantAuthorityContextTransfer : ContributionCoordinate
  dependencyAwareSearchSynthesisLineage : ContributionCoordinate

chughPaysCoordinate : ContributionCoordinate → Bool
chughPaysCoordinate reverseSustainabilityParadox = true
chughPaysCoordinate reciprocalESDCapacityIntegration = false
chughPaysCoordinate adoptionPerformanceTransformationSeparation = false
chughPaysCoordinate sourceRoleSameObjectPaymentDiscipline = false
chughPaysCoordinate participantAuthorityContextTransfer = false
chughPaysCoordinate dependencyAwareSearchSynthesisLineage = false

coordinateReference : ContributionCoordinate → String
coordinateReference reverseSustainabilityParadox =
  "digital education creates environmental/social sustainability tensions and should be addressed with lifecycle/procurement/circularity thinking"
coordinateReference reciprocalESDCapacityIntegration =
  "one framework jointly asks how digital education builds ESD capacity and how sustainability constrains digital education itself"
coordinateReference adoptionPerformanceTransformationSeparation =
  "typed separation of technology adoption, task performance/learning and institutional/system transformation"
coordinateReference sourceRoleSameObjectPaymentDiscipline =
  "source role, scope, same-object status and unpaid residuals retained through evidence payment"
coordinateReference participantAuthorityContextTransfer =
  "context-generalisation receipt and same-target-context participant-authority receipt remain conjunctive"
coordinateReference dependencyAwareSearchSynthesisLineage =
  "structured search -> eligible corpus -> source/scope extraction -> synthesis with non-skippable dependency lineage"

------------------------------------------------------------------------
-- Conservative novelty firewalls.
------------------------------------------------------------------------

data CloseAntecedentAutomaticallyMakesDuplicate : Set where
data FormalDifferenceAutomaticallyCreatesPublicationNovelty : Set where
data OneAntecedentExhaustsNoveltySearch : Set where
data CitationCountDeterminesNovelty : Set where

closeAntecedentDoesNotAutomaticallyMakeDuplicate :
  CloseAntecedentAutomaticallyMakesDuplicate → ⊥
closeAntecedentDoesNotAutomaticallyMakeDuplicate ()

formalDifferenceDoesNotAutomaticallyCreatePublicationNovelty :
  FormalDifferenceAutomaticallyCreatesPublicationNovelty → ⊥
formalDifferenceDoesNotAutomaticallyCreatePublicationNovelty ()

oneAntecedentDoesNotExhaustNoveltySearch :
  OneAntecedentExhaustsNoveltySearch → ⊥
oneAntecedentDoesNotExhaustNoveltySearch ()

citationCountDoesNotDetermineNovelty : CitationCountDeterminesNovelty → ⊥
citationCountDoesNotDetermineNovelty ()

record ContributionPositionBoundary : Set where
  constructor contribution-position-boundary
  field
    reverseSustainabilityAntecedentPaid : Bool
    reverseSustainabilityAntecedentPaidIsTrue :
      reverseSustainabilityAntecedentPaid ≡ true

    chughPaysReciprocalESDCapacityIntegration : Bool
    chughPaysReciprocalESDCapacityIntegrationIsFalse :
      chughPaysReciprocalESDCapacityIntegration ≡ false

    chughPaysSameObjectPaymentDiscipline : Bool
    chughPaysSameObjectPaymentDisciplineIsFalse :
      chughPaysSameObjectPaymentDiscipline ≡ false

    chughPaysParticipantAuthorityBoundary : Bool
    chughPaysParticipantAuthorityBoundaryIsFalse :
      chughPaysParticipantAuthorityBoundary ≡ false

    chughPaysDependencyAwareSearchSynthesisLineage : Bool
    chughPaysDependencyAwareSearchSynthesisLineageIsFalse :
      chughPaysDependencyAwareSearchSynthesisLineage ≡ false

    closeAntecedentRetainedAndCited : Bool
    closeAntecedentRetainedAndCitedIsTrue :
      closeAntecedentRetainedAndCited ≡ true

    globalNoveltyClaimPaid : Bool
    globalNoveltyClaimPaidIsFalse : globalNoveltyClaimPaid ≡ false

open ContributionPositionBoundary public

canonicalContributionPositionBoundary : ContributionPositionBoundary
canonicalContributionPositionBoundary =
  contribution-position-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl

contributionPositionReading : String
contributionPositionReading =
  "Chugh (2026) is retained as a close conceptual antecedent for the sustainability-paradox/reverse-direction claim. The current manuscript should therefore avoid claiming novelty for the bare proposition that digital education itself must be sustainable. Its candidate distinctive synthesis instead lies in reciprocal integration with ESD-capacity mechanisms plus explicit adoption/performance/transformation separations, source-role/same-object payment discipline, participant-authority/context-transfer boundaries, and dependency-aware structured-search-to-synthesis lineage. These differences do not themselves establish global publication novelty; that claim remains unpaid until the declared search and positioning work is complete."
