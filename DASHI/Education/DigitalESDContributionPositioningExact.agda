module DASHI.Education.DigitalESDContributionPositioningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Scholarly
import DASHI.Education.DigitalESDReciprocalBraidExact as Braid
import DASHI.Education.DigitalESDManuscriptMethodologyExact as Method
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact as Governance
import DASHI.Education.DigitalESDManuscriptDependencyPaymentAdapterExact as Payment

------------------------------------------------------------------------
-- CONTRIBUTION POSITIONING AGAINST CLOSE ANTECEDENTS
--
-- This is a thin attribution/comparison adapter, not a novelty oracle.
-- Chugh pays the reverse sustainability-paradox antecedent. Böhme pays a still
-- closer conceptual antecedent for mutually coupled sustainability/digitality
-- as a twin transformation in education. These findings contract the candidate
-- contribution rather than being ignored or treated as proof of duplication.
------------------------------------------------------------------------

reverseSustainabilityAntecedent : Attr.AttributedSource
reverseSustainabilityAntecedent = Scholarly.chughSustainabilityParadoxSource

twinTransformationAntecedent : Attr.AttributedSource
twinTransformationAntecedent = Scholarly.boehmeDigitainabilitySource

closeAntecedents : List Attr.AttributedSource
closeAntecedents = reverseSustainabilityAntecedent ∷ twinTransformationAntecedent ∷ []

reciprocalFrameworkRetained = Braid.canonicalDigitalESDReciprocalBraid
methodologyRetained = Method.canonicalMethodologyBoundary
governanceTransferRetained = Governance.canonicalParticipantGovernanceContextTransferBoundary
paymentDependencyRetained = Payment.canonicalManuscriptDependencyPaymentBoundary

data ContributionCoordinate : Set where
  reverseSustainabilityParadox : ContributionCoordinate
  twinTransformationIntegration : ContributionCoordinate
  adoptionPerformanceTransformationSeparation : ContributionCoordinate
  sourceRoleSameObjectPaymentDiscipline : ContributionCoordinate
  participantAuthorityContextTransfer : ContributionCoordinate
  dependencyAwareSearchSynthesisLineage : ContributionCoordinate

chughPaysCoordinate : ContributionCoordinate → Bool
chughPaysCoordinate reverseSustainabilityParadox = true
chughPaysCoordinate twinTransformationIntegration = false
chughPaysCoordinate adoptionPerformanceTransformationSeparation = false
chughPaysCoordinate sourceRoleSameObjectPaymentDiscipline = false
chughPaysCoordinate participantAuthorityContextTransfer = false
chughPaysCoordinate dependencyAwareSearchSynthesisLineage = false

boehmePaysCoordinate : ContributionCoordinate → Bool
boehmePaysCoordinate reverseSustainabilityParadox = false
boehmePaysCoordinate twinTransformationIntegration = true
boehmePaysCoordinate adoptionPerformanceTransformationSeparation = false
boehmePaysCoordinate sourceRoleSameObjectPaymentDiscipline = false
boehmePaysCoordinate participantAuthorityContextTransfer = false
boehmePaysCoordinate dependencyAwareSearchSynthesisLineage = false

coordinateReference : ContributionCoordinate → String
coordinateReference reverseSustainabilityParadox =
  "digital education creates environmental/social sustainability tensions and should be addressed with lifecycle/procurement/circularity thinking"
coordinateReference twinTransformationIntegration =
  "sustainability/ESD and digitality are treated as mutually coupled educational transformations rather than adjacent agendas"
coordinateReference adoptionPerformanceTransformationSeparation =
  "typed separation of technology adoption, implementation activity, input integration, task performance/learning and institutional/system transformation"
coordinateReference sourceRoleSameObjectPaymentDiscipline =
  "source role, scope, same-object status and unpaid residuals retained through evidence payment"
coordinateReference participantAuthorityContextTransfer =
  "context-generalisation receipt and same-target-context participant-authority receipt remain conjunctive"
coordinateReference dependencyAwareSearchSynthesisLineage =
  "structured search -> eligible corpus -> source/scope extraction -> synthesis with non-skippable dependency lineage"

data CloseAntecedentAutomaticallyMakesDuplicate : Set where
data FormalDifferenceAutomaticallyCreatesPublicationNovelty : Set where
data OneAntecedentExhaustsNoveltySearch : Set where
data CitationCountDeterminesNovelty : Set where

data TwinTransformationAntecedentLeavesNoDistinctEvidenceArchitecture : Set where

closeAntecedentDoesNotAutomaticallyMakeDuplicate : CloseAntecedentAutomaticallyMakesDuplicate → ⊥
closeAntecedentDoesNotAutomaticallyMakeDuplicate ()

formalDifferenceDoesNotAutomaticallyCreatePublicationNovelty : FormalDifferenceAutomaticallyCreatesPublicationNovelty → ⊥
formalDifferenceDoesNotAutomaticallyCreatePublicationNovelty ()

oneAntecedentDoesNotExhaustNoveltySearch : OneAntecedentExhaustsNoveltySearch → ⊥
oneAntecedentDoesNotExhaustNoveltySearch ()

citationCountDoesNotDetermineNovelty : CitationCountDeterminesNovelty → ⊥
citationCountDoesNotDetermineNovelty ()

twinTransformationAntecedentDoesNotEraseEvidenceArchitecture :
  TwinTransformationAntecedentLeavesNoDistinctEvidenceArchitecture → ⊥
twinTransformationAntecedentDoesNotEraseEvidenceArchitecture ()

record ContributionPositionBoundary : Set where
  constructor contribution-position-boundary
  field
    reverseSustainabilityAntecedentPaid : Bool
    reverseSustainabilityAntecedentPaidIsTrue : reverseSustainabilityAntecedentPaid ≡ true

    twinTransformationAntecedentPaid : Bool
    twinTransformationAntecedentPaidIsTrue : twinTransformationAntecedentPaid ≡ true

    chughPaysReciprocalESDCapacityIntegration : Bool
    chughPaysReciprocalESDCapacityIntegrationIsFalse : chughPaysReciprocalESDCapacityIntegration ≡ false

    boehmePaysTwinTransformationIntegration : Bool
    boehmePaysTwinTransformationIntegrationIsTrue : boehmePaysTwinTransformationIntegration ≡ true

    boehmePaysSameObjectPaymentDiscipline : Bool
    boehmePaysSameObjectPaymentDisciplineIsFalse : boehmePaysSameObjectPaymentDiscipline ≡ false

    closeAntecedentsPayParticipantAuthorityBoundary : Bool
    closeAntecedentsPayParticipantAuthorityBoundaryIsFalse : closeAntecedentsPayParticipantAuthorityBoundary ≡ false

    closeAntecedentsPayDependencyAwareSearchSynthesisLineage : Bool
    closeAntecedentsPayDependencyAwareSearchSynthesisLineageIsFalse : closeAntecedentsPayDependencyAwareSearchSynthesisLineage ≡ false

    closeAntecedentsRetainedAndCited : Bool
    closeAntecedentsRetainedAndCitedIsTrue : closeAntecedentsRetainedAndCited ≡ true

    globalNoveltyClaimPaid : Bool
    globalNoveltyClaimPaidIsFalse : globalNoveltyClaimPaid ≡ false

open ContributionPositionBoundary public

canonicalContributionPositionBoundary : ContributionPositionBoundary
canonicalContributionPositionBoundary = contribution-position-boundary
  true refl
  true refl
  false refl
  true refl
  false refl
  false refl
  false refl
  true refl
  false refl

contributionPositionReading : String
contributionPositionReading =
  "Two close 2026 antecedents materially contract the candidate contribution. Chugh pays the sustainability-paradox/reverse-sustainability premise; Böhme's Digitainability Framework pays a mutually coupled sustainability/digitality twin-transformation premise in education. The manuscript should therefore claim neither of those ideas as novel in the bare form. Its remaining candidate distinction lies in the evidence architecture: explicit adoption/activity/input/performance/learning/transformation separations, source-role and same-object payment discipline, participant-authority/context-transfer obligations, lifecycle method-versus-deployment residuals, and dependency-aware structured-search-to-synthesis lineage. Those differences still do not establish global publication novelty; that remains unpaid until the declared search and positioning work is complete."
