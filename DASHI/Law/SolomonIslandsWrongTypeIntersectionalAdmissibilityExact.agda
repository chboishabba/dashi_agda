module DASHI.Law.SolomonIslandsWrongTypeIntersectionalAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Applicability
import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Law.SolomonIslandsDomesticLegalCoverageExact as Coverage
import DASHI.Law.SolomonIslandsLeadershipCodeElementFitExact as Leadership

------------------------------------------------------------------------
-- SOLOMON ISLANDS: LEGAL ATTRIBUTION -> WRONGTYPE -> NONFACTORABILITY ->
-- APPLICABILITY ADMISSION
--
-- This is the missing weld.  The section-level authority objects remain the
-- source owners.  WrongType carries the source/system/protected-interest shape.
-- IntersectionalNonFactorability proves that a coarse `funding happened`
-- observer cannot determine element fit.  The existing SensibLaw applicability
-- status remains the admission owner: reported/alleged facts are candidate use,
-- not admitted applicability.
------------------------------------------------------------------------

solomonSystemId : Ontology.StableId
solomonSystemId = Ontology.stableId "SB.LEGAL"

antiCorruption92SourceId : Ontology.StableId
antiCorruption92SourceId = Ontology.stableId "SB.ANTI-CORRUPTION-2018.s92"

leadership17SourceId : Ontology.StableId
leadership17SourceId = Ontology.stableId "SB.LEADERSHIP-CODE-1999.s17"

parliamentaryIntegrityInterestId : Ontology.StableId
parliamentaryIntegrityInterestId = Ontology.stableId "interest:SB:parliamentary-integrity"

publicOfficialActorConstraintId : Ontology.StableId
publicOfficialActorConstraintId = Ontology.stableId "actor-constraint:SB:public-official"

leaderActorConstraintId : Ontology.StableId
leaderActorConstraintId = Ontology.stableId "actor-constraint:SB:leader"

benefitInfluenceRelationshipConstraintId : Ontology.StableId
benefitInfluenceRelationshipConstraintId = Ontology.stableId "relation-constraint:benefit-influence-official-duty"

antiCorruptionSection92WrongType : Ontology.WrongType
antiCorruptionSection92WrongType = Ontology.wrongTypeRecord
  (Ontology.stableId "wrong:SB:anti-corruption:s92")
  solomonSystemId
  (antiCorruption92SourceId ∷ [])
  (parliamentaryIntegrityInterestId ∷ [])
  (publicOfficialActorConstraintId ∷ [])
  (benefitInfluenceRelationshipConstraintId ∷ [])
  Ontology.intentional
  []
  []
  []

leadershipSection17WrongType : Ontology.WrongType
leadershipSection17WrongType = Ontology.wrongTypeRecord
  (Ontology.stableId "wrong:SB:leadership-code:s17")
  solomonSystemId
  (leadership17SourceId ∷ [])
  (parliamentaryIntegrityInterestId ∷ [])
  (leaderActorConstraintId ∷ [])
  (benefitInfluenceRelationshipConstraintId ∷ [])
  Ontology.intentional
  []
  []
  []

------------------------------------------------------------------------
-- Exact legal-attribution welds.
------------------------------------------------------------------------

record LegalCitationWrongTypeWeld
    (citation : Legal.LegalCitation)
    (wrong : Ontology.WrongType) : Set where
  constructor legal-citation-wrong-type-weld
  field
    sourceId : Ontology.StableId
    sourceReference : String
    sameJurisdiction : String
    authorityUseReviewed : Bool
    authorityUseReviewedIsTrue : authorityUseReviewed ≡ true
    citationDoesNotPayElements : Bool
    citationDoesNotPayElementsIsFalse : citationDoesNotPayElements ≡ false

open LegalCitationWrongTypeWeld public

antiCorruption92Weld :
  LegalCitationWrongTypeWeld Coverage.antiCorruptionBriberyPublicOfficial antiCorruptionSection92WrongType
antiCorruption92Weld = legal-citation-wrong-type-weld
  antiCorruption92SourceId
  "Anti-Corruption Act 2018 s 92(1)-(2), section-level authority and consumer-use receipt"
  "Solomon Islands"
  true refl
  false refl

leadership17Weld :
  LegalCitationWrongTypeWeld Leadership.leadershipCodeSection17Bribery leadershipSection17WrongType
leadership17Weld = legal-citation-wrong-type-weld
  leadership17SourceId
  "Leadership Code (Further Provisions) Act 1999 s 17(1)-(3), section-level authority and consumer-use receipt"
  "Solomon Islands"
  true refl
  false refl

------------------------------------------------------------------------
-- Intersectional/non-factorability witness.
--
-- Same coarse funding observation, opposite legal-element fit.  Therefore the
-- WrongType outcome cannot factor through the one-axis `funding exists` view.
------------------------------------------------------------------------

data SituatedFundingState : Set where
  publicFundingNoInfluenceNexus : SituatedFundingState
  sameFundingWithInfluenceNexus : SituatedFundingState


data FundingObserved : Set where
  fundingReported : FundingObserved

fundingOnlyObserver : SituatedFundingState → FundingObserved
fundingOnlyObserver publicFundingNoInfluenceNexus = fundingReported
fundingOnlyObserver sameFundingWithInfluenceNexus = fundingReported

s92ElementFit : SituatedFundingState → Bool
s92ElementFit publicFundingNoInfluenceNexus = false
s92ElementFit sameFundingWithInfluenceNexus = true

s92FitDiffers :
  s92ElementFit publicFundingNoInfluenceNexus ≡
  s92ElementFit sameFundingWithInfluenceNexus → ⊥
s92FitDiffers ()

s92FundingNonFactorability :
  NF.NonFactorabilityWitness fundingOnlyObserver s92ElementFit
s92FundingNonFactorability = NF.nonFactorabilityWitness
  publicFundingNoInfluenceNexus
  sameFundingWithInfluenceNexus
  refl
  s92FitDiffers

fundingAloneCannotDetermineS92Fit :
  NF.FactorsThrough fundingOnlyObserver s92ElementFit → ⊥
fundingAloneCannotDetermineS92Fit =
  NF.witnessRulesOutEveryFlatFactorisation s92FundingNonFactorability

------------------------------------------------------------------------
-- A second witness: same political advantage, different personal-benefit /
-- inducement coordinates.  Re-labelling political advantage cannot repair the
-- missing relational facts.
------------------------------------------------------------------------

data PoliticalAdvantageState : Set where
  coalitionAdvantageNoPersonalBenefit : PoliticalAdvantageState
  coalitionAdvantageWithPersonalInducement : PoliticalAdvantageState


data PoliticalAdvantageObserved : Set where
  governmentPoliticallyBenefits : PoliticalAdvantageObserved

politicalAdvantageObserver : PoliticalAdvantageState → PoliticalAdvantageObserved
politicalAdvantageObserver coalitionAdvantageNoPersonalBenefit = governmentPoliticallyBenefits
politicalAdvantageObserver coalitionAdvantageWithPersonalInducement = governmentPoliticallyBenefits

leadership17Fit : PoliticalAdvantageState → Bool
leadership17Fit coalitionAdvantageNoPersonalBenefit = false
leadership17Fit coalitionAdvantageWithPersonalInducement = true

leadership17FitDiffers :
  leadership17Fit coalitionAdvantageNoPersonalBenefit ≡
  leadership17Fit coalitionAdvantageWithPersonalInducement → ⊥
leadership17FitDiffers ()

leadership17PoliticalAdvantageNonFactorability :
  NF.NonFactorabilityWitness politicalAdvantageObserver leadership17Fit
leadership17PoliticalAdvantageNonFactorability = NF.nonFactorabilityWitness
  coalitionAdvantageNoPersonalBenefit
  coalitionAdvantageWithPersonalInducement
  refl
  leadership17FitDiffers

politicalAdvantageCannotDetermineLeadership17Fit :
  NF.FactorsThrough politicalAdvantageObserver leadership17Fit → ⊥
politicalAdvantageCannotDetermineLeadership17Fit =
  NF.witnessRulesOutEveryFlatFactorisation leadership17PoliticalAdvantageNonFactorability

------------------------------------------------------------------------
-- Applicability/admission weld.
--
-- SensibLaw's existing semantic input gate admits reported material only as
-- applicabilityCandidate.  We therefore expose the current Solomon state as a
-- candidate WrongType analysis, not an admitted applicability or violation.
------------------------------------------------------------------------

record SolomonWrongTypeAdmissionState : Set where
  constructor solomon-wrong-type-admission-state
  field
    wrongType : Ontology.WrongType
    authorityMapped : Bool
    authorityMappedIsTrue : authorityMapped ≡ true
    jurisdictionMapped : Bool
    jurisdictionMappedIsTrue : jurisdictionMapped ≡ true
    sectionLevelLocatorMapped : Bool
    sectionLevelLocatorMappedIsTrue : sectionLevelLocatorMapped ≡ true
    resultingApplicability : Status.ApplicabilityStatus
    resultingApplicabilityIsCandidate :
      resultingApplicability ≡ Status.applicabilityCandidate
    occurrenceAdmissionPaid : Bool
    occurrenceAdmissionPaidIsFalse : occurrenceAdmissionPaid ≡ false
    elementPaymentPaid : Bool
    elementPaymentPaidIsFalse : elementPaymentPaid ≡ false
    violationPromoted : Bool
    violationPromotedIsFalse : violationPromoted ≡ false

open SolomonWrongTypeAdmissionState public

currentS92AdmissionState : SolomonWrongTypeAdmissionState
currentS92AdmissionState = solomon-wrong-type-admission-state
  antiCorruptionSection92WrongType
  true refl
  true refl
  true refl
  Status.applicabilityCandidate refl
  false refl
  false refl
  false refl

currentLeadership17AdmissionState : SolomonWrongTypeAdmissionState
currentLeadership17AdmissionState = solomon-wrong-type-admission-state
  leadershipSection17WrongType
  true refl
  true refl
  true refl
  Status.applicabilityCandidate refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Explicit connection to the canonical WrongType applicability owner.
------------------------------------------------------------------------

canonicalApplicabilityReceiptType : Set
canonicalApplicabilityReceiptType = Applicability.WrongTypeApplicabilityReceipt

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SectionCitationMakesWrongTypeApplicable : Set where
data FundingObservationFactorsThroughS92Fit : Set where
data PoliticalAdvantageFactorsThroughLeadership17Fit : Set where
data CandidateApplicabilityEqualsAdmittedApplicability : Set where

authorityCitationDoesNotAutoApplyWrongType :
  SectionCitationMakesWrongTypeApplicable → ⊥
authorityCitationDoesNotAutoApplyWrongType ()

fundingDoesNotFactorThroughS92 : FundingObservationFactorsThroughS92Fit → ⊥
fundingDoesNotFactorThroughS92 ()

politicalAdvantageDoesNotFactorThroughLeadership17 :
  PoliticalAdvantageFactorsThroughLeadership17Fit → ⊥
politicalAdvantageDoesNotFactorThroughLeadership17 ()

candidateDoesNotEqualAdmitted : CandidateApplicabilityEqualsAdmittedApplicability → ⊥
candidateDoesNotEqualAdmitted ()
