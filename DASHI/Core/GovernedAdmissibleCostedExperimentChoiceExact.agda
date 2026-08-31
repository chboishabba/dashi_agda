module DASHI.Core.GovernedAdmissibleCostedExperimentChoiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ConsentTemporalExternalityExact as Consent
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Dist
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch

------------------------------------------------------------------------
-- GOVERNED ADMISSIBLE COSTED EXPERIMENT CHOICE
--
-- Source-neutral DASHI mathematics.
--
-- The existing actionability search already optimises only over a declared
-- comparison set.  This owner makes one high-consequence declaration explicit:
-- cost comparison happens only after independent receipts for epistemic
-- adequacy, authority, permission, scoped consent, obligations, externality,
-- distribution and temporal/intergenerational coverage have been supplied.
--
-- It does NOT define substantive ethics, welfare or law.  Downstream source
-- atlases/calibration owners determine what counts as a valid receipt in an
-- application.
------------------------------------------------------------------------

data EpistemicallyAdmissible : Choice.InformationMove → Set where
  governedEpistemic :
    EpistemicallyAdmissible Dist.strategyMove Dist.distributionAwareStrategy

data AuthorityAdmissible : Choice.InformationMove → Set where
  governedAuthority :
    AuthorityAdmissible Dist.strategyMove Dist.distributionAwareStrategy

data PermissionAdmissible : Choice.InformationMove → Set where
  governedPermission :
    PermissionAdmissible Dist.strategyMove Dist.distributionAwareStrategy

data ConsentAdmissibleAt :
    Consent.ActionScope → Choice.InformationMove → Set where
  governedInitialConsent :
    ConsentAdmissibleAt Consent.initialResearch
      (Dist.strategyMove Dist.distributionAwareStrategy)
  governedReuseConsent :
    ConsentAdmissibleAt Consent.downstreamReuse
      (Dist.strategyMove Dist.distributionAwareStrategy)

data ObligationsAdmissible : Choice.InformationMove → Set where
  governedObligations :
    ObligationsAdmissible Dist.strategyMove Dist.distributionAwareStrategy

data ExternalitiesCovered : Choice.InformationMove → Set where
  governedExternalities :
    ExternalitiesCovered Dist.strategyMove Dist.distributionAwareStrategy

data DistributionCovered : Choice.InformationMove → Set where
  governedDistribution :
    DistributionCovered Dist.strategyMove Dist.distributionAwareStrategy

data IntergenerationalCovered : Choice.InformationMove → Set where
  governedIntergenerational :
    IntergenerationalCovered Dist.strategyMove Dist.distributionAwareStrategy

record GovernedAdmissibleAt
    (scope : Consent.ActionScope)
    (move : Choice.InformationMove) : Set where
  constructor governedAdmissibleAt
  field
    epistemic : EpistemicallyAdmissible move
    authority : AuthorityAdmissible move
    permission : PermissionAdmissible move
    consent : ConsentAdmissibleAt scope move
    obligations : ObligationsAdmissible move
    externalities : ExternalitiesCovered move
    distribution : DistributionCovered move
    intergenerational : IntergenerationalCovered move

open GovernedAdmissibleAt public

canonicalGovernedInitialMove :
  GovernedAdmissibleAt Consent.initialResearch
    (Dist.strategyMove Dist.distributionAwareStrategy)
canonicalGovernedInitialMove =
  governedAdmissibleAt
    governedEpistemic governedAuthority governedPermission
    governedInitialConsent governedObligations governedExternalities
    governedDistribution governedIntergenerational

canonicalGovernedReuseMove :
  GovernedAdmissibleAt Consent.downstreamReuse
    (Dist.strategyMove Dist.distributionAwareStrategy)
canonicalGovernedReuseMove =
  governedAdmissibleAt
    governedEpistemic governedAuthority governedPermission
    governedReuseConsent governedObligations governedExternalities
    governedDistribution governedIntergenerational

------------------------------------------------------------------------
-- The institution-centred strategy has the SAME declared search/resource cost,
-- but no constructors exist for any governed-admissibility receipt above.
------------------------------------------------------------------------

institutionCentredCannotBeGovernedInitially :
  GovernedAdmissibleAt Consent.initialResearch
    (Dist.strategyMove Dist.institutionCentredStrategy) → ⊥
institutionCentredCannotBeGovernedInitially ()

institutionCentredCannotBeGovernedForReuse :
  GovernedAdmissibleAt Consent.downstreamReuse
    (Dist.strategyMove Dist.institutionCentredStrategy) → ⊥
institutionCentredCannotBeGovernedForReuse ()

sameRawCostStill :
  Choice.cost (Dist.strategyMove Dist.institutionCentredStrategy) ≡
  Choice.cost (Dist.strategyMove Dist.distributionAwareStrategy)
sameRawCostStill = Dist.sameDeclaredSearchCost

------------------------------------------------------------------------
-- Filter first, optimise second.
------------------------------------------------------------------------

record GovernedCheapestMove
    (scope : Consent.ActionScope)
    (Candidate : Choice.InformationMove → Set) : Set₁ where
  constructor governedCheapestMove
  field
    selected : Choice.InformationMove
    selectedCandidate : Candidate selected
    selectedGoverned : GovernedAdmissibleAt scope selected
    minimalAmongGoverned :
      (alternative : Choice.InformationMove) →
      Candidate alternative →
      GovernedAdmissibleAt scope alternative →
      Choice.cost selected ≤ Choice.cost alternative
    comparisonReference : String

open GovernedCheapestMove public

data DemoCandidate : Choice.InformationMove → Set where
  institutionCandidate : DemoCandidate (Dist.strategyMove Dist.institutionCentredStrategy)
  distributionCandidate : DemoCandidate (Dist.strategyMove Dist.distributionAwareStrategy)

canonicalGovernedCheapestInitial : GovernedCheapestMove Consent.initialResearch DemoCandidate
canonicalGovernedCheapestInitial =
  governedCheapestMove
    (Dist.strategyMove Dist.distributionAwareStrategy)
    distributionCandidate
    canonicalGovernedInitialMove
    minimal
    "Compare declared resource cost only after governed admissibility."
  where
    minimal :
      (alternative : Choice.InformationMove) →
      DemoCandidate alternative →
      GovernedAdmissibleAt Consent.initialResearch alternative →
      Choice.cost (Dist.strategyMove Dist.distributionAwareStrategy) ≤ Choice.cost alternative
    minimal .(Dist.strategyMove Dist.institutionCentredStrategy) institutionCandidate governed =
      ⊥-elim (institutionCentredCannotBeGovernedInitially governed)
    minimal .(Dist.strategyMove Dist.distributionAwareStrategy) distributionCandidate _ = ≤-refl

------------------------------------------------------------------------
-- Scope matters: initial consent is not reused as downstream-reuse consent.
------------------------------------------------------------------------

data InitialOnlyConsentReceipt : Set where initialOnly : InitialOnlyConsentReceipt

initialConsentCannotPopulateReuseAdmission :
  Consent.ConsentFor
    (Consent.scopedConsentState Consent.initialResearch Consent.consentGranted
      Consent.protocolPermissionPresent Consent.authorityPresent
      Consent.benefitSharingAbsent)
    Consent.downstreamReuse → ⊥
initialConsentCannotPopulateReuseAdmission = Consent.initialConsentDoesNotAuthorizeReuse

------------------------------------------------------------------------
-- Proof-search success remains orthogonal to governed action admissibility.
-- The imported owner is retained as the canonical proof-search authority;
-- this file does not reinterpret theorem-route admission as social authority.
------------------------------------------------------------------------

proofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record GovernedAdmissibleCostedChoiceBoundary : Set where
  constructor governed-admissible-costed-choice-boundary
  field
    cheapestRawMoveAutomaticallyGovernedAdmissible : Bool
    cheapestRawMoveAutomaticallyGovernedAdmissibleIsFalse :
      cheapestRawMoveAutomaticallyGovernedAdmissible ≡ false
    equalSearchCostMeansEqualSocialAdmissibility : Bool
    equalSearchCostMeansEqualSocialAdmissibilityIsFalse :
      equalSearchCostMeansEqualSocialAdmissibility ≡ false
    initialConsentMayBeReusedForAnyLaterScope : Bool
    initialConsentMayBeReusedForAnyLaterScopeIsFalse :
      initialConsentMayBeReusedForAnyLaterScope ≡ false
    proofRouteAdmissionEqualsGovernedActionAdmission : Bool
    proofRouteAdmissionEqualsGovernedActionAdmissionIsFalse :
      proofRouteAdmissionEqualsGovernedActionAdmission ≡ false
    admissibilityCoverageSettlesSubstantiveJustice : Bool
    admissibilityCoverageSettlesSubstantiveJusticeIsFalse :
      admissibilityCoverageSettlesSubstantiveJustice ≡ false

canonicalGovernedAdmissibleCostedChoiceBoundary :
  GovernedAdmissibleCostedChoiceBoundary
canonicalGovernedAdmissibleCostedChoiceBoundary =
  governed-admissible-costed-choice-boundary
    false refl false refl false refl false refl false refl
