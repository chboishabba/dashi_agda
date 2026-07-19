module DASHI.Governance.PublicEssentialCareDoctrineBoundary where

open import DASHI.Governance.HealthcareEqualityInvariant
open import DASHI.Governance.HealthcareAccessDistortion

------------------------------------------------------------------------
-- Public funding and essential-service dependence create a public-power
-- surface. Religious or ideological ownership does not erase the access
-- divergence produced when doctrine removes lawful clinically indicated care.

data FundingSurface : Set where
  whollyPublic : FundingSurface
  publiclySubsidised : FundingSurface
  publicPrivateContract : FundingSurface
  whollyPrivate : FundingSurface

data ServiceCriticality : Set where
  elective : ServiceCriticality
  important : ServiceCriticality
  essential : ServiceCriticality
  lifePreserving : ServiceCriticality

data DependencySurface : Set where
  freelySubstitutable : DependencySurface
  costlyExit : DependencySurface
  geographicallyCaptive : DependencySurface
  clinicallyCaptive : DependencySurface
  institutionallyTraumatised : DependencySurface

record PublicEssentialCareProvider : Set₁ where
  field
    funding : FundingSurface
    criticality : ServiceCriticality
    dependency : DependencySurface
    institutionalDoctrineOperative : Set

open PublicEssentialCareProvider public

record PublicDoctrineAccessFailure
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set₁ where
  field
    provider : PublicEssentialCareProvider
    publicOrSubsidised : Set
    essentialOrLifePreserving : Set
    doctrineFilter : DoctrinalAccessFilter system

open PublicDoctrineAccessFailure public

publicDoctrineAccessFailureDestroysEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  PublicDoctrineAccessFailure system →
  HealthcareEquality system →
  Never
publicDoctrineAccessFailureDestroysEquality failure =
  doctrinalFilterDestroysEquality (doctrineFilter failure)

record SurvivorForcedExposureFailure
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set₁ where
  field
    provider : PublicEssentialCareProvider
    abuseResidueDivergence : AccessDivergence system

open SurvivorForcedExposureFailure public

survivorForcedExposureDestroysEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  SurvivorForcedExposureFailure system →
  HealthcareEquality system →
  Never
survivorForcedExposureDestroysEquality failure =
  accessDivergenceDestroysEquality (abuseResidueDivergence failure)

------------------------------------------------------------------------
-- The conclusion is intentionally strict:
--
-- * referral is not equality when it changes accessible care;
-- * delay is not equality;
-- * forced disclosure or exposure is not equality;
-- * a worse-risk pathway is not equality;
-- * geography and capacity are failures too, not excuses;
-- * the predicate cannot be reconstructed while a divergence witness remains.

publiclyFundedDoctrineCannotCoexistWithEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  PublicDoctrineAccessFailure system →
  EqualityRepair system →
  Never
publiclyFundedDoctrineCannotCoexistWithEquality failure repair =
  publicDoctrineAccessFailureDestroysEquality failure
    (repairedEquality repair)
