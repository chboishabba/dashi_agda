module DASHI.Governance.PublicEssentialCareDoctrineBoundary where

open import Agda.Primitive using (Level; _⊔_)
open import DASHI.Governance.HealthcareEqualityInvariant
open import DASHI.Governance.HealthcareAccessDistortion

------------------------------------------------------------------------
-- Public funding and essential-service dependence create a public-power
-- surface.  Religious or ideological ownership does not erase the access
-- divergence produced when doctrine removes lawful clinically indicated care.

private
  variable
    ℓp ℓn ℓc ℓe : Level

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

record PublicEssentialCareProvider : Set where
  field
    funding : FundingSurface
    criticality : ServiceCriticality
    dependency : DependencySurface
    institutionalDoctrineOperative : Set

open PublicEssentialCareProvider public

record PublicDoctrineAccessFailure
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    provider : PublicEssentialCareProvider
    publicOrSubsidised : Set
    essentialOrLifePreserving : Set
    doctrineFilter : DoctrinalAccessFilter system

open PublicDoctrineAccessFailure public

publicDoctrineAccessFailureDestroysEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  PublicDoctrineAccessFailure system →
  HealthcareEquality system →
  Never
publicDoctrineAccessFailureDestroysEquality failure =
  doctrinalFilterDestroysEquality (doctrineFilter failure)

record SurvivorForcedExposureFailure
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    provider : PublicEssentialCareProvider
    abuseResidueDivergence : AccessDivergence system

open SurvivorForcedExposureFailure public

survivorForcedExposureDestroysEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  SurvivorForcedExposureFailure system →
  HealthcareEquality system →
  Never
survivorForcedExposureDestroysEquality failure =
  accessDivergenceDestroysEquality (abuseResidueDivergence failure)

------------------------------------------------------------------------
-- The formal conclusion is intentionally strict:
--
-- * referral is not equality when it changes accessible care;
-- * delay is not equality;
-- * forced disclosure or exposure is not equality;
-- * a worse-risk pathway is not equality;
-- * geography and capacity are failures too, not excuses;
-- * the predicate cannot be reconstructed while a divergence witness remains.

publiclyFundedDoctrineCannotCoexistWithEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  PublicDoctrineAccessFailure system →
  EqualityRepair system →
  Never
publiclyFundedDoctrineCannotCoexistWithEquality failure repair =
  publicDoctrineAccessFailureDestroysEquality failure
    (repairedEquality repair)
