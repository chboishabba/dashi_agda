module DASHI.Governance.HealthcareAccessDistortion where

open import DASHI.Governance.HealthcareEqualityInvariant

------------------------------------------------------------------------
-- Causes classify an access divergence; they do not weaken the invariant.
-- Geography, capacity, wealth and doctrine are explanatory coordinates,
-- never constructors of healthcare equality.

data DistortionAxis : Set where
  geography : DistortionAxis
  triageMisallocation : DistortionAxis
  specialistCapacity : DistortionAxis
  wealthOrInsurance : DistortionAxis
  disabilityAccess : DistortionAxis
  raceOrColoniality : DistortionAxis
  sexGenderOrReproduction : DistortionAxis
  providerIdentity : DistortionAxis
  institutionalDoctrine : DistortionAxis
  institutionalAbuseResidue : DistortionAxis
  forcedDependency : DistortionAxis

record CausedAccessDivergence
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set where
  field
    axis : DistortionAxis
    divergence : AccessDivergence system

open CausedAccessDivergence public

causeDoesNotExcuseDivergence :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  CausedAccessDivergence system →
  HealthcareEquality system →
  Never
causeDoesNotExcuseDivergence caused =
  accessDivergenceDestroysEquality (divergence caused)

record DoctrinalAccessFilter
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set where
  field
    doctrinalDivergence : AccessDivergence system

open DoctrinalAccessFilter public

doctrinalFilterDestroysEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  DoctrinalAccessFilter system →
  HealthcareEquality system →
  Never
doctrinalFilterDestroysEquality filter =
  accessDivergenceDestroysEquality (doctrinalDivergence filter)

record GeographicAccessFilter
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set where
  field
    geographicDivergence : AccessDivergence system

open GeographicAccessFilter public

geographicFilterDestroysEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  GeographicAccessFilter system →
  HealthcareEquality system →
  Never
geographicFilterDestroysEquality filter =
  accessDivergenceDestroysEquality (geographicDivergence filter)
