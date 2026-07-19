module DASHI.Governance.HealthcareAccessDistortion where

open import Agda.Primitive using (Level)
open import DASHI.Governance.HealthcareEqualityInvariant

------------------------------------------------------------------------
-- Causes classify an access divergence; they do not weaken the invariant.
-- Geography, capacity, wealth and doctrine are explanatory coordinates,
-- never constructors of healthcare equality.

private
  variable
    ℓp ℓn ℓc ℓe : Level

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
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    axis : DistortionAxis
    divergence : AccessDivergence system

open CausedAccessDivergence public

causeDoesNotExcuseDivergence :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  CausedAccessDivergence system →
  HealthcareEquality system →
  Never
causeDoesNotExcuseDivergence caused =
  accessDivergenceDestroysEquality (divergence caused)

record DoctrinalAccessFilter
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    doctrinalDivergence : AccessDivergence system

open DoctrinalAccessFilter public

doctrinalFilterDestroysEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  DoctrinalAccessFilter system →
  HealthcareEquality system →
  Never
doctrinalFilterDestroysEquality filter =
  accessDivergenceDestroysEquality (doctrinalDivergence filter)

record GeographicAccessFilter
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    geographicDivergence : AccessDivergence system

open GeographicAccessFilter public

geographicFilterDestroysEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  GeographicAccessFilter system →
  HealthcareEquality system →
  Never
geographicFilterDestroysEquality filter =
  accessDivergenceDestroysEquality (geographicDivergence filter)
