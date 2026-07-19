module DASHI.Governance.HealthcareEqualityInvariant where

------------------------------------------------------------------------
-- Strict healthcare-equality invariant.
--
-- Equality is not a graded score here. A system satisfies the invariant
-- only when clinically equivalent need always induces equivalent accessible
-- care. Any witnessed divergence destroys the predicate until the causal
-- access defect is removed.

data Never : Set where

record HealthcareSystem
  (Patient Need Care : Set)
  : Set₁ where
  field
    clinicalNeed : Patient → Need
    accessibleCare : Patient → Care
    clinicallyEquivalent : Patient → Patient → Set
    careEquivalent : Care → Care → Set

open HealthcareSystem public

HealthcareEquality :
  {Patient Need Care : Set} →
  HealthcareSystem Patient Need Care →
  Set
HealthcareEquality system =
  ∀ p q →
  clinicallyEquivalent system p q →
  careEquivalent system
    (accessibleCare system p)
    (accessibleCare system q)

record AccessDivergence
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set where
  field
    firstPatient : Patient
    secondPatient : Patient
    sameClinicalNeed :
      clinicallyEquivalent system firstPatient secondPatient
    unequalAccessibleCare :
      careEquivalent system
        (accessibleCare system firstPatient)
        (accessibleCare system secondPatient) →
      Never

open AccessDivergence public

accessDivergenceDestroysEquality :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  AccessDivergence system →
  HealthcareEquality system →
  Never
accessDivergenceDestroysEquality divergence equality =
  unequalAccessibleCare divergence
    (equality
      (firstPatient divergence)
      (secondPatient divergence)
      (sameClinicalNeed divergence))

record EqualityRepair
  {Patient Need Care : Set}
  (system : HealthcareSystem Patient Need Care)
  : Set where
  field
    repairedEquality : HealthcareEquality system

open EqualityRepair public

noRepairWhileDivergenceRemains :
  {Patient Need Care : Set} →
  {system : HealthcareSystem Patient Need Care} →
  AccessDivergence system →
  EqualityRepair system →
  Never
noRepairWhileDivergenceRemains divergence repair =
  accessDivergenceDestroysEquality divergence (repairedEquality repair)
