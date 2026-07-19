module DASHI.Governance.HealthcareEqualityInvariant where

open import Agda.Primitive using (Level; _⊔_)

------------------------------------------------------------------------
-- Strict healthcare-equality invariant.
--
-- Equality is not a graded score here.  A system satisfies the invariant
-- only when clinically equivalent need always induces equivalent accessible
-- care.  Any witnessed divergence destroys the predicate until the causal
-- access defect is removed.

private
  variable
    ℓp ℓn ℓc ℓe : Level

data Never : Set where

record HealthcareSystem
  (Patient : Set ℓp)
  (Need : Set ℓn)
  (Care : Set ℓc)
  : Set (ℓp ⊔ ℓn ⊔ ℓc) where
  field
    clinicalNeed : Patient → Need
    accessibleCare : Patient → Care
    clinicallyEquivalent : Patient → Patient → Set ℓe
    careEquivalent : Care → Care → Set ℓe

open HealthcareSystem public

HealthcareEquality :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  HealthcareSystem Patient Need Care →
  Set (ℓp ⊔ ℓe)
HealthcareEquality system =
  ∀ p q →
  clinicallyEquivalent system p q →
  careEquivalent system
    (accessibleCare system p)
    (accessibleCare system q)

record AccessDivergence
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
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
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
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
  {Patient : Set ℓp}
  {Need : Set ℓn}
  {Care : Set ℓc}
  (system : HealthcareSystem Patient Need Care)
  : Set (ℓp ⊔ ℓe) where
  field
    repairedEquality : HealthcareEquality system

open EqualityRepair public

noRepairWhileDivergenceRemains :
  {Patient : Set ℓp} →
  {Need : Set ℓn} →
  {Care : Set ℓc} →
  {system : HealthcareSystem Patient Need Care} →
  AccessDivergence system →
  EqualityRepair system →
  Never
noRepairWhileDivergenceRemains divergence repair =
  accessDivergenceDestroysEquality divergence (repairedEquality repair)
