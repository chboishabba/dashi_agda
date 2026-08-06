module DASHI.Physics.Common.GradedLocalCompatibilitySystemExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations aux
-- derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
-- A domain-neutral carrier for the exact common architecture used by the
-- Moonshine/VOA, Navier--Stokes shell and Yang--Mills RG lanes:
-- graded states, local operations, declared output grades, separating probes,
-- compatibility defects and defect transport.  The observation carrier is
-- separate from the state carrier.  No theorem identifies the concrete notions
-- of locality in those three domains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)

record GradedLocalCompatibilitySystem : Set₁ where
  constructor gradedLocalCompatibilitySystem
  field
    Grade : Set
    State : Set
    Probe : Set
    Observation : Set
    Defect : Set

    gradeOf : State → Grade
    localOperation : State → State → State
    outputGrade : State → State → Grade
    localOperationHasDeclaredGrade :
      ∀ left right →
      gradeOf (localOperation left right) ≡ outputGrade left right

    observe : Probe → State → Observation
    transportDefect : Defect → Defect

open GradedLocalCompatibilitySystem public

ProbeAgreement :
  (system : GradedLocalCompatibilitySystem) →
  State system → State system → Set
ProbeAgreement system left right =
  (probe : Probe system) →
  observe system probe left ≡ observe system probe right

record SeparatingGradedLocalCompatibilitySystem : Set₁ where
  constructor separatingGradedLocalCompatibilitySystem
  field
    system : GradedLocalCompatibilitySystem
    probesSeparate :
      ∀ left right →
      ProbeAgreement system left right →
      left ≡ right

open SeparatingGradedLocalCompatibilitySystem public

localOperationGradeStable :
  (system : GradedLocalCompatibilitySystem) →
  ∀ left right →
  gradeOf system (localOperation system left right)
  ≡ outputGrade system left right
localOperationGradeStable = localOperationHasDeclaredGrade

transportDefectTwice :
  (system : GradedLocalCompatibilitySystem) →
  Defect system → Defect system
transportDefectTwice system defect =
  transportDefect system (transportDefect system defect)

transportDefectEquality :
  (system : GradedLocalCompatibilitySystem) →
  ∀ {left right} → left ≡ right →
  transportDefect system left ≡ transportDefect system right
transportDefectEquality system equality =
  cong (transportDefect system) equality

record DomainIdentificationBoundary : Set where
  constructor domainIdentificationBoundary
  field
    voaLocalityIsNavierStokesShellLocality : Set
    voaLocalityIsNotIdentifiedWithNavierStokesShellLocality :
      voaLocalityIsNavierStokesShellLocality → Set

    voaLocalityIsYangMillsGaugeLocality : Set
    voaLocalityIsNotIdentifiedWithYangMillsGaugeLocality :
      voaLocalityIsYangMillsGaugeLocality → Set

canonicalDomainIdentificationBoundary : DomainIdentificationBoundary
canonicalDomainIdentificationBoundary =
  domainIdentificationBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
