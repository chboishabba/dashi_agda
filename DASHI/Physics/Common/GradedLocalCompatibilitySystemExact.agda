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
-- Domain-neutral graded states, local operations, output grades, probes,
-- observations and transported defects.  Concrete VOA locality, NS shell
-- compatibility and YM gauge/RG locality are not identified.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; cong)

record GradedLocalCompatibilitySystem : Set₁ where
  constructor gradedLocalCompatibilitySystem
  field
    Grade State Probe Observation Defect : Set
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
