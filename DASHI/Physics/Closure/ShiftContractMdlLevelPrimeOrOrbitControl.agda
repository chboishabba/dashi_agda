module DASHI.Physics.Closure.ShiftContractMdlLevelPrimeOrOrbitControl where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using (p2)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (MaximalCoarseObservable; π-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; mdlLevelOnState
    ; π-mdl-max
    ; π-mdl-max-refines-π-max
    ; π-mdl-max-separates-obstruction-pair
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
  using (ShiftContractMdlLevelCoarseFibre; carrier)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMFF
  using (primeField; orbitSummaryField; eigenShadowField)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using
    ( coarseCounterexampleLeft
    ; coarseCounterexampleRight
    ; sameCoarseObservable
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)

------------------------------------------------------------------------
-- Noncanonical prime/orbit control attempt on the strengthened surface
-- `mdlLevel × π-max`.
--
-- The surface itself is now explicit on the md-level fibre, but the repo
-- does not currently provide a fresh same-surface witness pair to support a
-- stronger prime-image or p2-orbit-summary control theorem.  So the sharpest
-- compiling result here is the same-surface package plus the obstruction that
-- this stronger surface still does not factor through the old coarse quotient.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

mdlLevel-package-controls-mdlLevel :
  ∀ x y →
  π-mdl-max x ≡ π-mdl-max y →
  mdlLevelOnState x ≡ mdlLevelOnState y
mdlLevel-package-controls-mdlLevel _ _ eq = cong proj₁ eq

mdlLevel-package-controls-coarse :
  ∀ x y →
  π-mdl-max x ≡ π-mdl-max y →
  SCCO.π-max x ≡ SCCO.π-max y
mdlLevel-package-controls-coarse _ _ eq = cong proj₂ eq

mdlLevel-package-refines-coarse :
  ∀ x →
  proj₂ (π-mdl-max x) ≡ SCCO.π-max x
mdlLevel-package-refines-coarse = π-mdl-max-refines-π-max

-- The strengthened surface exposes the new md-level fibre vocabulary.
mdlLevelFibrePrimeField :
  ∀ {q} →
  ShiftContractMdlLevelCoarseFibre q → FactorVec
mdlLevelFibrePrimeField = SCMFF.primeField

mdlLevelFibreOrbitSummary :
  ∀ {q} →
  ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
mdlLevelFibreOrbitSummary = SCMFF.orbitSummaryField p2

mdlLevelFibreEigenShadow :
  ∀ {q} →
  ShiftContractMdlLevelCoarseFibre q → Nat × Nat
mdlLevelFibreEigenShadow = SCMFF.eigenShadowField

mdlLevel-package-not-through-π-max :
  (∀ x y → SCCO.π-max x ≡ SCCO.π-max y → π-mdl-max x ≡ π-mdl-max y) →
  ⊥
mdlLevel-package-not-through-π-max through =
  π-mdl-max-separates-obstruction-pair
    (through
      coarseCounterexampleLeft
      coarseCounterexampleRight
      sameCoarseObservable)

record ShiftContractMdlLevelPrimeOrOrbitControlAttempt : Set₁ where
  field
    projection : ShiftContractState → MdlLevelCoarseObservable
    refines-π-max :
      ∀ x →
      proj₂ (projection x) ≡ SCCO.π-max x
    mdlLevel-controls :
      ∀ x y →
      projection x ≡ projection y →
      mdlLevelOnState x ≡ mdlLevelOnState y
    coarse-controls :
      ∀ x y →
      projection x ≡ projection y →
      SCCO.π-max x ≡ SCCO.π-max y
    separates-obstruction-pair :
      projection coarseCounterexampleLeft
        ≢
      projection coarseCounterexampleRight

canonicalShiftContractMdlLevelPrimeOrOrbitControlAttempt :
  ShiftContractMdlLevelPrimeOrOrbitControlAttempt
canonicalShiftContractMdlLevelPrimeOrOrbitControlAttempt =
  record
    { projection = π-mdl-max
    ; refines-π-max = mdlLevel-package-refines-coarse
    ; mdlLevel-controls = mdlLevel-package-controls-mdlLevel
    ; coarse-controls = mdlLevel-package-controls-coarse
    ; separates-obstruction-pair = π-mdl-max-separates-obstruction-pair
    }

open ShiftContractMdlLevelPrimeOrOrbitControlAttempt public
