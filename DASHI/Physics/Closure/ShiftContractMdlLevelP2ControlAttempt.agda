module DASHI.Physics.Closure.ShiftContractMdlLevelP2ControlAttempt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; mdlLevelOnState
    ; π-mdl-max
    ; π-mdl-max-refines-π-max
    ; π-mdl-max-separates-obstruction-pair
    )
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
  using (π-max)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using
    ( coarseCounterexampleLeft
    ; coarseCounterexampleRight
    ; sameCoarseObservable
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance
  using (ShiftContractState)

------------------------------------------------------------------------
-- Narrow mdl-level control attempt above `π-max`.
--
-- This is intentionally weaker than a genuine p2-to-prime-image control law.
-- It packages the strongest positive statement currently supported on the
-- exact stronger surface `mdlLevel × π-max`:
-- equality of the package determines both the mdlLevel coordinate and the
-- old coarse observable.

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

mdlLevel-package-controls-refinement :
  ∀ x →
  proj₂ (π-mdl-max x) ≡ SCCO.π-max x
mdlLevel-package-controls-refinement = π-mdl-max-refines-π-max

mdlLevel-package-not-through-π-max :
  (∀ x y → SCCO.π-max x ≡ SCCO.π-max y → π-mdl-max x ≡ π-mdl-max y) →
  ⊥
mdlLevel-package-not-through-π-max through =
  π-mdl-max-separates-obstruction-pair
    (through
      coarseCounterexampleLeft
      coarseCounterexampleRight
      sameCoarseObservable)

record ShiftContractMdlLevelP2ControlAttempt : Set₁ where
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

canonicalShiftContractMdlLevelP2ControlAttempt :
  ShiftContractMdlLevelP2ControlAttempt
canonicalShiftContractMdlLevelP2ControlAttempt =
  record
    { projection = π-mdl-max
    ; refines-π-max = mdlLevel-package-controls-refinement
    ; mdlLevel-controls = mdlLevel-package-controls-mdlLevel
    ; coarse-controls = mdlLevel-package-controls-coarse
    ; separates-obstruction-pair = π-mdl-max-separates-obstruction-pair
    }

open ShiftContractMdlLevelP2ControlAttempt public
