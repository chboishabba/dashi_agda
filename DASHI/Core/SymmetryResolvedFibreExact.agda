module DASHI.Core.SymmetryResolvedFibreExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- TOE spine: symmetry-bearing state, equivariant observation, and residual
-- reopening are independent structures.
--
-- A deliberately lossy observer is not required to preserve every operation
-- on the rich carrier.  Algebraic obligations live on the native action and
-- on reductions that explicitly claim equivariance.
------------------------------------------------------------------------

record LawfulAction (G X : Set) : Set where
  field
    identity : G
    compose : G → G → G
    act : G → X → X

    composeIdLeft :
      (g : G) → compose identity g ≡ g
    composeIdRight :
      (g : G) → compose g identity ≡ g
    composeAssoc :
      (h g f : G) →
      compose (compose h g) f ≡ compose h (compose g f)

    actIdentity :
      (x : X) → act identity x ≡ x
    actComposition :
      (g f : G) →
      (x : X) →
      act (compose g f) x ≡ act g (act f x)

open LawfulAction public

record EquivariantObserver
  (G Rich Coarse : Set)
  (rich : LawfulAction G Rich)
  (coarse : LawfulAction G Coarse)
  : Set where
  field
    observe : Rich → Coarse
    observeEquivariant :
      (g : G) →
      (x : Rich) →
      observe (act rich g x) ≡ act coarse g (observe x)

open EquivariantObserver public

record ReopenableObserver (Rich Surface Residual : Set) : Set where
  field
    project : Rich → Surface
    retainResidual : Rich → Residual
    reopen : Surface → Residual → Rich
    reopenExact :
      (x : Rich) →
      reopen (project x) (retainResidual x) ≡ x

open ReopenableObserver public

record SymmetryResolvedFibre
  (G Rich Surface Residual : Set)
  : Set where
  field
    richAction : LawfulAction G Rich
    surfaceAction : LawfulAction G Surface
    observer : EquivariantObserver G Rich Surface richAction surfaceAction
    residualObserver : ReopenableObserver Rich Surface Residual
    sameProjection :
      (x : Rich) →
      observe observer x ≡ project residualObserver x

open SymmetryResolvedFibre public

------------------------------------------------------------------------
-- Generic consequences.
------------------------------------------------------------------------

equivariantProjection :
  ∀ {G Rich Surface Residual}
  (F : SymmetryResolvedFibre G Rich Surface Residual) →
  (g : G) →
  (x : Rich) →
  project (residualObserver F) (act (richAction F) g x)
  ≡
  act (surfaceAction F) g (project (residualObserver F) x)
equivariantProjection F g x =
  trans
    (sym (sameProjection F (act (richAction F) g x)))
    (trans
      (observeEquivariant (observer F) g x)
      (cong (act (surfaceAction F) g) (sameProjection F x)))

reopenAfterObservation :
  ∀ {G Rich Surface Residual}
  (F : SymmetryResolvedFibre G Rich Surface Residual) →
  (x : Rich) →
  reopen (residualObserver F)
    (observe (observer F) x)
    (retainResidual (residualObserver F) x)
  ≡ x
reopenAfterObservation F x
  rewrite sameProjection F x = reopenExact (residualObserver F) x

observerPlusResidualIsInjective :
  ∀ {G Rich Surface Residual}
  (F : SymmetryResolvedFibre G Rich Surface Residual) →
  (x y : Rich) →
  observe (observer F) x ≡ observe (observer F) y →
  retainResidual (residualObserver F) x ≡ retainResidual (residualObserver F) y →
  x ≡ y
observerPlusResidualIsInjective F x y surfaceEq residualEq =
  trans
    (sym (reopenAfterObservation F x))
    (trans
      (cong
        (λ surface →
          reopen (residualObserver F) surface
            (retainResidual (residualObserver F) x))
        surfaceEq)
      (trans
        (cong
          (reopen (residualObserver F) (observe (observer F) y))
          residualEq)
        (reopenAfterObservation F y)))

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SymmetryResolvedFibreBoundary : Set where
  constructor boundary
  field
    coarseObserverMustPreserveEveryRichOperation : Bool
    coarseObserverMustPreserveEveryRichOperationIsFalse :
      coarseObserverMustPreserveEveryRichOperation ≡ false

    equalCarrierCardinalityDeterminesOperation : Bool
    equalCarrierCardinalityDeterminesOperationIsFalse :
      equalCarrierCardinalityDeterminesOperation ≡ false

    residualMayBeDiscardedWhenReopeningIsRequired : Bool
    residualMayBeDiscardedWhenReopeningIsRequiredIsFalse :
      residualMayBeDiscardedWhenReopeningIsRequired ≡ false

canonicalSymmetryResolvedFibreBoundary : SymmetryResolvedFibreBoundary
canonicalSymmetryResolvedFibreBoundary = boundary false refl false refl false refl
