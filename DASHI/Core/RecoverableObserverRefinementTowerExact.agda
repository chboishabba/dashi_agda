module DASHI.Core.RecoverableObserverRefinementTowerExact where

------------------------------------------------------------------------
-- RECOVERABLE QUOTIENTS AS FACTORIZED OBSERVER TOWERS
--
-- RecoverableQuotientCompositionExact already proves that two exact
-- recoverable projections compose and that the composite residual is the
-- product of the stage residuals.  This module cross-pollinates that result
-- with ObserverFactorizedRefinementExact.
--
-- A recoverable projection therefore carries two observer surfaces:
--
--   exact observer  = (coarse surface , residual)
--   public observer = coarse surface
--
-- with an explicit factor map `proj₁`.  The exact observer separates the fine
-- carrier, while the public observer need not.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RecoverableQuotientCompositionExact as Recoverable

exactRecoverableObserver :
  ∀ {X Y : Set}
    (projection : Recoverable.ExactRecoverableProjection X Y) →
  Observer.Observer X (Y × Recoverable.Residual projection)
exactRecoverableObserver projection x =
  Recoverable.project projection x , Recoverable.residual projection x

exactRecoverableObserverSeparating :
  ∀ {X Y : Set}
    (projection : Recoverable.ExactRecoverableProjection X Y) →
  Observer.Separating (exactRecoverableObserver projection)
exactRecoverableObserverSeparating projection x y same =
  trans
    (sym (Recoverable.reopenExact projection x))
    (trans
      (cong
        (λ pair →
          Recoverable.reopen projection (proj₁ pair) (proj₂ pair))
        same)
      (Recoverable.reopenExact projection y))

coarseFactorsThroughExactRecoverableObserver :
  ∀ {X Y : Set}
    (projection : Recoverable.ExactRecoverableProjection X Y) →
  Factorized.FactorizedRefinement
    (Recoverable.project projection)
    (exactRecoverableObserver projection)
coarseFactorsThroughExactRecoverableObserver projection =
  Factorized.factorizedRefinement proj₁ (λ x → refl)

------------------------------------------------------------------------
-- Composition retains the stagewise residual coordinates as a product.
------------------------------------------------------------------------

compositeExactObserver :
  ∀ {X Y Z : Set}
    (first : Recoverable.ExactRecoverableProjection X Y)
    (second : Recoverable.ExactRecoverableProjection Y Z) →
  Observer.Observer X
    (Z × (Recoverable.Residual first × Recoverable.Residual second))
compositeExactObserver first second =
  exactRecoverableObserver (Recoverable.composeRecoverable first second)

compositeExactObserverSeparating :
  ∀ {X Y Z : Set}
    (first : Recoverable.ExactRecoverableProjection X Y)
    (second : Recoverable.ExactRecoverableProjection Y Z) →
  Observer.Separating (compositeExactObserver first second)
compositeExactObserverSeparating first second =
  exactRecoverableObserverSeparating
    (Recoverable.composeRecoverable first second)

compositePublicObserverFactorsThroughExactObserver :
  ∀ {X Y Z : Set}
    (first : Recoverable.ExactRecoverableProjection X Y)
    (second : Recoverable.ExactRecoverableProjection Y Z) →
  Factorized.FactorizedRefinement
    (Recoverable.project (Recoverable.composeRecoverable first second))
    (compositeExactObserver first second)
compositePublicObserverFactorsThroughExactObserver first second =
  coarseFactorsThroughExactRecoverableObserver
    (Recoverable.composeRecoverable first second)

record RecoverableObserverRefinementTowerBoundary : Set where
  constructor recoverableObserverRefinementTowerBoundary
  field
    coarsePlusResidualSeparatesFineCarrier : Bool
    coarsePlusResidualSeparatesFineCarrierIsTrue :
      coarsePlusResidualSeparatesFineCarrier ≡ true
    publicSurfaceFactorsFromExactObserver : Bool
    publicSurfaceFactorsFromExactObserverIsTrue :
      publicSurfaceFactorsFromExactObserver ≡ true
    stagedResidualsComposeAsProduct : Bool
    stagedResidualsComposeAsProductIsTrue :
      stagedResidualsComposeAsProduct ≡ true
    productResidualMeansSemanticCoordinatesIndependent : Bool
    productResidualMeansSemanticCoordinatesIndependentIsFalse :
      productResidualMeansSemanticCoordinatesIndependent ≡ false

canonicalRecoverableObserverRefinementTowerBoundary :
  RecoverableObserverRefinementTowerBoundary
canonicalRecoverableObserverRefinementTowerBoundary =
  recoverableObserverRefinementTowerBoundary
    true refl
    true refl
    true refl
    false refl
