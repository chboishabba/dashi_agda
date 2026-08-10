module DASHI.Analysis.NormalizedFibreAveragingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Vladimir I. Bogachev, "Measure Theory", Springer, 2007.
-- DOI: 10.1007/978-3-540-34514-5.
--
-- The analytic disintegration theorem is NOT re-proved here.  This file gives
-- an exact finite conditional-probability model of the algebra used by it:
-- every coarse point has a two-point fibre with weights 1/2,1/2.  Thus the
-- fibre mass is literally one, fibre averaging is a left inverse to pullback,
-- and the induced fine-space operator is idempotent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- A finite fibre over an arbitrary coarse carrier.
------------------------------------------------------------------------

data Fibre2 : Set where
  leftFibre rightFibre : Fibre2

weight : Fibre2 → ℚ
weight leftFibre = ½
weight rightFibre = ½

fibreMass : ℚ
fibreMass = weight leftFibre + weight rightFibre

fibreMassIsOne : fibreMass ≡ 1ℚ
fibreMassIsOne = solve-∀

module FibreSystem {Base : Set} where

  FinePoint : Set
  FinePoint = Base × Fibre2

  π : FinePoint → Base
  π = proj₁

  CoarseObservable : Set
  CoarseObservable = Base → ℚ

  FineObservable : Set
  FineObservable = FinePoint → ℚ

  pullback : CoarseObservable → FineObservable
  pullback f (y , side) = f y

  average : FineObservable → CoarseObservable
  average g y =
    weight leftFibre * g (y , leftFibre)
    + weight rightFibre * g (y , rightFibre)

  halfDouble : ∀ q → ½ * q + ½ * q ≡ q
  halfDouble = solve-∀

  averagePullback :
    (f : CoarseObservable) (y : Base) →
    average (pullback f) y ≡ f y
  averagePullback f y = halfDouble (f y)

  -- P = pi^* pi_* in this finite model.
  coarseProjection : FineObservable → FineObservable
  coarseProjection g = pullback (average g)

  projectionIdempotentScalar : ∀ a b →
    ½ * (½ * a + ½ * b) + ½ * (½ * a + ½ * b)
    ≡ ½ * a + ½ * b
  projectionIdempotentScalar = solve-∀

  projectionIdempotent :
    (g : FineObservable) (x : FinePoint) →
    coarseProjection (coarseProjection g) x ≡ coarseProjection g x
  projectionIdempotent g (y , leftFibre) =
    projectionIdempotentScalar
      (g (y , leftFibre))
      (g (y , rightFibre))
  projectionIdempotent g (y , rightFibre) =
    projectionIdempotentScalar
      (g (y , leftFibre))
      (g (y , rightFibre))

  -- Q is retained explicitly for the next orthogonality layer.
  fineResidual : FineObservable → FineObservable
  fineResidual g x = g x - coarseProjection g x

  coarsePlusResidual :
    (g : FineObservable) (x : FinePoint) →
    coarseProjection g x + fineResidual g x ≡ g x
  coarsePlusResidual g x = solve-∀

------------------------------------------------------------------------
-- Claim scope.
--
-- These are constructive finite equalities.  They model the normalization
-- hypothesis mu_y(pi^-1(y)) = 1 and its algebraic consequences.  They do not
-- assert existence of a disintegration for an arbitrary measurable map.
------------------------------------------------------------------------

record NormalizedFibreClaimScope : Set where
  constructor normalizedFibreClaimScope
  field
    finiteProbabilityMassConstructed : Bool
    finiteProbabilityMassConstructedIsTrue :
      finiteProbabilityMassConstructed ≡ true

    arbitraryRokhlinDisintegrationConstructed : Bool
    arbitraryRokhlinDisintegrationConstructedIsFalse :
      arbitraryRokhlinDisintegrationConstructed ≡ false

canonicalNormalizedFibreClaimScope : NormalizedFibreClaimScope
canonicalNormalizedFibreClaimScope =
  normalizedFibreClaimScope true refl false refl
