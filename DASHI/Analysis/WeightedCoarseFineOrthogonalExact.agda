module DASHI.Analysis.WeightedCoarseFineOrthogonalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Vladimir I. Bogachev, "Measure Theory", Springer, 2007.
-- DOI: 10.1007/978-3-540-34514-5.
--
-- Stephane G. Mallat,
-- "A Theory for Multiresolution Signal Decomposition: The Wavelet
-- Representation", IEEE TPAMI 11(7), 1989, 674-693.
-- DOI: 10.1109/34.192463.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite probability-fibre model from
-- NormalizedFibreAveragingExact with exact weighted-inner-product identities.
-- Pullback and fibre averaging are adjoint in this finite model; hence the
-- induced coarse operator is self-adjoint and idempotent.  The coarse and
-- residual components are therefore exactly orthogonal fibre by fibre.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Analysis.NormalizedFibreAveragingExact as N

module WeightedFibreSystem {Base : Set} where

  FinePoint : Set
  FinePoint = Base × N.Fibre2

  CoarseObservable : Set
  CoarseObservable = Base → ℚ

  FineObservable : Set
  FineObservable = FinePoint → ℚ

  pullback : CoarseObservable → FineObservable
  pullback f (y , side) = f y

  average : FineObservable → CoarseObservable
  average g y =
    ½ * g (y , N.leftFibre) + ½ * g (y , N.rightFibre)

  P : FineObservable → FineObservable
  P g = pullback (average g)

  Q : FineObservable → FineObservable
  Q g x = g x - P g x

  coarseInnerAt : Base → CoarseObservable → CoarseObservable → ℚ
  coarseInnerAt y f g = f y * g y

  fineInnerAt : Base → FineObservable → FineObservable → ℚ
  fineInnerAt y f g =
    ½ * (f (y , N.leftFibre) * g (y , N.leftFibre))
    + ½ * (f (y , N.rightFibre) * g (y , N.rightFibre))

  -- A = U* in the finite weighted model.
  pullbackAverageAdjoint :
    (y : Base) (f : CoarseObservable) (g : FineObservable) →
    fineInnerAt y (pullback f) g
    ≡ coarseInnerAt y f (average g)
  pullbackAverageAdjoint y f g = solve-∀

  averagePullback :
    (y : Base) (f : CoarseObservable) →
    average (pullback f) y ≡ f y
  averagePullback y f = solve-∀

  projectionIdempotent :
    (g : FineObservable) (x : FinePoint) →
    P (P g) x ≡ P g x
  projectionIdempotent g (y , N.leftFibre) = solve-∀
  projectionIdempotent g (y , N.rightFibre) = solve-∀

  -- Self-adjointness of P is the stronger Hilbert-style fact that does not
  -- follow merely from the equation P^2=P.
  projectionSelfAdjoint :
    (y : Base) (f g : FineObservable) →
    fineInnerAt y (P f) g ≡ fineInnerAt y f (P g)
  projectionSelfAdjoint y f g = solve-∀

  coarsePlusResidual :
    (g : FineObservable) (x : FinePoint) →
    P g x + Q g x ≡ g x
  coarsePlusResidual g x = solve-∀

  averageResidualIsZero :
    (y : Base) (g : FineObservable) →
    average (Q g) y ≡ 0ℚ
  averageResidualIsZero y g = solve-∀

  projectionKillsResidual :
    (g : FineObservable) (x : FinePoint) →
    P (Q g) x ≡ 0ℚ
  projectionKillsResidual g (y , N.leftFibre) = solve-∀
  projectionKillsResidual g (y , N.rightFibre) = solve-∀

  residualKillsProjection :
    (g : FineObservable) (x : FinePoint) →
    Q (P g) x ≡ 0ℚ
  residualKillsProjection g (y , N.leftFibre) = solve-∀
  residualKillsProjection g (y , N.rightFibre) = solve-∀

  projectionResidualOrthogonal :
    (y : Base) (g : FineObservable) →
    fineInnerAt y (P g) (Q g) ≡ 0ℚ
  projectionResidualOrthogonal y g = solve-∀

  residualProjectionOrthogonal :
    (y : Base) (g : FineObservable) →
    fineInnerAt y (Q g) (P g) ≡ 0ℚ
  residualProjectionOrthogonal y g = solve-∀

  ----------------------------------------------------------------------
  -- Exact decomposition-level "glasses" involution.
  --
  -- We do NOT infer an automorphism J of the entire fine-observable space.
  -- What is constructed without extra hypotheses is the involution exchanging
  -- the already-proved coarse and residual coordinates.
  ----------------------------------------------------------------------

  Decomposition : Set
  Decomposition = FineObservable × FineObservable

  decompose : FineObservable → Decomposition
  decompose g = P g , Q g

  glassesSwap : Decomposition → Decomposition
  glassesSwap (coarse , residual) = residual , coarse

  glassesSwapInvolutive :
    (d : Decomposition) → glassesSwap (glassesSwap d) ≡ d
  glassesSwapInvolutive (coarse , residual) = refl

  glassesSwapExchangesCoarseResidual :
    (g : FineObservable) →
    glassesSwap (decompose g) ≡ (Q g , P g)
  glassesSwapExchangesCoarseResidual g = refl

record WeightedOrthogonalClaimScope : Set where
  constructor weightedOrthogonalClaimScope
  field
    finiteAdjointAndOrthogonalSplitConstructed : Bool
    finiteAdjointAndOrthogonalSplitConstructedIsTrue :
      finiteAdjointAndOrthogonalSplitConstructed ≡ true

    arbitraryHilbertDisintegrationConstructed : Bool
    arbitraryHilbertDisintegrationConstructedIsFalse :
      arbitraryHilbertDisintegrationConstructed ≡ false

    globalGlassesAutomorphismConstructed : Bool
    globalGlassesAutomorphismConstructedIsFalse :
      globalGlassesAutomorphismConstructed ≡ false

canonicalWeightedOrthogonalClaimScope : WeightedOrthogonalClaimScope
canonicalWeightedOrthogonalClaimScope =
  weightedOrthogonalClaimScope true refl false refl false refl
