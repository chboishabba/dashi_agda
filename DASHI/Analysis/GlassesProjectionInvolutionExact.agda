module DASHI.Analysis.GlassesProjectionInvolutionExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Construct, rather than merely suggest, the finite "glasses inversion" from
-- the Round-8 discussion.  On each two-point probability fibre the coarse
-- projector P averages the two coordinates and Q = I-P is the antisymmetric
-- residual.  The rational involution J(a,b) = (a,-b) exchanges these two
-- one-dimensional subspaces exactly:
--
--                     J P J = Q   and   J Q J = P.
--
-- No square roots are needed.  The corresponding inversion defect is therefore
-- exactly zero in this concrete finite model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; ½; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Analysis.NormalizedFibreAveragingExact as N

module GlassesSystem {Base : Set} where

  FinePoint : Set
  FinePoint = Base × N.Fibre2

  FineObservable : Set
  FineObservable = FinePoint → ℚ

  P : FineObservable → FineObservable
  P g (y , side) =
    ½ * g (y , N.leftFibre) + ½ * g (y , N.rightFibre)

  Q : FineObservable → FineObservable
  Q g x = g x - P g x

  J : FineObservable → FineObservable
  J g (y , N.leftFibre) = g (y , N.leftFibre)
  J g (y , N.rightFibre) = - g (y , N.rightFibre)

  JInvolutive :
    (g : FineObservable) (x : FinePoint) → J (J g) x ≡ g x
  JInvolutive g (y , N.leftFibre) = refl
  JInvolutive g (y , N.rightFibre) = solve-∀

  JPJIsQ :
    (g : FineObservable) (x : FinePoint) →
    J (P (J g)) x ≡ Q g x
  JPJIsQ g (y , N.leftFibre) = solve-∀
  JPJIsQ g (y , N.rightFibre) = solve-∀

  JQJIsP :
    (g : FineObservable) (x : FinePoint) →
    J (Q (J g)) x ≡ P g x
  JQJIsP g (y , N.leftFibre) = solve-∀
  JQJIsP g (y , N.rightFibre) = solve-∀

  -- Omega = J P J - Q is identically zero.
  inversionDefect : FineObservable → FineObservable
  inversionDefect g x = J (P (J g)) x - Q g x

  inversionDefectIsZero :
    (g : FineObservable) (x : FinePoint) →
    inversionDefect g x ≡ 0ℚ
  inversionDefectIsZero g (y , N.leftFibre) = solve-∀
  inversionDefectIsZero g (y , N.rightFibre) = solve-∀

  -- The same carrier supports two complementary readings without either being
  -- declared an absolute semantic truth: J changes the decomposition basis.
  exchangesProjectors :
    (g : FineObservable) (x : FinePoint) →
    J (P (J g)) x ≡ Q g x
    × J (Q (J g)) x ≡ P g x
  exchangesProjectors g x = JPJIsQ g x , JQJIsP g x

record GlassesInvolutionClaimScope : Set where
  constructor glassesInvolutionClaimScope
  field
    globalFiniteFibreInvolutionConstructed : Bool
    globalFiniteFibreInvolutionConstructedIsTrue :
      globalFiniteFibreInvolutionConstructed ≡ true

    exactProjectorExchangeConstructed : Bool
    exactProjectorExchangeConstructedIsTrue :
      exactProjectorExchangeConstructed ≡ true

    ideologicalTruthOperatorConstructed : Bool
    ideologicalTruthOperatorConstructedIsFalse :
      ideologicalTruthOperatorConstructed ≡ false

canonicalGlassesInvolutionClaimScope : GlassesInvolutionClaimScope
canonicalGlassesInvolutionClaimScope =
  glassesInvolutionClaimScope true refl true refl false refl
