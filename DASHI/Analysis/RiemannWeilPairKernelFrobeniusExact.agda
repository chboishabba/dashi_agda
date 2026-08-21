module DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026).
-- DOI: 10.48550/arXiv.2608.13637.
--
-- MACHINE-CHECKED COMPANION
-- Anthropic, `zeta-23-lean` (2026), especially `Zeta23/ZeroSide.lean`
-- and `Zeta23/ZeroSide/RankTraceMult.lean`.
--
-- DASHI CONTRIBUTION
--
-- Make explicit the nonlinear kernel identity hidden when the paper passes
-- from the bilinear zero matrix to its Frobenius square.
--
-- For u=a+i b and v=c+i d define
--
--   S = u^T v              (holomorphic/bilinear kernel),
--   H = u^T conjugate(v)   (Hermitian kernel).
--
-- Writing
--
--   p = a.c,  q = a.d,  r = b.c,  s = b.d,
--
-- gives
--
--   Re S = p-s,   Im S = q+r,
--   Re H = p+s,   Im H = r-q.
--
-- The paired real blocks are
--
--   Q_u = 2m (a a^T - b b^T),
--   Q_v = 2n (c c^T - d d^T),
--
-- and their Frobenius cross term is
--
--   <Q_u,Q_v>_F
--     = 4mn (p^2-q^2-r^2+s^2)
--     = 2mn Re(S^2 + H^2).
--
-- Therefore the displacement-sensitive Hermitian kernel is ALREADY latent in
-- the nonlinear Frobenius quantity estimated on the prime side.  No new linear
-- explicit formula is required merely to make H appear.  The remaining issue
-- is sign/interference control of the off-diagonal pair terms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)

square : ℤ → ℤ
square x = x * x

record PairCrossMoments : Set where
  constructor pairCrossMoments
  field
    ac : ℤ
    ad : ℤ
    bc : ℤ
    bd : ℤ

open PairCrossMoments public

holomorphicReal : PairCrossMoments → ℤ
holomorphicReal x = ac x - bd x

holomorphicImag : PairCrossMoments → ℤ
holomorphicImag x = ad x + bc x

hermitianReal : PairCrossMoments → ℤ
hermitianReal x = ac x + bd x

hermitianImag : PairCrossMoments → ℤ
hermitianImag x = bc x - ad x

realSquare : ℤ → ℤ → ℤ
realSquare re im = square re - square im

holomorphicSquareReal : PairCrossMoments → ℤ
holomorphicSquareReal x = realSquare (holomorphicReal x) (holomorphicImag x)

hermitianSquareReal : PairCrossMoments → ℤ
hermitianSquareReal x = realSquare (hermitianReal x) (hermitianImag x)

pairBlockCrossCore : PairCrossMoments → ℤ
pairBlockCrossCore x =
  square (ac x) - square (ad x) - square (bc x) + square (bd x)

------------------------------------------------------------------------
-- Exact kernel identity.
------------------------------------------------------------------------

holomorphicPlusHermitianSquaresExposePairCrossCore :
  (x : PairCrossMoments) →
  holomorphicSquareReal x + hermitianSquareReal x
    ≡ (+ 2) * pairBlockCrossCore x
holomorphicPlusHermitianSquaresExposePairCrossCore
  (pairCrossMoments p q r s) =
  solve 4
    (λ p q r s →
      (((p :- s) :* (p :- s)) :- ((q :+ r) :* (q :+ r)))
      :+
      (((p :+ s) :* (p :+ s)) :- ((r :- q) :* (r :- q)))
      :=
      con (+ 2) :*
        ((((p :* p) :- (q :* q)) :- (r :* r)) :+ (s :* s)))
    refl

------------------------------------------------------------------------
-- Diagonal specialization u=v with a.b=0.
--
-- p=A=||a||^2, s=B=||b||^2, q=r=0.  Thus
--
--   C = A-B = u^T u,
--   H = A+B = u^T conjugate(u)=||u||^2,
--
-- and C^2 + H^2 = 2(A^2+B^2).
------------------------------------------------------------------------

diagonalMoments : ℤ → ℤ → PairCrossMoments
diagonalMoments A B = pairCrossMoments A (+ 0) (+ 0) B

diagonalHolomorphicReal :
  (A B : ℤ) → holomorphicReal (diagonalMoments A B) ≡ A - B
diagonalHolomorphicReal A B = refl

diagonalHermitianReal :
  (A B : ℤ) → hermitianReal (diagonalMoments A B) ≡ A + B
diagonalHermitianReal A B = refl

diagonalKernelEnergyIdentity :
  (A B : ℤ) →
  square (A - B) + square (A + B)
    ≡ (+ 2) * (square A + square B)
diagonalKernelEnergyIdentity =
  solve 2
    (λ A B →
      ((A :- B) :* (A :- B)) :+ ((A :+ B) :* (A :+ B))
      := con (+ 2) :* ((A :* A) :+ (B :* B)))
    refl

------------------------------------------------------------------------
-- Interference obstruction.
--
-- The Hermitian kernel appearing inside the global Frobenius square is not by
-- itself enough: cross-pair terms can have either sign.  The following exact
-- witness corresponds algebraically to a purely-real channel for one pair and
-- a purely-imaginary aligned channel for another.
------------------------------------------------------------------------

negativeInterferenceWitness : PairCrossMoments
negativeInterferenceWitness = pairCrossMoments (+ 0) (+ 1) (+ 0) (+ 0)

negativeInterferenceCoreIsMinusOne :
  pairBlockCrossCore negativeInterferenceWitness ≡ -[1+ 0 ]
negativeInterferenceCoreIsMinusOne = refl

negativeInterferenceHolomorphicPlusHermitianIsMinusTwo :
  holomorphicSquareReal negativeInterferenceWitness
    + hermitianSquareReal negativeInterferenceWitness
    ≡ -[1+ 1 ]
negativeInterferenceHolomorphicPlusHermitianIsMinusTwo = refl

------------------------------------------------------------------------
-- Frontier contract.
--
-- Since the desired H-kernel is already present in ||Q||_F^2, the missing
-- theorem should be an almost-orthogonality / interference estimate rather
-- than a brand-new explicit formula.  In the analytic setting S and H are
-- expected to be controlled by complex continuations of the same Phi kernel:
--
--   S_rs ~ L Phi(z_r-z_s),
--   H_rs ~ L Phi(z_r-conjugate(z_s)).
--
-- The existing psi-decay, tail and pair-correlation machinery is therefore a
-- plausible source of the needed bound, but no such bound is asserted here.
------------------------------------------------------------------------

record PairKernelInterferenceAdapter : Set₁ where
  field
    AnalyticPair : Set
    diagonalHermitianExcess : AnalyticPair → ℤ
    offDiagonalInterference : AnalyticPair → AnalyticPair → ℤ
    arithmeticFrobeniusControl : ℤ

record PairKernelFrobeniusBoundary : Set where
  field
    pairwiseKernelIdentityConstructed : Bool
    hermitianKernelLocatedInsideFrobenius : Bool
    negativeInterferenceWitnessConstructed : Bool
    complexPhiKernelIdentificationProvedHere : Bool
    almostOrthogonalityBoundProvedHere : Bool
    diagonalExcessDominatesInterferenceHere : Bool
    weightedTransverseMomentBoundProvedHere : Bool
    riemannHypothesisProvedHere : Bool

pairKernelFrobeniusBoundary : PairKernelFrobeniusBoundary
pairKernelFrobeniusBoundary = record
  { pairwiseKernelIdentityConstructed = true
  ; hermitianKernelLocatedInsideFrobenius = true
  ; negativeInterferenceWitnessConstructed = true
  ; complexPhiKernelIdentificationProvedHere = false
  ; almostOrthogonalityBoundProvedHere = false
  ; diagonalExcessDominatesInterferenceHere = false
  ; weightedTransverseMomentBoundProvedHere = false
  ; riemannHypothesisProvedHere = false
  }
