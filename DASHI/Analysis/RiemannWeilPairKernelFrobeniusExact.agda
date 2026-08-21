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
    p q r s

------------------------------------------------------------------------
-- Exact interference ledger.
--
-- The sign-indefinite part is not mysterious: it is exactly the two mixed
-- channels q=a.d and r=b.c.  Define
--
--   P = p^2+s^2,
--   N = q^2+r^2.
--
-- Then
--
--   pairBlockCrossCore + N = P,
--
-- and, after the S/H rewrite,
--
--   Re(S^2+H^2) + 2N = 2P.
--
-- Thus any analytic almost-orthogonality theorem only has to dominate the
-- aggregate mixed-channel budget N.  This is the exact algebraic loss socket.
------------------------------------------------------------------------

positiveAlignedChannelEnergy : PairCrossMoments → ℤ
positiveAlignedChannelEnergy x = square (ac x) + square (bd x)

mixedChannelInterferenceEnergy : PairCrossMoments → ℤ
mixedChannelInterferenceEnergy x = square (ad x) + square (bc x)

pairCrossCorePlusMixedEnergyIsAlignedEnergy :
  (x : PairCrossMoments) →
  pairBlockCrossCore x + mixedChannelInterferenceEnergy x
    ≡ positiveAlignedChannelEnergy x
pairCrossCorePlusMixedEnergyIsAlignedEnergy (pairCrossMoments p q r s) =
  solve 4
    (λ p q r s →
      ((((p :* p) :- (q :* q)) :- (r :* r)) :+ (s :* s))
        :+ ((q :* q) :+ (r :* r))
      := (p :* p) :+ (s :* s))
    refl
    p q r s

holomorphicHermitianPlusTwiceMixedIsTwiceAligned :
  (x : PairCrossMoments) →
  (holomorphicSquareReal x + hermitianSquareReal x)
    + (+ 2) * mixedChannelInterferenceEnergy x
    ≡ (+ 2) * positiveAlignedChannelEnergy x
holomorphicHermitianPlusTwiceMixedIsTwiceAligned (pairCrossMoments p q r s) =
  solve 4
    (λ p q r s →
      ((((p :- s) :* (p :- s)) :- ((q :+ r) :* (q :+ r)))
        :+
        (((p :+ s) :* (p :+ s)) :- ((r :- q) :* (r :- q))))
        :+ (con (+ 2) :* ((q :* q) :+ (r :* r)))
      := con (+ 2) :* ((p :* p) :+ (s :* s)))
    refl
    p q r s

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

mixedEnergyVanishesOnOrthogonalDiagonal :
  (A B : ℤ) →
  mixedChannelInterferenceEnergy (diagonalMoments A B) ≡ (+ 0)
mixedEnergyVanishesOnOrthogonalDiagonal A B = refl

------------------------------------------------------------------------
-- Interference obstruction.
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

negativeWitnessMixedEnergyIsOne :
  mixedChannelInterferenceEnergy negativeInterferenceWitness ≡ (+ 1)
negativeWitnessMixedEnergyIsOne = refl

negativeWitnessAlignedEnergyIsZero :
  positiveAlignedChannelEnergy negativeInterferenceWitness ≡ (+ 0)
negativeWitnessAlignedEnergyIsZero = refl

------------------------------------------------------------------------
-- Frontier contract.
------------------------------------------------------------------------

record PairKernelInterferenceAdapter : Set₁ where
  field
    AnalyticPair : Set
    diagonalHermitianExcess : AnalyticPair → ℤ
    offDiagonalMixedChannelBudget : AnalyticPair → AnalyticPair → ℤ
    arithmeticFrobeniusControl : ℤ

record PairKernelFrobeniusBoundary : Set where
  field
    pairwiseKernelIdentityConstructed : Bool
    hermitianKernelLocatedInsideFrobenius : Bool
    exactMixedChannelLossDecompositionConstructed : Bool
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
  ; exactMixedChannelLossDecompositionConstructed = true
  ; negativeInterferenceWitnessConstructed = true
  ; complexPhiKernelIdentificationProvedHere = false
  ; almostOrthogonalityBoundProvedHere = false
  ; diagonalExcessDominatesInterferenceHere = false
  ; weightedTransverseMomentBoundProvedHere = false
  ; riemannHypothesisProvedHere = false
  }
