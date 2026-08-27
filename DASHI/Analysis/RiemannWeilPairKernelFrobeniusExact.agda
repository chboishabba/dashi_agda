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
-- For u=a+i b and v=c+i d define
--
--   S = u^T v              (holomorphic/bilinear kernel),
--   H = u^T conjugate(v)   (Hermitian kernel),
--
-- and p=a.c, q=a.d, r=b.c, s=b.d.  Then
--
--   Re S = p-s,   Im S = q+r,
--   Re H = p+s,   Im H = r-q.
--
-- The nonlinear Frobenius cross term already contains both S and H.  The
-- only sign-indefinite loss is N_uv=q^2+r^2.  This version also makes explicit
-- the sharper kernel reduction
--
--   (Im S)^2 + (Im H)^2 = 2 N_uv,
--
-- so after complex Poisson identifies S/H with difference/sum Phi-kernels,
-- G2 becomes a kernel-decay/summability problem rather than an opaque vector
-- interference problem.
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
-- NEW EXACT G2 REDUCTION.
--
-- The mixed vector channels are exactly half the combined imaginary energy of
-- the S/H kernels:
--
--   (q+r)^2 + (r-q)^2 = 2(q^2+r^2).
--
-- Therefore an analytic bound on Im S and Im H immediately bounds the entire
-- mixed interference budget.  No separate vector-space observable is needed.
------------------------------------------------------------------------

imaginaryKernelEnergy : PairCrossMoments → ℤ
imaginaryKernelEnergy x =
  square (holomorphicImag x) + square (hermitianImag x)

imaginaryKernelEnergyIsTwiceMixedInterference :
  (x : PairCrossMoments) →
  imaginaryKernelEnergy x
    ≡ (+ 2) * mixedChannelInterferenceEnergy x
imaginaryKernelEnergyIsTwiceMixedInterference
  (pairCrossMoments p q r s) =
  solve 2
    (λ q r →
      (((q :+ r) :* (q :+ r)) :+ ((r :- q) :* (r :- q)))
      := con (+ 2) :* ((q :* q) :+ (r :* r)))
    refl
    q r

realKernelEnergy : PairCrossMoments → ℤ
realKernelEnergy x =
  square (holomorphicReal x) + square (hermitianReal x)

realKernelEnergyIsTwiceAlignedEnergy :
  (x : PairCrossMoments) →
  realKernelEnergy x
    ≡ (+ 2) * positiveAlignedChannelEnergy x
realKernelEnergyIsTwiceAlignedEnergy
  (pairCrossMoments p q r s) =
  solve 2
    (λ p s →
      (((p :- s) :* (p :- s)) :+ ((p :+ s) :* (p :+ s)))
      := con (+ 2) :* ((p :* p) :+ (s :* s)))
    refl
    p s

record MixedInterferenceKernelReductionAdapter : Set₁ where
  field
    AnalyticPair : Set
    pairMoments : AnalyticPair → AnalyticPair → PairCrossMoments
    holomorphicDifferenceKernel : AnalyticPair → AnalyticPair → ℤ
    hermitianSumKernel : AnalyticPair → AnalyticPair → ℤ
    identifyHolomorphicImag :
      (u v : AnalyticPair) →
      holomorphicImag (pairMoments u v)
        ≡ holomorphicDifferenceKernel u v
    identifyHermitianImag :
      (u v : AnalyticPair) →
      hermitianImag (pairMoments u v)
        ≡ hermitianSumKernel u v

------------------------------------------------------------------------
-- Diagonal specialization u=v with a.b=0.
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
    imaginaryKernelExactlyTwiceMixedLoss : Bool
    mixedLossReducedToDifferenceAndSumKernelControl : Bool
    negativeInterferenceWitnessConstructed : Bool
    complexPhiKernelIdentificationProvedHere : Bool
    offDiagonalPhiKernelSummabilityProvedHere : Bool
    almostOrthogonalityBoundProvedHere : Bool
    diagonalExcessDominatesInterferenceHere : Bool
    weightedTransverseMomentBoundProvedHere : Bool
    riemannHypothesisProvedHere : Bool

pairKernelFrobeniusBoundary : PairKernelFrobeniusBoundary
pairKernelFrobeniusBoundary = record
  { pairwiseKernelIdentityConstructed = true
  ; hermitianKernelLocatedInsideFrobenius = true
  ; exactMixedChannelLossDecompositionConstructed = true
  ; imaginaryKernelExactlyTwiceMixedLoss = true
  ; mixedLossReducedToDifferenceAndSumKernelControl = true
  ; negativeInterferenceWitnessConstructed = true
  ; complexPhiKernelIdentificationProvedHere = false
  ; offDiagonalPhiKernelSummabilityProvedHere = false
  ; almostOrthogonalityBoundProvedHere = false
  ; diagonalExcessDominatesInterferenceHere = false
  ; weightedTransverseMomentBoundProvedHere = false
  ; riemannHypothesisProvedHere = false
  }
