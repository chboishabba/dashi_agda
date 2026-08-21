module DASHI.Analysis.RiemannComplexPoissonPairEnergyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / SOURCE-NATIVE MOTIVATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026).
-- DOI: 10.48550/arXiv.2608.13637.
--
-- MACHINE-CHECKED COMPANION SOURCE
--
-- Anthropic, `zeta-23-lean` (2026), especially:
--   * Zeta23/Defs.lean
--   * Zeta23/Poisson.lean
--   * Zeta23/ZeroSide.lean
--
-- The companion source defines
--
--   gamma_rho = (rho - 1/2)/i = gamma - i alpha,
--   v_rho(k)  = phiHat(gamma_rho - tau_k),
--
-- and proves the real-argument Gabor/Poisson identity
--
--   sum_k phiHat(tau-tau_k) phiHat(tau'-tau_k)
--     = L Phi(tau-tau').
--
-- Its Poisson module explicitly notes that the complex continuation mentioned
-- in the paper is not needed by the published proof.  If that continuation is
-- established for z and conj(z), then for z = gamma - i alpha one obtains the
-- distance-sensitive full-grid norm identity
--
--   sum_k |phiHat(z-tau_k)|^2
--     = L Phi(z-conj z)
--     = L Phi(-2 i alpha).
--
-- Since phi is real and even,
--
--   Phi(-2 i alpha)
--     = integral phi(u)^2 exp(2 alpha u) du
--     = integral phi(u)^2 cosh(2 alpha u) du,
--
-- so the full-grid norm is minimal at alpha = 0 and its excess is quadratic
-- to second order (indeed cosh x - 1 >= x^2/2).  This is the first genuinely
-- displacement-sensitive producer found in the present tranche.
--
-- IMPORTANT BOUNDARY
--
-- This Agda module does NOT claim the analytic complex-continuation theorem or
-- the finite-grid/tail estimate.  It closes the exact local linear-algebra
-- consequence once the complex-Poisson norm information is supplied:
--
--   constant complex-square sum + increased Hermitian norm
--       => positive imaginary-channel energy
--       => an exact positive Frobenius excess of the paired hyperbolic block.
--
-- It also proves a second no-factor theorem: the holomorphic/bilinear baseline
-- seen by the diagonal Weil/Gabor square cannot by itself reconstruct the
-- Hermitian norm defect.  Hence the new producer must transport genuinely
-- additional Hermitian information back to the arithmetic side rather than
-- merely repackage the existing trace identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

record PairEnergyLedger : Set where
  constructor pairEnergyLedger
  field
    multiplicityPredecessor : Nat
    baselineSquareSum : Nat
    imaginaryChannelEnergy : Nat

open PairEnergyLedger public

multiplicity : PairEnergyLedger → Nat
multiplicity q = multiplicityPredecessor q + 1

realChannelEnergy : PairEnergyLedger → Nat
realChannelEnergy q = baselineSquareSum q + imaginaryChannelEnergy q

fullGridHermitianEnergy : PairEnergyLedger → Nat
fullGridHermitianEnergy q = realChannelEnergy q + imaginaryChannelEnergy q

criticalHermitianBaseline : PairEnergyLedger → Nat
criticalHermitianBaseline q = baselineSquareSum q

pairBlockFrobeniusSquared : PairEnergyLedger → Nat
pairBlockFrobeniusSquared q =
  4 * multiplicity q * multiplicity q *
    ( realChannelEnergy q * realChannelEnergy q
    + imaginaryChannelEnergy q * imaginaryChannelEnergy q
    )

criticalBlockFrobeniusSquared : PairEnergyLedger → Nat
criticalBlockFrobeniusSquared q =
  4 * multiplicity q * multiplicity q *
    (baselineSquareSum q * baselineSquareSum q)

pairBlockFrobeniusExcess : PairEnergyLedger → Nat
pairBlockFrobeniusExcess q =
  8 * multiplicity q * multiplicity q *
    imaginaryChannelEnergy q * realChannelEnergy q

fullGridEnergyDecomposition :
  (q : PairEnergyLedger) →
  fullGridHermitianEnergy q
    ≡ baselineSquareSum q + 2 * imaginaryChannelEnergy q
fullGridEnergyDecomposition (pairEnergyLedger m c b) =
  solve 2
    (λ c b → (c :+ b) :+ b := c :+ (con 2 :* b))
    refl
    c b

pairBlockFrobeniusDecomposition :
  (q : PairEnergyLedger) →
  pairBlockFrobeniusSquared q
    ≡ criticalBlockFrobeniusSquared q + pairBlockFrobeniusExcess q
pairBlockFrobeniusDecomposition (pairEnergyLedger m c b) =
  solve 3
    (λ m c b →
      (con 4 :* (m :+ con 1) :* (m :+ con 1) :*
        (((c :+ b) :* (c :+ b)) :+ (b :* b)))
      :=
      (con 4 :* (m :+ con 1) :* (m :+ con 1) :* (c :* c))
      :+
      (con 8 :* (m :+ con 1) :* (m :+ con 1) :* b :* (c :+ b)))
    refl
    m c b

criticalPairHasZeroFrobeniusExcess :
  (m c : Nat) →
  pairBlockFrobeniusExcess (pairEnergyLedger m c zero) ≡ zero
criticalPairHasZeroFrobeniusExcess m c =
  solve 2
    (λ m c →
      con 8 :* (m :+ con 1) :* (m :+ con 1) :* con 0 :* (c :+ con 0)
      := con 0)
    refl
    m c

criticalPairRecoversBaselineFrobenius :
  (m c : Nat) →
  pairBlockFrobeniusSquared (pairEnergyLedger m c zero)
    ≡ criticalBlockFrobeniusSquared (pairEnergyLedger m c zero)
criticalPairRecoversBaselineFrobenius m c =
  pairBlockFrobeniusDecomposition (pairEnergyLedger m c zero)

nearPairEnergy : PairEnergyLedger
nearPairEnergy = pairEnergyLedger 0 1 1

farPairEnergy : PairEnergyLedger
farPairEnergy = pairEnergyLedger 0 1 3

nearPairFullGridEnergyIsThree :
  fullGridHermitianEnergy nearPairEnergy ≡ 3
nearPairFullGridEnergyIsThree = refl

farPairFullGridEnergyIsSeven :
  fullGridHermitianEnergy farPairEnergy ≡ 7
farPairFullGridEnergyIsSeven = refl

nearPairFrobeniusIsTwenty :
  pairBlockFrobeniusSquared nearPairEnergy ≡ 20
nearPairFrobeniusIsTwenty = refl

farPairFrobeniusIsHundred :
  pairBlockFrobeniusSquared farPairEnergy ≡ 100
farPairFrobeniusIsHundred = refl

nearPairExcessIsSixteen :
  pairBlockFrobeniusExcess nearPairEnergy ≡ 16
nearPairExcessIsSixteen = refl

farPairExcessIsNinetySix :
  pairBlockFrobeniusExcess farPairEnergy ≡ 96
farPairExcessIsNinetySix = refl

nearFarHolomorphicBaselinesCollide :
  baselineSquareSum nearPairEnergy ≡ baselineSquareSum farPairEnergy
nearFarHolomorphicBaselinesCollide = refl

threeIsNotSeven : 3 ≡ 7 → ⊥
threeIsNotSeven ()

holomorphicBaselineCannotDetermineHermitianEnergy :
  (decode : Nat → Nat) →
  ((q : PairEnergyLedger) →
    decode (baselineSquareSum q) ≡ fullGridHermitianEnergy q) →
  ⊥
holomorphicBaselineCannotDetermineHermitianEnergy decode rec =
  threeIsNotSeven
    (trans
      (sym nearPairFullGridEnergyIsThree)
      (trans
        (sym (rec nearPairEnergy))
        (trans
          (rec farPairEnergy)
          farPairFullGridEnergyIsSeven)))

record ComplexPoissonCoercivityAdapter : Set₁ where
  field
    AnalyticPair : Set
    squaredTransverseDisplacement : AnalyticPair → Nat
    fullGridNormExcess : AnalyticPair → Nat
    coerciveWeight : Nat
    weightedSquaredDisplacement : AnalyticPair → Nat
    weightedSquaredDisplacementDefinition :
      (x : AnalyticPair) →
      weightedSquaredDisplacement x
        ≡ coerciveWeight * squaredTransverseDisplacement x

record FiniteCompressionTransferAdapter : Set₁ where
  field
    AnalyticPair : Set
    fullGridDefect : AnalyticPair → Nat
    finiteCompressionDefect : AnalyticPair → Nat
    interferenceBudget : AnalyticPair → Nat

record HermitianArithmeticTransportAdapter : Set₁ where
  field
    AnalyticPair : Set
    hermitianDefect : AnalyticPair → Nat
    arithmeticObservable : AnalyticPair → Nat
    retainedResidual : AnalyticPair → Nat

record ComplexPoissonPairEnergyBoundary : Set where
  field
    localPairFrobeniusIdentityConstructed : Bool
    traceBlindButEnergySensitiveWitnessConstructed : Bool
    holomorphicToHermitianFactorizationRefuted : Bool
    complexPoissonContinuationProvedHere : Bool
    alphaSquaredCoshCoercivityProvedHere : Bool
    finiteGridRetentionProvedHere : Bool
    crossPairInterferenceControlledHere : Bool
    hermitianArithmeticTransportConstructedHere : Bool
    globalWeightedTransverseMomentBoundProved : Bool
    riemannHypothesisProvedHere : Bool

complexPoissonPairEnergyBoundary : ComplexPoissonPairEnergyBoundary
complexPoissonPairEnergyBoundary = record
  { localPairFrobeniusIdentityConstructed = true
  ; traceBlindButEnergySensitiveWitnessConstructed = true
  ; holomorphicToHermitianFactorizationRefuted = true
  ; complexPoissonContinuationProvedHere = false
  ; alphaSquaredCoshCoercivityProvedHere = false
  ; finiteGridRetentionProvedHere = false
  ; crossPairInterferenceControlledHere = false
  ; hermitianArithmeticTransportConstructedHere = false
  ; globalWeightedTransverseMomentBoundProved = false
  ; riemannHypothesisProvedHere = false
  }
