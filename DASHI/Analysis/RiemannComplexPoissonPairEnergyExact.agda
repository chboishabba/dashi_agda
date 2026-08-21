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
-- That is the hard algebraic seam needed before attempting the remaining
-- analytic producer in the paper's actual finite compression.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

------------------------------------------------------------------------
-- Exact pair-energy ledger.
--
-- Write v = a + i b and abbreviate
--
--   A = ||a||^2,
--   B = ||b||^2,
--   C = sum_k v_k^2.
--
-- The complex Poisson continuation at equal arguments predicts C is the same
-- baseline a L^2 as on the critical line.  Since C is real, a.b = 0; hence
-- A - B = C.  We encode that relation subtraction-free as A = C + B.
--
-- The paired real block is 2 m (a a^T - b b^T).  With a.b = 0 its squared
-- Frobenius norm is
--
--   4 m^2 (A^2 + B^2).
--
-- At B = 0 the critical-line baseline is 4 m^2 C^2.  Their difference is
-- exactly
--
--   8 m^2 B A.
--
-- Thus an inverse pair can be trace/signature-blind yet retain a strictly
-- positive second-order residual through B.
------------------------------------------------------------------------

record PairEnergyLedger : Set where
  constructor pairEnergyLedger
  field
    multiplicityPredecessor : Nat
    baselineSquareSum : Nat
    imaginaryChannelEnergy : Nat

open PairEnergyLedger public

multiplicity : PairEnergyLedger → Nat
multiplicity q = suc (multiplicityPredecessor q)

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

------------------------------------------------------------------------
-- Polynomial identities: these are the exact local block calculation.
------------------------------------------------------------------------

fullGridEnergyDecomposition :
  (q : PairEnergyLedger) →
  fullGridHermitianEnergy q
    ≡ baselineSquareSum q + 2 * imaginaryChannelEnergy q
fullGridEnergyDecomposition (pairEnergyLedger m c b) =
  solve 2
    (λ c b → (c :+ b) :+ b := c :+ (con 2 :* b))
    refl

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

criticalPairHasZeroFrobeniusExcess :
  (m c : Nat) →
  pairBlockFrobeniusExcess (pairEnergyLedger m c zero) ≡ zero
criticalPairHasZeroFrobeniusExcess m c = refl

criticalPairRecoversBaselineFrobenius :
  (m c : Nat) →
  pairBlockFrobeniusSquared (pairEnergyLedger m c zero)
    ≡ criticalBlockFrobeniusSquared (pairEnergyLedger m c zero)
criticalPairRecoversBaselineFrobenius m c =
  pairBlockFrobeniusDecomposition (pairEnergyLedger m c zero)

------------------------------------------------------------------------
-- Concrete separating checksum.
--
-- These two blocks have the same multiplicity and same complex-square
-- baseline, hence the same bare hyperbolic signature and trace-type baseline,
-- but different imaginary-channel energies.  The Frobenius residual separates
-- them exactly.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Typed analytic seam.
--
-- The discovered producer needs two analytic promotions before it can feed an
-- RH-strength argument:
--
-- (1) complex Poisson continuation / coercivity:
--       full-grid excess >= const * alpha^2 * secondMoment(phi^2);
--
-- (2) finite-compression transfer:
--       the paper's k=0,...,d-1 compression retains enough of that excess,
--       with cross-pair interference controlled on the prime side.
--
-- Keeping these as named data prevents the exact local algebra above from
-- being mistaken for the still-open global analytic estimate.
------------------------------------------------------------------------

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

record ComplexPoissonPairEnergyBoundary : Set where
  field
    localPairFrobeniusIdentityConstructed : Bool
    traceBlindButEnergySensitiveWitnessConstructed : Bool
    complexPoissonContinuationProvedHere : Bool
    alphaSquaredCoshCoercivityProvedHere : Bool
    finiteGridRetentionProvedHere : Bool
    crossPairInterferenceControlledHere : Bool
    globalWeightedTransverseMomentBoundProved : Bool
    riemannHypothesisProvedHere : Bool

complexPoissonPairEnergyBoundary : ComplexPoissonPairEnergyBoundary
complexPoissonPairEnergyBoundary = record
  { localPairFrobeniusIdentityConstructed = true
  ; traceBlindButEnergySensitiveWitnessConstructed = true
  ; complexPoissonContinuationProvedHere = false
  ; alphaSquaredCoshCoercivityProvedHere = false
  ; finiteGridRetentionProvedHere = false
  ; crossPairInterferenceControlledHere = false
  ; globalWeightedTransverseMomentBoundProved = false
  ; riemannHypothesisProvedHere = false
  }
