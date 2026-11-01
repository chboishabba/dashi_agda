module DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- SOURCE NORMALIZATION
--
-- Equations (0.18), (0.20), and (2.15) use
--
--       1/g_k^2 = 1/g_{k+1}^2 + beta_{k+1}.
--
-- Thus, with u_k = 1/g_k^2,
--
--       u_k = u_{k+1} + beta_{k+1}.
--
-- This orientation is important: k increases toward the coarser/terminal
-- lattice, so positive beta means u grows when the recursion is followed
-- BACKWARDS toward the ultraviolet.  A formula with a positive increment in
-- the k -> k+1 direction silently reverses Bałaban's indexing.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact finite telescope and the two-sided linear tube.  If every
-- source beta coefficient lies in [betaLower,betaUpper], then
--
--   n betaLower <= u_0-u_n <= n betaUpper.
--
-- This is the algebraic content of CMP109 Theorem 2 / equation (0.31); the hard
-- analytic frontier is now precisely the uniform positive enclosure of the
-- history-dependent beta coefficients.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

betaPartial : (Nat → ℚ) → Nat → ℚ
betaPartial beta zero = 0ℚ
betaPartial beta (suc depth) = betaPartial beta depth + beta (suc depth)

record SourceNormalizedCouplingTrajectory : Set₁ where
  field
    inverseCoupling beta : Nat → ℚ
    sourceRecurrence : ∀ depth →
      inverseCoupling depth
      ≡ inverseCoupling (suc depth) + beta (suc depth)

open SourceNormalizedCouplingTrajectory public

sourceRecurrenceTelescope :
  (trajectory : SourceNormalizedCouplingTrajectory) →
  ∀ depth →
  inverseCoupling trajectory zero
  ≡ inverseCoupling trajectory depth + betaPartial (beta trajectory) depth
sourceRecurrenceTelescope trajectory zero =
  sym (ℚP.+-identityʳ (inverseCoupling trajectory zero))
sourceRecurrenceTelescope trajectory (suc depth) =
  trans
    (sourceRecurrenceTelescope trajectory depth)
    (trans
      (cong
        (λ selected → selected + betaPartial (beta trajectory) depth)
        (sourceRecurrence trajectory depth))
      (ℚRing.solve-∀
        (inverseCoupling trajectory (suc depth))
        (beta trajectory (suc depth))
        (betaPartial (beta trajectory) depth)))

record UniformBetaEnclosure
    (trajectory : SourceNormalizedCouplingTrajectory) : Set where
  field
    betaLower betaUpper : ℚ
    betaLowerNonnegative : 0ℚ ≤ betaLower
    betaLowerBelow : ∀ step → betaLower ≤ beta trajectory (suc step)
    betaBelowUpper : ∀ step → beta trajectory (suc step) ≤ betaUpper

open UniformBetaEnclosure public

betaPartialLower :
  ∀ {trajectory}
    (bounds : UniformBetaEnclosure trajectory) →
  ∀ depth →
  Sums.natAsRational depth * betaLower bounds
  ≤ betaPartial (beta trajectory) depth
betaPartialLower bounds zero = ℚP.≤-refl
betaPartialLower {trajectory} bounds (suc depth) =
  let
    induction = betaPartialLower bounds depth
    step = betaLowerBelow bounds depth
    summed = ℚP.+-mono-≤ induction step
  in
  subst
    (λ lower → lower
      ≤ betaPartial (beta trajectory) depth
        + beta trajectory (suc depth))
    (ℚRing.solve-∀
      (Sums.natAsRational depth) (betaLower bounds))
    summed

betaPartialUpper :
  ∀ {trajectory}
    (bounds : UniformBetaEnclosure trajectory) →
  ∀ depth →
  betaPartial (beta trajectory) depth
  ≤ Sums.natAsRational depth * betaUpper bounds
betaPartialUpper bounds zero = ℚP.≤-refl
betaPartialUpper {trajectory} bounds (suc depth) =
  let
    induction = betaPartialUpper bounds depth
    step = betaBelowUpper bounds depth
    summed = ℚP.+-mono-≤ induction step
  in
  subst
    (λ upper →
      betaPartial (beta trajectory) depth
        + beta trajectory (suc depth) ≤ upper)
    (ℚRing.solve-∀
      (Sums.natAsRational depth) (betaUpper bounds))
    summed

inverseCouplingDifferenceIsBetaPartial :
  (trajectory : SourceNormalizedCouplingTrajectory) →
  ∀ depth →
  inverseCoupling trajectory zero - inverseCoupling trajectory depth
  ≡ betaPartial (beta trajectory) depth
inverseCouplingDifferenceIsBetaPartial trajectory depth =
  trans
    (cong (_- inverseCoupling trajectory depth)
      (sourceRecurrenceTelescope trajectory depth))
    (ℚRing.solve-∀
      (inverseCoupling trajectory depth)
      (betaPartial (beta trajectory) depth))

sourceNormalizedTwoSidedUVTube :
  ∀ {trajectory}
    (bounds : UniformBetaEnclosure trajectory) →
  ∀ depth →
  (Sums.natAsRational depth * betaLower bounds
    ≤ inverseCoupling trajectory zero - inverseCoupling trajectory depth)
  ×
  (inverseCoupling trajectory zero - inverseCoupling trajectory depth
    ≤ Sums.natAsRational depth * betaUpper bounds)
sourceNormalizedTwoSidedUVTube {trajectory} bounds depth =
  subst
    (λ selected →
      (Sums.natAsRational depth * betaLower bounds ≤ selected)
      × (selected ≤ Sums.natAsRational depth * betaUpper bounds))
    (sym (inverseCouplingDifferenceIsBetaPartial trajectory depth))
    (betaPartialLower bounds depth , betaPartialUpper bounds depth)

ym4SourceNormalizedCouplingTelescopeLevel : ProofLevel
ym4SourceNormalizedCouplingTelescopeLevel = machineChecked

ym4SourceNormalizedTwoSidedUVTubeLevel : ProofLevel
ym4SourceNormalizedTwoSidedUVTubeLevel = machineChecked

-- CMP109 itself explicitly defers the proof of the required positive uniform
-- beta enclosure to a separate perturbative analysis.  This remains the real
-- RG1e analytic producer and must not be replaced by the continuum one-loop
-- coefficient as an axiom.
ym4PhysicalHistoryDependentBetaEnclosureLevel : ProofLevel
ym4PhysicalHistoryDependentBetaEnclosureLevel = conditional
