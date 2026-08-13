module DASHI.Physics.YangMills.BalabanYM4CouplingSlackTubeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
-- The published complete-density theorem needs the running coupling to remain
-- in a sufficiently small domain.  That requirement is weaker than a sharp
-- two-sided asymptotic-freedom coefficient theorem.  In the source recurrence
-- u_k = u_{k+1} + beta_{k+1}, allow each beta step to undershoot zero by an
-- allocated rational loss.  The cumulative allocated loss gives a rigorous
-- one-sided tube for u=g^-2.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

slackPartial : (Nat → ℚ) → Nat → ℚ
slackPartial slack zero = 0ℚ
slackPartial slack (suc depth) = slackPartial slack depth + slack (suc depth)

record OneSidedBetaSlack
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set where
  field
    slack : Nat → ℚ
    stepLower : ∀ step →
      - slack (suc step) ≤ Flow.beta trajectory (suc step)

open OneSidedBetaSlack public

betaPartialOneSidedLower :
  ∀ {trajectory} (control : OneSidedBetaSlack trajectory) depth →
  - slackPartial (slack control) depth
  ≤ Flow.betaPartial (Flow.beta trajectory) depth
betaPartialOneSidedLower control zero = ℚP.≤-refl
betaPartialOneSidedLower {trajectory} control (suc depth) =
  subst
    (λ lower → lower
      ≤ Flow.betaPartial (Flow.beta trajectory) depth
        + Flow.beta trajectory (suc depth))
    (ℚRing.solve-∀
      (slackPartial (slack control) depth)
      (slack control (suc depth)))
    (ℚP.+-mono-≤
      (betaPartialOneSidedLower control depth)
      (stepLower control depth))

uvInverseCouplingOneSidedTube :
  ∀ {trajectory} (control : OneSidedBetaSlack trajectory) depth →
  Flow.inverseCoupling trajectory depth
    - slackPartial (slack control) depth
  ≤ Flow.inverseCoupling trajectory zero
uvInverseCouplingOneSidedTube {trajectory} control depth =
  let
    shifted = ℚP.+-monoˡ-≤
      (Flow.inverseCoupling trajectory depth)
      (betaPartialOneSidedLower control depth)
  in
  subst
    (λ right →
      Flow.inverseCoupling trajectory depth
        - slackPartial (slack control) depth
      ≤ right)
    (sym (Flow.sourceRecurrenceTelescope trajectory depth))
    (subst
      (λ left → left
        ≤ Flow.inverseCoupling trajectory depth
          + Flow.betaPartial (Flow.beta trajectory) depth)
      (ℚRing.solve-∀
        (Flow.inverseCoupling trajectory depth)
        (slackPartial (slack control) depth))
      shifted)

ym4OneSidedCouplingSlackTubeLevel : ProofLevel
ym4OneSidedCouplingSlackTubeLevel = machineChecked

ym4PhysicalOneSidedBetaSlackProducerLevel : ProofLevel
ym4PhysicalOneSidedBetaSlackProducerLevel = conditional
