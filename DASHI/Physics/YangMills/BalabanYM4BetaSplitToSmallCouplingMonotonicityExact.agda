module DASHI.Physics.YangMills.BalabanYM4BetaSplitToSmallCouplingMonotonicityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger Dashen and David J. Gross,
-- "Relationship between lattice and continuum definitions of the
-- gauge-theory coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Separate the hypothesis actually needed by the published complete-density
-- theorem from the stronger asymptotic-freedom tube.  The existing finite-
-- lattice split
--
--       beta = betaZ + betaInt
--
-- proves beta >= gaussianLower/2 whenever the Gaussian term has a nonnegative
-- lower bound and the interaction costs at most half of it.  Therefore the same
-- split already gives beta>=0, hence finite inverse-coupling monotonicity and
-- backwards threshold propagation.
--
-- The upper beta bound and a STRICTLY positive gaussianLower are unnecessary
-- for this order-theoretic consequence.  This is useful because Bałaban's
-- CMP122 Theorem 1 only assumes an all-scale sufficiently-small coupling
-- history; it does not require us to establish the full two-sided Theorem-2
-- asymptotic tube merely to reuse the complete-density theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (0ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact as Step
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as Finite
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split

betaSplitGivesNonnegativeBeta :
  ∀ {trajectory}
    (split : Split.FiniteLatticeBetaSplit trajectory) step →
  0ℚ ≤ Flow.beta trajectory (suc step)
betaSplitGivesNonnegativeBeta split step =
  ℚP.≤-trans
    (Split.halfGaussianNonnegative split)
    (Split.fullBetaLowerHalfGaussian split step)

betaSplitAsNonnegativeTrajectory :
  ∀ {trajectory} →
  Split.FiniteLatticeBetaSplit trajectory →
  Step.NonnegativeBetaTrajectory trajectory
betaSplitAsNonnegativeTrajectory split = record
  { Step.NonnegativeBetaTrajectory.betaNonnegative =
      betaSplitGivesNonnegativeBeta split
  }

betaSplitFiniteInverseMonotone :
  ∀ {trajectory}
    (split : Split.FiniteLatticeBetaSplit trajectory)
    start gap →
  Flow.inverseCoupling trajectory (Finite.advance start gap)
  ≤ Flow.inverseCoupling trajectory start
betaSplitFiniteInverseMonotone split =
  Finite.inverseCouplingFiniteMonotone
    (betaSplitAsNonnegativeTrajectory split)

betaSplitPropagatesInverseThresholdBackwards :
  ∀ {trajectory}
    (split : Split.FiniteLatticeBetaSplit trajectory)
    threshold start gap →
  threshold ≤ Flow.inverseCoupling trajectory (Finite.advance start gap) →
  threshold ≤ Flow.inverseCoupling trajectory start
betaSplitPropagatesInverseThresholdBackwards split =
  Finite.inverseThresholdPropagatesBackwards
    (betaSplitAsNonnegativeTrajectory split)

ym4BetaSplitNonnegativeTrajectoryLevel : ProofLevel
ym4BetaSplitNonnegativeTrajectoryLevel = machineChecked

ym4BetaSplitFiniteSmallCouplingMonotonicityLevel : ProofLevel
ym4BetaSplitFiniteSmallCouplingMonotonicityLevel = machineChecked
