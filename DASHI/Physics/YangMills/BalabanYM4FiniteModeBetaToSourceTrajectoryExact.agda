module DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger Dashen and David J. Gross,
-- "Relationship between lattice and continuum definitions of the
-- gauge-theory coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- DASHI CONTRIBUTION
--
-- Consume the per-mode Gaussian and per-atom interaction estimates directly
-- at the source recurrence.  The small-coupling history only needs beta>=0,
-- so no auxiliary beta upper bound is introduced here.
--
-- For each step the previous module proves
--
--   (1/2) b_k <= betaZ_k + betaInt_k,
--
-- from finite local enclosures.  If b_k>=0 and the literal source recurrence
-- coefficient is exactly this sum, beta_{k+1} is nonnegative.  This produces
-- the existing NonnegativeBetaTrajectory consumed by the terminal inverse-
-- coupling threshold argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4SourceCouplingSmallnessPropagationExact as Source

record FiniteModeBetaTrajectoryData
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (Mode Atom : Set) : Set₁ where
  field
    gaussianAt : Nat → Local.FiniteGaussianModeEnclosure Mode
    interactionAt : Nat → Local.FiniteInteractionAtomEnclosure Atom
    gamma : Nat → ℚ.ℚ

    sourceBetaSplitExact : ∀ step →
      Flow.beta trajectory (suc step)
      ≡ Local.betaZ (gaussianAt step) + Local.betaInt (interactionAt step)

    gaussianLowerNonnegative : ∀ step →
      0ℚ ≤ Local.computedGaussianLower (gaussianAt step)

    interactionCouplingNonnegative : ∀ step →
      0ℚ ≤ Local.coupling (interactionAt step)
    gammaNonnegative : ∀ step → 0ℚ ≤ gamma step
    interactionCouplingBelowGamma : ∀ step →
      Local.coupling (interactionAt step) ≤ gamma step

    interactionCoefficientTotalNonnegative : ∀ step →
      0ℚ ≤ Local.interactionCoefficientTotal (interactionAt step)

    quarticAbsorption : ∀ step →
      Local.interactionCoefficientTotal (interactionAt step)
        * Local.power4 (gamma step)
      ≤ Local.half * Local.computedGaussianLower (gaussianAt step)

open FiniteModeBetaTrajectoryData public

halfGaussianLowerNonnegative :
  ∀ {trajectory Mode Atom}
    (dataSet : FiniteModeBetaTrajectoryData trajectory Mode Atom) step →
  0ℚ ≤ Local.half * Local.computedGaussianLower (gaussianAt dataSet step)
halfGaussianLowerNonnegative dataSet step =
  Norm.scaleNonnegative
    Local.half
    (ℚP.nonNegative⁻¹ Local.half)
    (gaussianLowerNonnegative dataSet step)

sourceBetaNonnegativeFromFiniteModes :
  ∀ {trajectory Mode Atom}
    (dataSet : FiniteModeBetaTrajectoryData trajectory Mode Atom) step →
  0ℚ ≤ Flow.beta trajectory (suc step)
sourceBetaNonnegativeFromFiniteModes {trajectory} dataSet step =
  let
    localLower = Local.betaSplitLowerAfterQuarticAbsorption
      (gaussianAt dataSet step)
      (interactionAt dataSet step)
      (gamma dataSet step)
      (interactionCouplingNonnegative dataSet step)
      (gammaNonnegative dataSet step)
      (interactionCouplingBelowGamma dataSet step)
      (interactionCoefficientTotalNonnegative dataSet step)
      (quarticAbsorption dataSet step)

    zeroToHalf = halfGaussianLowerNonnegative dataSet step
    zeroToSplit = ℚP.≤-trans zeroToHalf localLower
  in
  subst
    (λ upper → 0ℚ ≤ upper)
    (sym (sourceBetaSplitExact dataSet step))
    zeroToSplit

finiteModesAsNonnegativeBetaTrajectory :
  ∀ {trajectory Mode Atom} →
  FiniteModeBetaTrajectoryData trajectory Mode Atom →
  Source.NonnegativeBetaTrajectory trajectory
finiteModesAsNonnegativeBetaTrajectory dataSet = record
  { Source.NonnegativeBetaTrajectory.betaNonnegative =
      sourceBetaNonnegativeFromFiniteModes dataSet
  }

yM4FiniteModeBetaToSourceTrajectoryLevel : ProofLevel
yM4FiniteModeBetaToSourceTrajectoryLevel = machineChecked

-- Only the literal mode/atom evaluation and exact source split remain; no
-- global beta-positivity field is accepted by this producer.
yM4LiteralFiniteModeSourceSplitInstantiationLevel : ProofLevel
yM4LiteralFiniteModeSourceSplitInstantiationLevel = conditional
