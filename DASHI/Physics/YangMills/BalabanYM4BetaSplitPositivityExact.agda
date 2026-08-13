module DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact where

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
-- gauge-theory coupling",
-- Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- DASHI CONTRIBUTION
--
-- Formalize the source-faithful RG1e positivity strategy without inserting the
-- continuum one-loop coefficient as an axiom.  CMP109's finite-lattice beta is
-- split into the Gaussian-normalization contribution betaZ and the nonlinear
-- fluctuation contribution betaInt.  If
--
--       b* <= betaZ <= B*
--       -b*/2 <= betaInt <= b*/2,
--
-- then the full history-dependent coefficient obeys
--
--       b*/2 <= beta <= B* + b*/2.
--
-- Combined with the already-proved source-oriented recurrence telescope this
-- gives the finite UV tube immediately.  The remaining analytic calculation is
-- exactly the uniform Gaussian determinant lower bound and nonlinear remainder
-- estimate on the literal CMP109 carrier/history domain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

half : ℚ → ℚ
half value = value / + 2

record FiniteLatticeBetaSplit
    (trajectory : Flow.SourceNormalizedCouplingTrajectory) : Set₁ where
  field
    betaZ betaInt : Agda.Builtin.Nat.Nat → ℚ
    splitExact : ∀ step →
      Flow.beta trajectory (Agda.Builtin.Nat.suc step)
      ≡ betaZ step + betaInt step

    gaussianLower gaussianUpper : ℚ
    gaussianLowerNonnegative : 0ℚ ≤ gaussianLower

    betaZLower : ∀ step → gaussianLower ≤ betaZ step
    betaZUpper : ∀ step → betaZ step ≤ gaussianUpper

    interactionLower : ∀ step →
      0ℚ - half gaussianLower ≤ betaInt step
    interactionUpper : ∀ step →
      betaInt step ≤ half gaussianLower

open FiniteLatticeBetaSplit public

fullBetaLowerHalfGaussian :
  ∀ {trajectory}
    (split : FiniteLatticeBetaSplit trajectory) step →
  half (gaussianLower split)
  ≤ Flow.beta trajectory (Agda.Builtin.Nat.suc step)
fullBetaLowerHalfGaussian split step =
  subst
    (λ selected → half (gaussianLower split) ≤ selected)
    (sym (splitExact split step))
    (subst
      (λ lower → lower
        ≤ betaZ split step + betaInt split step)
      (ℚRing.solve-∀ (gaussianLower split))
      (ℚP.+-mono-≤
        (betaZLower split step)
        (interactionLower split step)))

fullBetaUpperGaussianPlusHalf :
  ∀ {trajectory}
    (split : FiniteLatticeBetaSplit trajectory) step →
  Flow.beta trajectory (Agda.Builtin.Nat.suc step)
  ≤ gaussianUpper split + half (gaussianLower split)
fullBetaUpperGaussianPlusHalf split step =
  subst
    (λ selected → selected
      ≤ gaussianUpper split + half (gaussianLower split))
    (sym (splitExact split step))
    (ℚP.+-mono-≤
      (betaZUpper split step)
      (interactionUpper split step))

halfGaussianNonnegative :
  ∀ {trajectory}
    (split : FiniteLatticeBetaSplit trajectory) →
  0ℚ ≤ half (gaussianLower split)
halfGaussianNonnegative split =
  subst
    (λ selected → 0ℚ ≤ selected)
    (ℚRing.solve-∀ (gaussianLower split))
    (let
      halfNonnegative : 0ℚ ≤ (+ 1 / 2)
      halfNonnegative = ℚP.nonNegative⁻¹ (+ 1 / 2)
    in
    ℚP.*-mono-≤
      (gaussianLowerNonnegative split) halfNonnegative)

betaSplitProducesUniformEnclosure :
  ∀ {trajectory}
    (split : FiniteLatticeBetaSplit trajectory) →
  Flow.UniformBetaEnclosure trajectory
betaSplitProducesUniformEnclosure split = record
  { Flow.UniformBetaEnclosure.betaLower = half (gaussianLower split)
  ; Flow.UniformBetaEnclosure.betaUpper =
      gaussianUpper split + half (gaussianLower split)
  ; Flow.UniformBetaEnclosure.betaLowerNonnegative =
      halfGaussianNonnegative split
  ; Flow.UniformBetaEnclosure.betaLowerBelow =
      fullBetaLowerHalfGaussian split
  ; Flow.UniformBetaEnclosure.betaBelowUpper =
      fullBetaUpperGaussianPlusHalf split
  }

betaSplitProducesUVTube :
  ∀ {trajectory}
    (split : FiniteLatticeBetaSplit trajectory) depth →
  (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.natAsRational depth
      * half (gaussianLower split)
    ≤ Flow.inverseCoupling trajectory Agda.Builtin.Nat.zero
      - Flow.inverseCoupling trajectory depth)
  ×
  (Flow.inverseCoupling trajectory Agda.Builtin.Nat.zero
      - Flow.inverseCoupling trajectory depth
    ≤ DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.natAsRational depth
      * (gaussianUpper split + half (gaussianLower split)))
betaSplitProducesUVTube split =
  Flow.sourceNormalizedTwoSidedUVTube
    (betaSplitProducesUniformEnclosure split)
  where
  open import Agda.Builtin.Nat
  open import Data.Product.Base using (_×_)
  open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact

yM4BetaSplitPositivityLevel : ProofLevel
yM4BetaSplitPositivityLevel = machineChecked

yM4GaussianDeterminantPositiveEnclosureLevel : ProofLevel
yM4GaussianDeterminantPositiveEnclosureLevel = conditional

yM4NonlinearBetaRemainderHalfGapLevel : ProofLevel
yM4NonlinearBetaRemainderHalfGapLevel = conditional
