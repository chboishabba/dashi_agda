module DASHI.Physics.YangMills.BalabanYM4FiniteLatticeBetaEstimateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Dashen and David J. Gross,
-- "Relationship between Lattice and Continuum Definitions of the Gauge-Theory
-- Coupling", Physical Review D 23 (1981), 2340--2344.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Finite-lattice beta estimate at one literal RG step.  The one-loop Gaussian
-- coefficient and the signed quartic interaction remainder are kept as the
-- actual two summands.  A physical quartic estimate
--
--       |beta_int| <= C_int g^4
--
-- and one common small-coupling compatibility
--
--       C_int g^4 <= z_*/2 <= beta_Z/2
--
-- give beta >= z_*/2 >= 0.  The all-scale `FiniteLatticeBetaSplit` is built in
-- the separate trajectory module, so this file does not invent a second split
-- record incompatible with the repository API.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

fourthPower : ℚ → ℚ
fourthPower g = (g * g) * (g * g)

record FiniteLatticeBetaEstimate : Set where
  field
    beta betaZ betaInt coupling interactionConstant zLower : ℚ
    betaSplitExact : beta ≡ betaZ + betaInt
    couplingNonnegative : 0ℚ ≤ coupling
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    zLowerNonnegative : 0ℚ ≤ zLower
    gaussianLower : zLower ≤ betaZ
    interactionQuartic :
      ∣ betaInt ∣ ≤ interactionConstant * fourthPower coupling
    quarticFitsHalfGaussianGap :
      interactionConstant * fourthPower coupling ≤ half * zLower

open FiniteLatticeBetaEstimate public

interactionBelowHalfGaussianGap :
  ∀ dataSet → ∣ betaInt dataSet ∣ ≤ half * zLower dataSet
interactionBelowHalfGaussianGap dataSet =
  ℚP.≤-trans
    (interactionQuartic dataSet)
    (quarticFitsHalfGaussianGap dataSet)

interactionSignedLower :
  ∀ dataSet →
  0ℚ - (half * zLower dataSet) ≤ betaInt dataSet
interactionSignedLower dataSet =
  let
    absBound = interactionBelowHalfGaussianGap dataSet
    negAbsBelow : 0ℚ - ∣ betaInt dataSet ∣ ≤ betaInt dataSet
    negAbsBelow = ℚP.-∣p∣≤p (betaInt dataSet)
    reflected :
      0ℚ - (half * zLower dataSet)
      ≤ 0ℚ - ∣ betaInt dataSet ∣
    reflected = ℚP.neg-antimono-≤ absBound
  in
  ℚP.≤-trans reflected negAbsBelow

interactionSignedUpper :
  ∀ dataSet → betaInt dataSet ≤ half * zLower dataSet
interactionSignedUpper dataSet =
  ℚP.≤-trans
    (ℚP.p≤∣p∣ (betaInt dataSet))
    (interactionBelowHalfGaussianGap dataSet)

finiteLatticeBetaLowerHalfGap :
  ∀ dataSet → half * zLower dataSet ≤ beta dataSet
finiteLatticeBetaLowerHalfGap dataSet =
  let
    summed :
      zLower dataSet + (0ℚ - half * zLower dataSet)
      ≤ betaZ dataSet + betaInt dataSet
    summed = ℚP.+-mono-≤
      (gaussianLower dataSet)
      (interactionSignedLower dataSet)

    leftExact :
      zLower dataSet + (0ℚ - half * zLower dataSet)
      ≡ half * zLower dataSet
    leftExact = ℚRing.solve-∀ (zLower dataSet)
  in
  subst
    (λ lower → lower ≤ beta dataSet)
    leftExact
    (subst
      (λ upper →
        zLower dataSet + (0ℚ - half * zLower dataSet) ≤ upper)
      (sym (betaSplitExact dataSet))
      summed)

finiteLatticeBetaNonnegative :
  ∀ dataSet → 0ℚ ≤ beta dataSet
finiteLatticeBetaNonnegative dataSet =
  let
    halfZNN : 0ℚ ≤ half * zLower dataSet
    halfZNN = Norm.scaleNonnegative half
      (ℚP.nonNegative⁻¹ half)
      (zLowerNonnegative dataSet)
  in
  ℚP.≤-trans halfZNN (finiteLatticeBetaLowerHalfGap dataSet)

ym4FiniteLatticeBetaQuarticEstimateLevel : ProofLevel
ym4FiniteLatticeBetaQuarticEstimateLevel = machineChecked

ym4FiniteLatticeBetaHalfGapLevel : ProofLevel
ym4FiniteLatticeBetaHalfGapLevel = machineChecked

ym4FiniteLatticeBetaNonnegativeLevel : ProofLevel
ym4FiniteLatticeBetaNonnegativeLevel = machineChecked
