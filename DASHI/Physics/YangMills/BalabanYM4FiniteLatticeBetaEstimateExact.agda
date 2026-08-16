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
-- Put the finite-lattice beta estimate in the exact form needed by the
-- complete-density small-coupling history.  The relevant coefficient is split
-- at the literal localized plaquette projector:
--
--       beta = beta_Z + beta_int,
--
-- where beta_Z is the gauge/ghost one-loop plaquette coefficient and beta_int
-- is the total quartic localized remainder.  If the finite Brillouin-zone
-- certificate gives beta_Z >= z_* > 0 and the physical quartic estimate gives
--
--       |beta_int| <= C_int g^4 <= z_*/2,
--
-- then beta >= z_*/2 > 0.  Unlike the older beta-split interface, the theorem
-- below also carries the actual g^4 remainder production and proves the
-- half-gap from a single small-coupling compatibility inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split

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

    -- This is the literal quartic small-field remainder estimate after the
    -- plaquette coefficient projector.
    interactionQuartic :
      ∣ betaInt ∣ ≤ interactionConstant * fourthPower coupling

    -- One common small-coupling budget; no independent beta remainder input.
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
  where
    open import Relation.Binary.PropositionalEquality using (sym)

finiteLatticeBetaNonnegative :
  ∀ dataSet → 0ℚ ≤ beta dataSet
finiteLatticeBetaNonnegative dataSet =
  let
    halfZNN : 0ℚ ≤ half * zLower dataSet
    halfZNN = ℚP.*-mono-≤
      (ℚP.nonNegative⁻¹ half)
      (zLowerNonnegative dataSet)
      ℚP.≤-refl ℚP.≤-refl
  in
  ℚP.≤-trans halfZNN (finiteLatticeBetaLowerHalfGap dataSet)

finiteLatticeBetaSplitForExistingHistory :
  ∀ dataSet →
  Split.BetaSplitBounds
    (beta dataSet)
    (betaZ dataSet)
    (betaInt dataSet)
    (zLower dataSet)
    (betaZ dataSet)
finiteLatticeBetaSplitForExistingHistory dataSet = record
  { Split.BetaSplitBounds.betaSplitExact = betaSplitExact dataSet
  ; Split.BetaSplitBounds.gaussianLower = gaussianLower dataSet
  ; Split.BetaSplitBounds.gaussianUpper = ℚP.≤-refl
  ; Split.BetaSplitBounds.interactionLower = interactionSignedLower dataSet
  ; Split.BetaSplitBounds.interactionUpper =
      ℚP.≤-trans
        (ℚP.p≤∣p∣ (betaInt dataSet))
        (interactionBelowHalfGaussianGap dataSet)
  }

ym4FiniteLatticeBetaQuarticEstimateLevel : ProofLevel
ym4FiniteLatticeBetaQuarticEstimateLevel = machineChecked

ym4FiniteLatticeBetaHalfGapLevel : ProofLevel
ym4FiniteLatticeBetaHalfGapLevel = machineChecked

ym4FiniteLatticeBetaNonnegativeLevel : ProofLevel
ym4FiniteLatticeBetaNonnegativeLevel = machineChecked
