module DASHI.Physics.YangMills.BalabanP33BlockPoincareNormalizationWallExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01211042.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- STRESS-TEST COMPARISON ONLY
--
-- Lluis Eriksson,
-- "The Volume-Uniform Poincare Walls: Machine-Checked Obstructions for Flat
-- and Fluctuation-Sector Block-Poincare Routes to Combes-Thomas Coercivity in
-- Lattice Yang-Mills", ai.viXra:2607.0042 (2026), no DOI assigned.
--
-- The ai.viXra manuscript is not used as an authority.  The two scalar
-- implications below are proved independently in Agda.  They record exactly
-- which normalization hypotheses cause the obstruction and therefore prevent
-- accidental transfer of the claim to a rescaled block map or to the full
-- interacting Wilson Hessian.
--
-- DASHI CONTRIBUTION
--
-- (1) Constant-sector wall.  If the fine/coarse norm identity on a constant
--     mode is
--
--       fineNorm = L^2 coarseNorm
--
--     in four dimensions, then any Poincare inequality
--
--       fineNorm <= CP coarseNorm
--
--     forces L^2 <= CP.
--
-- (2) Fluctuation low-mode wall.  If a nonzero fluctuation mode has Rayleigh
--     numerator at most (9/(2M)) times its norm, then any quotient Poincare
--     inequality forces 2M/9 <= CP.
--
-- Both are one-sided falsifiers for one unscaled normalization.  Neither says
-- that interacting-Hessian coercivity, weighted block norms, or rescaled
-- averages fail.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Positive-factor cancellation in the exact form used by both walls.
------------------------------------------------------------------------

cancelPositiveRightFactor :
  ∀ left right factor →
  0ℚ < factor →
  left * factor ≤ right * factor →
  left ≤ right
cancelPositiveRightFactor left right factor factorPositive bound =
  let
    instance
      factorPositiveInstance : Positive factor
      factorPositiveInstance = ℚ.positive factorPositive

    commuted : factor * left ≤ factor * right
    commuted =
      subst
        (λ lower → lower ≤ factor * right)
        (ℚRing.solve-∀ left factor)
        (subst
          (λ upper → left * factor ≤ upper)
          (sym (ℚRing.solve-∀ right factor))
          bound)
  in
  ℚP.*-cancelˡ-≤-pos factor commuted

------------------------------------------------------------------------
-- Wall 1: constant sector for the unscaled four-dimensional line integral.
------------------------------------------------------------------------

constantSectorForcesScaleSquared :
  ∀ scaleSquared coarseNorm fineNorm poincareConstant →
  0ℚ < coarseNorm →
  fineNorm ≡ scaleSquared * coarseNorm →
  fineNorm ≤ poincareConstant * coarseNorm →
  scaleSquared ≤ poincareConstant
constantSectorForcesScaleSquared
    scaleSquared coarseNorm fineNorm poincareConstant
    coarsePositive normalization poincare =
  cancelPositiveRightFactor
    scaleSquared poincareConstant coarseNorm coarsePositive
    (subst
      (λ selected → selected ≤ poincareConstant * coarseNorm)
      normalization
      poincare)

fourDimensionalUnscaledConstantWall :
  ∀ blockScale coarseNorm fineNorm poincareConstant →
  0ℚ < coarseNorm →
  fineNorm ≡ (blockScale * blockScale) * coarseNorm →
  fineNorm ≤ poincareConstant * coarseNorm →
  blockScale * blockScale ≤ poincareConstant
fourDimensionalUnscaledConstantWall =
  constantSectorForcesScaleSquared

------------------------------------------------------------------------
-- Wall 2: fluctuation-sector square-wave Rayleigh estimate.
------------------------------------------------------------------------

quotientLowModeForcesReciprocalRayleighConstant :
  ∀ normSq numerator poincareConstant rayleighCoefficient →
  0ℚ < normSq →
  0ℚ ≤ poincareConstant →
  numerator ≤ rayleighCoefficient * normSq →
  normSq ≤ poincareConstant * numerator →
  1ℚ ≤ poincareConstant * rayleighCoefficient
quotientLowModeForcesReciprocalRayleighConstant
    normSq numerator poincareConstant rayleighCoefficient
    normPositive constantNonnegative numeratorBound poincare =
  let
    instance
      constantNN : NonNegative poincareConstant
      constantNN = ℚ.nonNegative constantNonnegative

    chained :
      normSq
      ≤ poincareConstant * (rayleighCoefficient * normSq)
    chained =
      ℚP.≤-trans
        poincare
        (ℚP.*-monoˡ-≤-nonNeg poincareConstant numeratorBound)

    factored :
      1ℚ * normSq
      ≤ (poincareConstant * rayleighCoefficient) * normSq
    factored =
      subst
        (λ lower →
          lower
          ≤ (poincareConstant * rayleighCoefficient) * normSq)
        (ℚRing.solve-∀ normSq)
        (subst
          (λ upper → normSq ≤ upper)
          (sym
            (ℚRing.solve-∀
              poincareConstant rayleighCoefficient normSq))
          chained)
  in
  cancelPositiveRightFactor
    1ℚ (poincareConstant * rayleighCoefficient)
    normSq normPositive factored

fluctuationSquareModeForcesLinearConstant :
  ∀ twoM normSq numerator poincareConstant →
  0ℚ < twoM →
  0ℚ < normSq →
  0ℚ ≤ poincareConstant →
  0ℚ ≤ twoM / (+ 9 / 1) →
  numerator ≤ ((+ 9 / 1) / twoM) * normSq →
  normSq ≤ poincareConstant * numerator →
  twoM / (+ 9 / 1) ≤ poincareConstant
fluctuationSquareModeForcesLinearConstant
    twoM normSq numerator poincareConstant
    twoMPositive normPositive constantNonnegative scaleNonnegative
    numeratorBound poincare =
  let
    reciprocalRayleigh :
      1ℚ ≤ poincareConstant * ((+ 9 / 1) / twoM)
    reciprocalRayleigh =
      quotientLowModeForcesReciprocalRayleighConstant
        normSq numerator poincareConstant ((+ 9 / 1) / twoM)
        normPositive constantNonnegative numeratorBound poincare

    instance
      scaleNN : NonNegative (twoM / (+ 9 / 1))
      scaleNN = ℚ.nonNegative scaleNonnegative

    scaled :
      (twoM / (+ 9 / 1)) * 1ℚ
      ≤ (twoM / (+ 9 / 1))
          * (poincareConstant * ((+ 9 / 1) / twoM))
    scaled =
      ℚP.*-monoˡ-≤-nonNeg
        (twoM / (+ 9 / 1)) reciprocalRayleigh
  in
  subst
    (λ lower → lower ≤ poincareConstant)
    (ℚRing.solve-∀ twoM)
    (subst
      (λ upper →
        (twoM / (+ 9 / 1)) * 1ℚ ≤ upper)
      (sym (ℚRing.solve-∀ twoM poincareConstant))
      scaled)

------------------------------------------------------------------------
-- One exact visible witness: M=100 forces CP >= 200/9.
------------------------------------------------------------------------

squareModeScale200Over9 : ℚ
squareModeScale200Over9 = + 200 / 9

squareModeAtM100Forces :
  ∀ normSq numerator poincareConstant →
  0ℚ < normSq →
  0ℚ ≤ poincareConstant →
  numerator ≤ (+ 9 / 200) * normSq →
  normSq ≤ poincareConstant * numerator →
  squareModeScale200Over9 ≤ poincareConstant
squareModeAtM100Forces
    normSq numerator poincareConstant
    normPositive constantNonnegative numeratorBound poincare =
  fluctuationSquareModeForcesLinearConstant
    (+ 200 / 1) normSq numerator poincareConstant
    (ℚP.positive⁻¹ (+ 200 / 1))
    normPositive constantNonnegative
    (ℚP.nonNegative⁻¹ squareModeScale200Over9)
    (subst
      (λ coefficient → numerator ≤ coefficient * normSq)
      (ℚRing.solve [])
      numeratorBound)
    poincare

blockPoincareConstantSectorWallLevel : ProofLevel
blockPoincareConstantSectorWallLevel = machineChecked

blockPoincareFluctuationLowModeWallLevel : ProofLevel
blockPoincareFluctuationLowModeWallLevel = machineChecked

interactingHessianRouteUnaffectedLevel : ProofLevel
interactingHessianRouteUnaffectedLevel = machineChecked
