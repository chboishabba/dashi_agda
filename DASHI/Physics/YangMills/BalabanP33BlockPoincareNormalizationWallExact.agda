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
-- (2) Fluctuation low-mode wall.  The quotient Rayleigh estimate is kept in
--     the exact cross-multiplied form
--
--       (2M) numerator <= 9 normSq.
--
--     Together with normSq <= CP numerator it forces
--
--       2M <= 9 CP,
--
--     i.e. CP >= 2M/9, without introducing a variable rational denominator.
--
-- Both are one-sided falsifiers for one unscaled normalization.  Neither says
-- that interacting-Hessian coercivity, weighted block norms, or rescaled
-- averages fail.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (Σ; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; _/_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation using (¬_)

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

    leftCommuted : left * factor ≡ factor * left
    leftCommuted = ℚRing.solve []

    rightCommuted : right * factor ≡ factor * right
    rightCommuted = ℚRing.solve []

    rightReduced : left * factor ≤ factor * right
    rightReduced =
      subst
        (λ upper → left * factor ≤ upper)
        rightCommuted
        bound

    commuted : factor * left ≤ factor * right
    commuted =
      subst
        (λ lower → lower ≤ factor * right)
        leftCommuted
        rightReduced
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

nine : ℚ
nine = + 9 / 1

fluctuationSquareModeForcesLinearCrossBound :
  ∀ twoM normSq numerator poincareConstant →
  0ℚ ≤ twoM →
  0ℚ < normSq →
  0ℚ ≤ poincareConstant →
  twoM * numerator ≤ nine * normSq →
  normSq ≤ poincareConstant * numerator →
  twoM ≤ nine * poincareConstant
fluctuationSquareModeForcesLinearCrossBound
    twoM normSq numerator poincareConstant
    twoMNonnegative normPositive constantNonnegative
    rayleighCrossBound poincare =
  let
    instance
      twoMNN : NonNegative twoM
      twoMNN = ℚ.nonNegative twoMNonnegative
      constantNN : NonNegative poincareConstant
      constantNN = ℚ.nonNegative constantNonnegative

    leftStep :
      twoM * normSq
      ≤ twoM * (poincareConstant * numerator)
    leftStep =
      ℚP.*-monoˡ-≤-nonNeg twoM poincare

    rayleighScaled :
      poincareConstant * (twoM * numerator)
      ≤ poincareConstant * (nine * normSq)
    rayleighScaled =
      ℚP.*-monoˡ-≤-nonNeg
        poincareConstant rayleighCrossBound

    leftRearranged :
      twoM * (poincareConstant * numerator)
      ≡ poincareConstant * (twoM * numerator)
    leftRearranged = ℚRing.solve []

    rightRearranged :
      poincareConstant * (nine * normSq)
      ≡ (nine * poincareConstant) * normSq
    rightRearranged = ℚRing.solve []

    rightReduced :
      poincareConstant * (twoM * numerator)
      ≤ (nine * poincareConstant) * normSq
    rightReduced =
      subst
        (λ upper →
          poincareConstant * (twoM * numerator) ≤ upper)
        rightRearranged
        rayleighScaled

    middleStep :
      twoM * (poincareConstant * numerator)
      ≤ (nine * poincareConstant) * normSq
    middleStep =
      subst
        (λ lower → lower ≤ (nine * poincareConstant) * normSq)
        (sym leftRearranged)
        rightReduced

    productBound :
      twoM * normSq
      ≤ (nine * poincareConstant) * normSq
    productBound = ℚP.≤-trans leftStep middleStep
  in
  cancelPositiveRightFactor
    twoM (nine * poincareConstant) normSq
    normPositive productBound

------------------------------------------------------------------------
-- Generic quantifier-level wall.
------------------------------------------------------------------------

UnboundedAbove : ∀ {Scale : Set} → (Scale → ℚ) → Set
UnboundedAbove {Scale} lower =
  ∀ bound → Σ Scale (λ scale → bound < lower scale)

NoUniformUpperBound : ∀ {Scale : Set} → (Scale → ℚ) → Set
NoUniformUpperBound lower =
  ¬ (Σ ℚ (λ uniform → ∀ scale → lower scale ≤ uniform))

unboundedLowerBoundsRefuteUniformConstant :
  ∀ {Scale : Set} (lower : Scale → ℚ) →
  UnboundedAbove lower →
  NoUniformUpperBound lower
unboundedLowerBoundsRefuteUniformConstant lower unbounded
    (uniform , dominates) with unbounded uniform
... | scale , uniformBelowScale =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans uniformBelowScale (dominates scale))

constantSectorUniformGateFalse :
  ∀ {Scale : Set}
    (scaleSquared : Scale → ℚ) →
  UnboundedAbove scaleSquared →
  NoUniformUpperBound scaleSquared
constantSectorUniformGateFalse =
  unboundedLowerBoundsRefuteUniformConstant

fluctuationSectorUniformGateFalse :
  ∀ {Scale : Set}
    (linearLowerBound : Scale → ℚ) →
  UnboundedAbove linearLowerBound →
  NoUniformUpperBound linearLowerBound
fluctuationSectorUniformGateFalse =
  unboundedLowerBoundsRefuteUniformConstant

------------------------------------------------------------------------
-- One exact visible cross-multiplied witness: M=100 forces 200 <= 9 CP.
------------------------------------------------------------------------

squareModeAtM100ForcesCrossBound :
  ∀ normSq numerator poincareConstant →
  0ℚ < normSq →
  0ℚ ≤ poincareConstant →
  (+ 200 / 1) * numerator ≤ nine * normSq →
  normSq ≤ poincareConstant * numerator →
  (+ 200 / 1) ≤ nine * poincareConstant
squareModeAtM100ForcesCrossBound
    normSq numerator poincareConstant
    normPositive constantNonnegative rayleigh poincare =
  fluctuationSquareModeForcesLinearCrossBound
    (+ 200 / 1) normSq numerator poincareConstant
    (ℚP.nonNegative⁻¹ (+ 200 / 1))
    normPositive constantNonnegative rayleigh poincare

blockPoincareConstantSectorWallLevel : ProofLevel
blockPoincareConstantSectorWallLevel = machineChecked

blockPoincareFluctuationLowModeWallLevel : ProofLevel
blockPoincareFluctuationLowModeWallLevel = machineChecked

blockPoincareUniformQuantifierWallLevel : ProofLevel
blockPoincareUniformQuantifierWallLevel = machineChecked

interactingHessianRouteUnaffectedLevel : ProofLevel
interactingHessianRouteUnaffectedLevel = machineChecked
