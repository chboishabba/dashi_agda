module DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact where

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
-- DASHI CONTRIBUTION
--
-- Make L3/L4 finite and compositional.  A Gaussian lower bound is built from
-- PER-MODE lower enclosures, not supplied as `betaZ >= b*`.  Likewise the
-- interaction lower bound is built from a finite list of literal interaction
-- atoms, each carrying its O(g^4) coefficient.  The exact finite sums then give
--
--   b_* <= beta_Z,
--   - C_beta g^4 <= beta_int.
--
-- A separate exact quartic-monotonicity theorem transports g<=gamma into the
-- uniform small-coupling condition C_beta gamma^4 <= b_*/2 and hence
--
--   b_*/2 <= beta_Z + beta_int.
--
-- The remaining physical work is therefore the actual finite Brillouin-mode
-- and interaction-atom enclosure, not this order algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

oneLoopSU2Factor half : ℚ
oneLoopSU2Factor = + 11 / 12
half = + 1 / 2

sumMonotone :
  ∀ {A : Set} (indices : List A) (lower upper : A → ℚ) →
  (∀ index → lower index ≤ upper index) →
  Sums.sumRational indices lower ≤ Sums.sumRational indices upper
sumMonotone [] lower upper pointwise = ℚP.≤-refl
sumMonotone (index ∷ indices) lower upper pointwise =
  ℚP.+-mono-≤
    (pointwise index)
    (sumMonotone indices lower upper pointwise)

record FiniteGaussianModeEnclosure (Mode : Set) : Set₁ where
  field
    modes : List Mode
    contribution lowerContribution : Mode → ℚ
    modeLower : ∀ mode → lowerContribution mode ≤ contribution mode

    ell epsilon betaZ epsilonBudget : ℚ
    ellExact : ell ≡ Sums.sumRational modes contribution
    betaZExact : betaZ ≡ oneLoopSU2Factor * ell + epsilon
    epsilonLower : - epsilonBudget ≤ epsilon

open FiniteGaussianModeEnclosure public

computedEllLower :
  ∀ {Mode} → FiniteGaussianModeEnclosure Mode → ℚ
computedEllLower dataSet =
  Sums.sumRational (modes dataSet) (lowerContribution dataSet)

computedGaussianLower :
  ∀ {Mode} → FiniteGaussianModeEnclosure Mode → ℚ
computedGaussianLower dataSet =
  oneLoopSU2Factor * computedEllLower dataSet - epsilonBudget dataSet

computedEllLowerIsValid :
  ∀ {Mode} (dataSet : FiniteGaussianModeEnclosure Mode) →
  computedEllLower dataSet ≤ ell dataSet
computedEllLowerIsValid dataSet =
  subst
    (λ upper → computedEllLower dataSet ≤ upper)
    (sym (ellExact dataSet))
    (sumMonotone
      (modes dataSet)
      (lowerContribution dataSet)
      (contribution dataSet)
      (modeLower dataSet))

computedGaussianLowerIsValid :
  ∀ {Mode} (dataSet : FiniteGaussianModeEnclosure Mode) →
  computedGaussianLower dataSet ≤ betaZ dataSet
computedGaussianLowerIsValid dataSet =
  let
    scaledEll = Norm.scaleNonnegative
      oneLoopSU2Factor
      (ℚP.nonNegative⁻¹ oneLoopSU2Factor)
      (computedEllLowerIsValid dataSet)
    summed = ℚP.+-mono-≤ scaledEll (epsilonLower dataSet)
  in
  subst
    (λ upper → computedGaussianLower dataSet ≤ upper)
    (sym (betaZExact dataSet))
    (subst
      (λ lower → lower
        ≤ oneLoopSU2Factor * ell dataSet + epsilon dataSet)
      (ℚRing.solve-∀
        oneLoopSU2Factor
        (computedEllLower dataSet)
        (epsilonBudget dataSet))
      summed)

power4 : ℚ → ℚ
power4 value = (value * value) * (value * value)

squareMonotone : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → left ≤ right →
  left * left ≤ right * right
squareMonotone left right leftNN rightNN leftBelow =
  ℚP.≤-trans
    (Norm.scaleNonnegative left leftNN leftBelow)
    (Norm.scaleNonnegative right rightNN leftBelow)

power4Monotone : ∀ left right →
  0ℚ ≤ left → 0ℚ ≤ right → left ≤ right →
  power4 left ≤ power4 right
power4Monotone left right leftNN rightNN leftBelow =
  let
    squareBelow = squareMonotone left right leftNN rightNN leftBelow
    leftSquareNN = ℚP.nonNegative⁻¹ (left * left)
    rightSquareNN = ℚP.nonNegative⁻¹ (right * right)
  in
  squareMonotone
    (left * left) (right * right)
    leftSquareNN rightSquareNN squareBelow

record FiniteInteractionAtomEnclosure (Atom : Set) : Set₁ where
  field
    atoms : List Atom
    coupling betaInt : ℚ
    interactionAtom coefficient : Atom → ℚ

    betaIntExact : betaInt ≡ Sums.sumRational atoms interactionAtom
    coefficientNonnegative : ∀ atom → 0ℚ ≤ coefficient atom
    atomLower : ∀ atom →
      - (coefficient atom * power4 coupling) ≤ interactionAtom atom

open FiniteInteractionAtomEnclosure public

interactionCoefficientTotal :
  ∀ {Atom} → FiniteInteractionAtomEnclosure Atom → ℚ
interactionCoefficientTotal dataSet =
  Sums.sumRational (atoms dataSet) (coefficient dataSet)

interactionLowerSum :
  ∀ {Atom} (dataSet : FiniteInteractionAtomEnclosure Atom) →
  Sums.sumRational (atoms dataSet)
    (λ atom → - (coefficient dataSet atom * power4 (coupling dataSet)))
  ≤ betaInt dataSet
interactionLowerSum dataSet =
  subst
    (λ upper →
      Sums.sumRational (atoms dataSet)
        (λ atom → - (coefficient dataSet atom * power4 (coupling dataSet)))
      ≤ upper)
    (sym (betaIntExact dataSet))
    (sumMonotone
      (atoms dataSet)
      (λ atom → - (coefficient dataSet atom * power4 (coupling dataSet)))
      (interactionAtom dataSet)
      (atomLower dataSet))

interactionLowerCollapsed :
  ∀ {Atom} (dataSet : FiniteInteractionAtomEnclosure Atom) →
  - (interactionCoefficientTotal dataSet * power4 (coupling dataSet))
  ≤ betaInt dataSet
interactionLowerCollapsed dataSet =
  let
    distributed = Sums.sumRationalScale
      (power4 (coupling dataSet))
      (atoms dataSet) (coefficient dataSet)
    negated = Sums.sumRationalNegate
      (atoms dataSet)
      (λ atom → coefficient dataSet atom * power4 (coupling dataSet))
    identify :
      Sums.sumRational (atoms dataSet)
        (λ atom → - (coefficient dataSet atom * power4 (coupling dataSet)))
      ≡ - (interactionCoefficientTotal dataSet * power4 (coupling dataSet))
    identify = trans negated (cong -_ distributed)
  in
  subst
    (λ lower → lower ≤ betaInt dataSet)
    identify
    (interactionLowerSum dataSet)

quarticUniformInteractionLower :
  ∀ {Atom}
    (dataSet : FiniteInteractionAtomEnclosure Atom)
    gamma →
  0ℚ ≤ coupling dataSet → 0ℚ ≤ gamma → coupling dataSet ≤ gamma →
  0ℚ ≤ interactionCoefficientTotal dataSet →
  - (interactionCoefficientTotal dataSet * power4 gamma)
  ≤ betaInt dataSet
quarticUniformInteractionLower dataSet gamma couplingNN gammaNN couplingBelow totalNN =
  let
    fourthBelow = power4Monotone
      (coupling dataSet) gamma couplingNN gammaNN couplingBelow
    scaled = Norm.scaleNonnegative
      (interactionCoefficientTotal dataSet) totalNN fourthBelow
    negated = ℚP.neg-mono-≤ scaled
  in
  ℚP.≤-trans negated (interactionLowerCollapsed dataSet)

betaSplitLowerAfterQuarticAbsorption :
  ∀ {Mode Atom}
    (gaussian : FiniteGaussianModeEnclosure Mode)
    (interaction : FiniteInteractionAtomEnclosure Atom)
    gamma →
  betaZ gaussian + betaInt interaction ≡ betaZ gaussian + betaInt interaction →
  0ℚ ≤ coupling interaction → 0ℚ ≤ gamma → coupling interaction ≤ gamma →
  0ℚ ≤ interactionCoefficientTotal interaction →
  interactionCoefficientTotal interaction * power4 gamma
    ≤ half * computedGaussianLower gaussian →
  half * computedGaussianLower gaussian
    ≤ betaZ gaussian + betaInt interaction
betaSplitLowerAfterQuarticAbsorption gaussian interaction gamma refl
    couplingNN gammaNN couplingBelow totalNN threshold =
  let
    interactionUniform = quarticUniformInteractionLower
      interaction gamma couplingNN gammaNN couplingBelow totalNN
    gaussianBound = computedGaussianLowerIsValid gaussian
    summed = ℚP.+-mono-≤ gaussianBound interactionUniform
    targetShift :
      half * computedGaussianLower gaussian
      ≤ computedGaussianLower gaussian
        - interactionCoefficientTotal interaction * power4 gamma
    targetShift =
      subst
        (λ lower → lower
          ≤ computedGaussianLower gaussian
            - interactionCoefficientTotal interaction * power4 gamma)
        (ℚRing.solve-∀ (computedGaussianLower gaussian))
        (ℚP.+-monoʳ-≤
          (half * computedGaussianLower gaussian)
          (ℚP.neg-mono-≤ threshold))
  in
  ℚP.≤-trans targetShift summed

yM4FiniteGaussianModeLowerLevel : ProofLevel
yM4FiniteGaussianModeLowerLevel = machineChecked

yM4FiniteInteractionAtomQuarticLevel : ProofLevel
yM4FiniteInteractionAtomQuarticLevel = machineChecked

yM4FiniteBetaQuarticAbsorptionLevel : ProofLevel
yM4FiniteBetaQuarticAbsorptionLevel = machineChecked

yM4LiteralFiniteBrillouinModeInstantiationLevel : ProofLevel
yM4LiteralFiniteBrillouinModeInstantiationLevel = conditional

yM4LiteralInteractionAtomInstantiationLevel : ProofLevel
yM4LiteralInteractionAtomInstantiationLevel = conditional
