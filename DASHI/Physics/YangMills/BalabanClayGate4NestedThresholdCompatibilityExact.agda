module DASHI.Physics.YangMills.BalabanClayGate4NestedThresholdCompatibilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Joint compatibility of the small-chart, perturbative, propagator and
-- Wilson large-field regimes.
--
-- The key analytic point is that the principal-log chart threshold need not
-- itself pay the polymer entropy.  We therefore retain three nested scales
--
--   chartRadius <= moderateThreshold <= badFieldThreshold,
--
-- and expose the exact simultaneous inequalities which a physical numerical
-- instantiation must satisfy.
------------------------------------------------------------------------

record OrderedCompatibilityAlgebra (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar
    square : Scalar → Scalar
    LessEqual StrictlyLess : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    multiplyMonotoneNonnegative : ∀ {left leftUpper right rightUpper} →
      LessEqual zero left → LessEqual left leftUpper →
      LessEqual zero right → LessEqual right rightUpper →
      LessEqual (multiply left right) (multiply leftUpper rightUpper)

open OrderedCompatibilityAlgebra public

record NestedFieldThresholds
    {Scalar : Set} (algebra : OrderedCompatibilityAlgebra Scalar) : Set₁ where
  field
    chartRadius moderateThreshold badFieldThreshold : Scalar

    chartInsideModerate :
      LessEqual algebra chartRadius moderateThreshold
    moderateInsideBad :
      LessEqual algebra moderateThreshold badFieldThreshold

open NestedFieldThresholds public

chartInsideBad :
  ∀ {Scalar} {algebra : OrderedCompatibilityAlgebra Scalar} →
  (thresholds : NestedFieldThresholds algebra) →
  LessEqual algebra
    (chartRadius thresholds)
    (badFieldThreshold thresholds)
chartInsideBad {algebra = algebra} thresholds =
  transitive algebra
    (chartInsideModerate thresholds)
    (moderateInsideBad thresholds)

record PhysicalThresholdCompatibility
    {Scalar : Set} (algebra : OrderedCompatibilityAlgebra Scalar) : Set₁ where
  field
    thresholds : NestedFieldThresholds algebra

    chartConstant propagatorConstant overlapConstant : Scalar
    propagatorTarget beta wilsonCoercivity : Scalar
    animalEntropy decayWeight reservedSlack : Scalar

    chartControl :
      StrictlyLess algebra
        (multiply algebra chartConstant
          (chartRadius thresholds))
        (one algebra)

    propagatorControl :
      LessEqual algebra
        (multiply algebra propagatorConstant
          (chartRadius thresholds))
        propagatorTarget

    overlapControl :
      LessEqual algebra
        (multiply algebra overlapConstant
          (moderateThreshold thresholds))
        (badFieldThreshold thresholds)

    wilsonPaysEntropyDecayAndSlack :
      LessEqual algebra
        (add algebra animalEntropy
          (add algebra decayWeight reservedSlack))
        (multiply algebra beta
          (multiply algebra wilsonCoercivity
            (square algebra (badFieldThreshold thresholds))))

open PhysicalThresholdCompatibility public

record WilsonAdmissibleInterval
    {Scalar : Set} (algebra : OrderedCompatibilityAlgebra Scalar) : Set₁ where
  field
    entropyLowerBound chartUpperBound selectedBadSquare : Scalar

    selectedAboveEntropyLowerBound :
      LessEqual algebra entropyLowerBound selectedBadSquare

    selectedBelowChartUpperBound :
      LessEqual algebra selectedBadSquare chartUpperBound

open WilsonAdmissibleInterval public

wilsonAdmissibleIntervalNonempty :
  ∀ {Scalar} {algebra : OrderedCompatibilityAlgebra Scalar} →
  (interval : WilsonAdmissibleInterval algebra) →
  LessEqual algebra
    (entropyLowerBound interval)
    (chartUpperBound interval)
wilsonAdmissibleIntervalNonempty {algebra = algebra} interval =
  transitive algebra
    (selectedAboveEntropyLowerBound interval)
    (selectedBelowChartUpperBound interval)

record UniformScaleCompatibility
    (Scale Scalar : Set)
    (algebra : OrderedCompatibilityAlgebra Scalar) : Set₁ where
  field
    compatibilityAt : Scale → PhysicalThresholdCompatibility algebra

open UniformScaleCompatibility public

nestedThresholdTransitivityLevel : ProofLevel
nestedThresholdTransitivityLevel = machineChecked

wilsonAdmissibleIntervalNonemptyLevel : ProofLevel
wilsonAdmissibleIntervalNonemptyLevel = machineChecked

physicalJointThresholdConstantsInputsLevel : ProofLevel
physicalJointThresholdConstantsInputsLevel = conditional

physicalUniformScaleCompatibilityInputsLevel : ProofLevel
physicalUniformScaleCompatibilityInputsLevel = conditional
