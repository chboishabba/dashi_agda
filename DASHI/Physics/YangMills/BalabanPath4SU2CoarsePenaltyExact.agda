module DASHI.Physics.YangMills.BalabanPath4SU2CoarsePenaltyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  ( ℚ; 0ℚ; _-_; _*_; _≤_; _/_
  ; NonNegative; nonNegative )
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact
  using (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate
  using (oneSixteenth; nonnegativeFraction)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using
    ( configuredPathCoercivityConstant
    ; configuredPathCoercivityConstantIsOneSixteenth
    )
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
  using
    ( FieldEqual
    ; subtractField
    ; axisAverage4Subtract
    ; axisAverage4RespectsPointwise
    )
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (bondComponent)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact
  using (physicalTangentInnerNonnegative)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
open import DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using (gaugeFixedHessianQuadraticForm)

------------------------------------------------------------------------
-- The configured coarse penalty has coefficient one, hence dominates the
-- required 1/16 share of the coarse projection norm.
------------------------------------------------------------------------

fifteenSixteenth : ℚ
fifteenSixteenth = + 15 / 16

fifteenSixteenthTimesNonnegative : ∀ value →
  0ℚ ≤ value → 0ℚ ≤ fifteenSixteenth * value
fifteenSixteenthTimesNonnegative value zero≤value =
  let
    instance
      coefficientNonnegative : NonNegative fifteenSixteenth
      coefficientNonnegative = nonNegative (nonnegativeFraction 15 16)

      valueNonnegative : NonNegative value
      valueNonnegative = nonNegative zero≤value

      productNonnegative : NonNegative (fifteenSixteenth * value)
      productNonnegative =
        ℚP.nonNeg*nonNeg⇒nonNeg fifteenSixteenth value
  in
  ℚP.nonNegative⁻¹ (fifteenSixteenth * value)

oneSixteenthSplit : ∀ value →
  oneSixteenth * value + fifteenSixteenth * value ≡ value
oneSixteenthSplit = ℚRing.solve-∀

oneSixteenthTimesBelow : ∀ value →
  0ℚ ≤ value → oneSixteenth * value ≤ value
oneSixteenthTimesBelow value zero≤value =
  subst
    (λ right → oneSixteenth * value ≤ right)
    (oneSixteenthSplit value)
    (baseBelowBasePlusRemainder
      (oneSixteenth * value)
      (fifteenSixteenth * value)
      (fifteenSixteenthTimesNonnegative value zero≤value))

projectionNormNonnegative : ∀ tangent →
  0ℚ ≤ physicalUnweightedNormSq (fineProjection tangent)
projectionNormNonnegative tangent =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (physicalNormMatchesInner (fineProjection tangent)))
    (physicalTangentInnerNonnegative (fineProjection tangent))

coarsePenaltyScalarDomination : ∀ tangent →
  configuredPathCoercivityConstant
    * physicalUnweightedNormSq (fineProjection tangent)
  ≤ concreteCoarseInner
      (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
coarsePenaltyScalarDomination tangent =
  subst
    (λ coefficient →
      coefficient * physicalUnweightedNormSq (fineProjection tangent)
      ≤ concreteCoarseInner
          (literalBlockAverageQ tangent) (literalBlockAverageQ tangent))
    (sym configuredPathCoercivityConstantIsOneSixteenth)
    (subst
      (λ right →
        oneSixteenth * physicalUnweightedNormSq (fineProjection tangent)
        ≤ right)
      (sym (coarsePenaltyNormMatchesProjection tangent))
      (oneSixteenthTimesBelow
        (physicalUnweightedNormSq (fineProjection tangent))
        (projectionNormNonnegative tangent)))

------------------------------------------------------------------------
-- Q annihilates the exact fine residual.
------------------------------------------------------------------------

average0Subtract : ∀ left right →
  FieldEqual (average0 (subtractField left right))
    (subtractField (average0 left) (average0 right))
average0Subtract left right =
  axisAverage4Subtract axis0 left right

average01Subtract : ∀ left right →
  FieldEqual (average01 (subtractField left right))
    (subtractField (average01 left) (average01 right))
average01Subtract left right site =
  trans
    (axisAverage4RespectsPointwise axis1 (average0Subtract left right) site)
    (axisAverage4Subtract axis1 (average0 left) (average0 right) site)

average012Subtract : ∀ left right →
  FieldEqual (average012 (subtractField left right))
    (subtractField (average012 left) (average012 right))
average012Subtract left right site =
  trans
    (axisAverage4RespectsPointwise axis2 (average01Subtract left right) site)
    (axisAverage4Subtract axis2 (average01 left) (average01 right) site)

average0123Subtract : ∀ left right →
  FieldEqual (average0123 (subtractField left right))
    (subtractField (average0123 left) (average0123 right))
average0123Subtract left right site =
  trans
    (axisAverage4RespectsPointwise axis3 (average012Subtract left right) site)
    (axisAverage4Subtract axis3 (average012 left) (average012 right) site)

average0123ResidualZero : ∀ field site →
  average0123 (subtractField field (average0123 field)) site ≡ 0ℚ
average0123ResidualZero field site =
  trans
    (average0123Subtract field (average0123 field) site)
    (trans
      (cong
        (λ value → average0123 field site - value)
        (average0123OfFixed
          (average0123 field) (average0123Fixed field) site))
      (ℚRing.solve-∀ (average0123 field site)))

fineFluctuationAverageZero : ∀ tangent →
  CoarseAverageZero (fineFluctuation tangent)
fineFluctuationAverageZero tangent component bondAxis site =
  average0123ResidualZero
    (bondComponent (tangent component) bondAxis) site

fineFluctuationHessianCoercivity : ∀ tangent →
  configuredPathCoercivityConstant
    * physicalUnweightedNormSq (fineFluctuation tangent)
  ≤ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
fineFluctuationHessianCoercivity tangent =
  fineFluctuationCoercivity
    (fineFluctuation tangent)
    (fineFluctuationAverageZero tangent)

coarsePenalizedFluctuationCoercivity : ∀ tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
    + concreteCoarseInner
        (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
coarsePenalizedFluctuationCoercivity tangent =
  coarsePenalizedCoercivity tangent
    (gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent))
    (fineFluctuationHessianCoercivity tangent)
    (coarsePenaltyScalarDomination tangent)

coarsePenaltyScalarDominationLevel : ProofLevel
coarsePenaltyScalarDominationLevel = machineChecked

fineFluctuationKernelLevel : ProofLevel
fineFluctuationKernelLevel = machineChecked

coarsePenalizedFluctuationCoercivityLevel : ProofLevel
coarsePenalizedFluctuationCoercivityLevel = machineChecked
