module DASHI.Physics.YangMills.BalabanClayGate4KochWittwerContractionResidualExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- A-posteriori contraction/residual architecture.
--
-- Hans Koch and Peter Wittwer,
-- "A Non-Gaussian Renormalization Group Fixed Point for Hierarchical Scalar
-- Lattice Field Theories",
-- Communications in Mathematical Physics 106 (3) (1986), 495--532.
-- DOI: 10.1007/BF01207260.
--
-- Hans Koch and Peter Wittwer,
-- "On the Renormalization Group Transformation for Scalar Hierarchical
-- Models",
-- Communications in Mathematical Physics 138 (1991), 537--568.
-- DOI: 10.1007/BF02102041.
--
-- Hans Koch, Alain Schenkel and Peter Wittwer,
-- "Computer-Assisted Proofs in Analysis and Programming in Logic: A Case
-- Study", mp_arc 94-394 (1994); no DOI recorded.
--
-- Relationship: the theorem below is the reusable mathematical pattern, not a
-- Yang--Mills estimate.  If R is rho-contractive, x* is fixed and x0 has
-- residual at most epsilon, then
--
--   d(x*,x0) <= rho d(x*,x0) + epsilon,
--
-- and the selected ordered scalar algebra converts this to the familiar
-- epsilon/(1-rho) bound.
------------------------------------------------------------------------

record ContractionResidualAlgebra (Scalar : Set) : Set₁ where
  field
    zero add multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    multiplyMonotoneLeft : ∀ {lower upper} common →
      LessEqual lower upper →
      LessEqual (multiply common lower) (multiply common upper)

open ContractionResidualAlgebra public

record ContractionResidualData
    (Point Scalar : Set) : Set₁ where
  field
    algebra : ContractionResidualAlgebra Scalar
    transform : Point → Point
    distance : Point → Point → Scalar

    rho epsilon residualErrorBound : Scalar
    approximatePoint fixedPoint : Point

    fixedPointMeaning : transform fixedPoint ≡ fixedPoint

    triangleThroughTransform :
      LessEqual algebra
        (distance fixedPoint approximatePoint)
        (add algebra
          (distance (transform fixedPoint)
            (transform approximatePoint))
          (distance (transform approximatePoint) approximatePoint))

    contraction :
      LessEqual algebra
        (distance (transform fixedPoint)
          (transform approximatePoint))
        (multiply algebra rho
          (distance fixedPoint approximatePoint))

    residual :
      LessEqual algebra
        (distance (transform approximatePoint) approximatePoint)
        epsilon

    solveOneMinusRho : ∀ value →
      LessEqual algebra value
        (add algebra (multiply algebra rho value) epsilon) →
      LessEqual algebra value residualErrorBound

open ContractionResidualData public

fixedPointDistanceBelowAffineResidual :
  ∀ {Point Scalar}
    (dataSet : ContractionResidualData Point Scalar) →
  LessEqual (algebra dataSet)
    (distance dataSet (fixedPoint dataSet) (approximatePoint dataSet))
    (add (algebra dataSet)
      (multiply (algebra dataSet)
        (rho dataSet)
        (distance dataSet
          (fixedPoint dataSet) (approximatePoint dataSet)))
      (epsilon dataSet))
fixedPointDistanceBelowAffineResidual dataSet =
  transitive (algebra dataSet)
    (triangleThroughTransform dataSet)
    (addMonotone (algebra dataSet)
      (contraction dataSet)
      (residual dataSet))

fixedPointDistanceBelowResidualOverOneMinusRho :
  ∀ {Point Scalar}
    (dataSet : ContractionResidualData Point Scalar) →
  LessEqual (algebra dataSet)
    (distance dataSet (fixedPoint dataSet) (approximatePoint dataSet))
    (residualErrorBound dataSet)
fixedPointDistanceBelowResidualOverOneMinusRho dataSet =
  solveOneMinusRho dataSet
    (distance dataSet (fixedPoint dataSet) (approximatePoint dataSet))
    (fixedPointDistanceBelowAffineResidual dataSet)

record ExplicitResidualQuotientMeaning
    {Point Scalar : Set}
    (dataSet : ContractionResidualData Point Scalar) : Set₁ where
  field
    one subtract divide : Scalar → Scalar → Scalar

    residualErrorBoundMeaning :
      residualErrorBound dataSet
      ≡ divide (epsilon dataSet)
          (subtract one (rho dataSet))

open ExplicitResidualQuotientMeaning public

fixedPointDistanceBelowExplicitResidualQuotient :
  ∀ {Point Scalar}
    {dataSet : ContractionResidualData Point Scalar}
    (meaning : ExplicitResidualQuotientMeaning dataSet) →
  LessEqual (algebra dataSet)
    (distance dataSet (fixedPoint dataSet) (approximatePoint dataSet))
    (divide meaning (epsilon dataSet)
      (subtract meaning (one meaning) (rho dataSet)))
fixedPointDistanceBelowExplicitResidualQuotient {dataSet = dataSet} meaning =
  subst
    (λ upper → LessEqual (algebra dataSet)
      (distance dataSet (fixedPoint dataSet) (approximatePoint dataSet))
      upper)
    (residualErrorBoundMeaning meaning)
    (fixedPointDistanceBelowResidualOverOneMinusRho dataSet)

contractionResidualAffineBoundLevel : ProofLevel
contractionResidualAffineBoundLevel = machineChecked

contractionResidualQuotientBoundLevel : ProofLevel
contractionResidualQuotientBoundLevel = machineChecked

kochWittwerContractionMethodologyLevel : ProofLevel
kochWittwerContractionMethodologyLevel = standardImported

physicalYangMillsContractionRatioInputsLevel : ProofLevel
physicalYangMillsContractionRatioInputsLevel = conditional

physicalYangMillsResidualInputsLevel : ProofLevel
physicalYangMillsResidualInputsLevel = conditional
