module DASHI.Physics.YangMills.BalabanCMP98Path13BishopNativeSourceExact where

-- Bałaban CMP98 (1985), eqs. (119)--(121).
-- Reuse the existing two-carrier path compiler on actual Bishop coordinates.
-- No Bishop-to-legacy real transport or setoid-to-propositional equality.
-- The chart and selected physical background remain explicit source inputs.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
import Real as B
import RealProperties as BP
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as P
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2ToBishopTraceExact as Scalar
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as J
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as Two
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Pert
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanRationalUnitQuaternionRealLieAdjointExact as Adj
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162

BishopLie : Set
BishopLie = P.LieCoordinate3 → B.ℝ

_≈v_ : BishopLie → BishopLie → Set
u ≈v v = ∀ c → B._≃_ (u c) (v c)

embedLie : J.Lie3Vector → BishopLie
embedLie v c = Scalar.rationalCoordinateToBishop (v c)

bishopSignedCarrier : R146.SignedAdditiveOperatorCarrier
bishopSignedCarrier = record
  { R146.SignedAdditiveOperatorCarrier.additive = record
    { R126.AdditiveOperatorCarrier.Vector = BishopLie
    ; R126.AdditiveOperatorCarrier.zeroV = λ _ → B.0ℝ
    ; R126.AdditiveOperatorCarrier.addV = λ u v c → B._+_ (u c) (v c)
    }
  ; R146.SignedAdditiveOperatorCarrier.negV = λ v c → B.- (v c)
  }

scale : ℚ → BishopLie → BishopLie
scale a v c = B._*_ (Scalar.rationalCoordinateToBishop a) (v c)

sumBishop : ∀ {I : Set} → List I → (I → B.ℝ) → B.ℝ
sumBishop [] f = B.0ℝ
sumBishop (i ∷ is) f = B._+_ (f i) (sumBishop is f)

matrixAction : J.Lie3Matrix → BishopLie → BishopLie
matrixAction m v row =
  sumBishop P.lieCoordinates3
    (λ col → B._*_ (Scalar.rationalCoordinateToBishop (m row col)) (v col))

unitAdjoint : SU2.RationalUnitQuaternion → BishopLie → BishopLie
unitAdjoint u = matrixAction (Adj.unitAdjointRationalMatrix u)

-- A chart-specific local calculus, not an assertion of global invertibility.
record LocalChart : Set₁ where
  field
    principalLog : SU2.RationalUnitQuaternion → BishopLie
    dexpPlus jPlus adjointExp : BishopLie → BishopLie → BishopLie
    Relevant : BishopLie → Set
    inverseOnChart : ∀ y → Relevant y → ∀ v →
      jPlus y (dexpPlus y v) ≈v v
open LocalChart public

relativeUnit :
  ∀ {CoarseField} → Family.Path13FamilyGeometry CoarseField →
  Family.Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  SU2.RationalUnitQuaternion
relativeUnit geometry bond = Geometry.relativeContourElement
  (Family.geometrySourceAt geometry bond)

record Inputs (CoarseField : Set) : Set₁ where
  field
    geometry : Family.Path13FamilyGeometry CoarseField
    chart : LocalChart
    -- The source geometry is reused; this is the remaining actual chart
    -- admission at the literal relative contour.
    pointRelevant : ∀ bond step point →
      Relevant chart
        (principalLog chart
          (relativeUnit geometry bond step point))
open Inputs public

pointY : ∀ {C} → Inputs C → Family.Path13PositiveBond → Nat →
  Centered.CenteredBlockPoint4 6 → BishopLie
pointY inputs bond step point =
  principalLog (chart inputs) (relativeUnit (geometry inputs) bond step point)

outerY : ∀ {C} → Inputs C → Family.Path13PositiveBond → Nat → BishopLie
outerY inputs bond step c =
  sumBishop (Carrier.elements (Centered.centeredBlockFinite 6))
    (λ point → scale R147.siteWeightℚ (pointY inputs bond step point) c)

sourceAt : ∀ {C} → Inputs C → Family.Path13PositiveBond →
  Two.TwoCarrierEquation119PathData bishopSignedCarrier
    Pert.Path13RationalPerturbation SU2.RationalUnitQuaternion
    R192.path13PeriodicIndex Group.rationalSU2ExactLinkGroup
sourceAt inputs bond = record
  { Two.TwoCarrierEquation119PathData.realization =
      λ _ → R192.path13PhysicalPeriodicRealization
        (Family.familyBackground (geometry inputs))
  ; Two.TwoCarrierEquation119PathData.bondComponent =
      λ _ perturbation site direction →
        embedLie (Pert.rationalSignedBondLie3
          (Family.familyBackground (geometry inputs)) perturbation site direction)
  ; Two.TwoCarrierEquation119PathData.adjointLink = λ _ → unitAdjoint
  ; Two.TwoCarrierEquation119PathData.scaleV = scale
  ; Two.TwoCarrierEquation119PathData.minusEmbedding =
      Family.minusEmbeddingFor (geometry inputs) bond
  ; Two.TwoCarrierEquation119PathData.plusEmbedding =
      λ step → R163.translatedEmbedding
        (Family.minusEmbeddingFor (geometry inputs) bond step)
        (Family.coarseSegmentFor bond)
  ; Two.TwoCarrierEquation119PathData.coarseSegment =
      λ _ → Family.coarseSegmentFor bond
  ; Two.TwoCarrierEquation119PathData.coarseSegmentEndsAtPlusCentre = λ _ → refl
  ; Two.TwoCarrierEquation119PathData.translationCommutation =
      R162.periodicSegmentCommutation R192.path13PeriodicIndex
  ; Two.TwoCarrierEquation119PathData.dexpMinusOuter =
      λ step → dexpPlus (chart inputs) (outerY inputs bond step)
  ; Two.TwoCarrierEquation119PathData.inverseDexpMinusAt =
      λ step point → jPlus (chart inputs) (pointY inputs bond step point)
  ; Two.TwoCarrierEquation119PathData.adjointExpAt =
      λ step point → adjointExp (chart inputs) (pointY inputs bond step point)
  ; Two.TwoCarrierEquation119PathData.adjointExpOuter =
      λ step → adjointExp (chart inputs) (outerY inputs bond step)
  }

fieldFamily : ∀ {C} → Inputs C →
  Two.TwoCarrierEquation119FieldFamily bishopSignedCarrier
    Pert.Path13RationalPerturbation Family.Path13PositiveBond
    SU2.RationalUnitQuaternion R192.path13PeriodicIndex
    Group.rationalSU2ExactLinkGroup
fieldFamily inputs = record { Two.TwoCarrierEquation119FieldFamily.sourceAt = sourceAt inputs }

equation119 : ∀ {C} → Inputs C → Nat → Pert.Path13RationalPerturbation →
  Family.Path13PositiveBond → BishopLie
equation119 inputs = Two.assembledEquation119QPrime (fieldFamily inputs)

equation120 : ∀ {C} → Inputs C → Nat → Pert.Path13RationalPerturbation →
  Family.Path13PositiveBond → BishopLie
equation120 inputs = Two.assembledEquation120QSource (fieldFamily inputs)

pointInverse : ∀ {C} (inputs : Inputs C) bond step point v →
  jPlus (chart inputs) (pointY inputs bond step point)
    (dexpPlus (chart inputs) (pointY inputs bond step point) v) ≈v v
pointInverse inputs bond step point =
  inverseOnChart (chart inputs) (pointY inputs bond step point)
    (pointRelevant inputs bond step point)
