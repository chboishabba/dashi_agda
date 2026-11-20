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
import DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogAdPolynomialExact as Poly
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as P
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2ToBishopTraceExact as Scalar
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as J
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119TwoCarrierSelectedBondExact as Two
import DASHI.Physics.YangMills.BalabanCMP98Path13PerturbationCarrierWeldExact as Pert
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13CanonicalBondCenteredEmbeddingExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredTorusBijectionExact as Bijection
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
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

-- Avoid the legacy Path13FamilyGeometry record: it contains a legacy-real
-- principal chart even though the contour construction never reads it.
-- Select the original variational background and canonical geometry directly.
Path13Variational : Set → Set₁
Path13Variational C = Variational.BackgroundFieldVariationalTheorem
  C Background.RationalSU2Background13 Family.Path13PositiveBond ℚ

record NativeGeometry (C : Set) : Set₁ where
  field
    variational : Path13Variational C
    coarse : C
    small : Variational.CoarseSmallField variational coarse
    walkCertificate : Bijection.CenteredTorusWalkAgreementCertificate R158.sourceRadius
open NativeGeometry public

nativeBackground : ∀ {C} → NativeGeometry C → Background.RationalSU2Background13
nativeBackground g = Variational.background (variational g) (coarse g) (small g)

nativeGeometryAt : ∀ {C} → NativeGeometry C → Family.Path13PositiveBond →
  Geometry.Equation119GeometrySource R192.path13PeriodicIndex
    SU2.RationalUnitQuaternion Group.rationalSU2ExactLinkGroup
nativeGeometryAt g bond = record
  { Geometry.Equation119GeometrySource.realization =
      λ _ → R192.path13PhysicalPeriodicRealization (nativeBackground g)
  ; Geometry.Equation119GeometrySource.minusEmbedding =
      λ _ → Canonical.canonicalEmbeddingAtSite (walkCertificate g) (Carrier.first bond)
  ; Geometry.Equation119GeometrySource.coarseSegment = λ _ → Family.coarseSegmentFor bond
  }

relativeUnit :
  ∀ {CoarseField} → NativeGeometry CoarseField →
  Family.Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  SU2.RationalUnitQuaternion
relativeUnit geometry bond = Geometry.relativeContourElement
  (nativeGeometryAt geometry bond)

record Inputs (CoarseField : Set) : Set₁ where
  field
    geometry : NativeGeometry CoarseField
    chart : LocalChart
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
        (nativeBackground (geometry inputs))
  ; Two.TwoCarrierEquation119PathData.bondComponent =
      λ _ perturbation site direction →
        embedLie (Pert.rationalSignedBondLie3
          (nativeBackground (geometry inputs)) perturbation site direction)
  ; Two.TwoCarrierEquation119PathData.adjointLink = λ _ → unitAdjoint
  ; Two.TwoCarrierEquation119PathData.scaleV = scale
  ; Two.TwoCarrierEquation119PathData.minusEmbedding =
      Geometry.minusEmbedding (nativeGeometryAt (geometry inputs) bond)
  ; Two.TwoCarrierEquation119PathData.plusEmbedding =
      λ step → R163.translatedEmbedding
        (Geometry.minusEmbedding (nativeGeometryAt (geometry inputs) bond) step)
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

------------------------------------------------------------------------
-- Native reduced-polynomial operations, with explicit pure-quaternion
-- normalization. Reuse the existing Bishop Vec3 and ad-polynomial owner.
------------------------------------------------------------------------

toVec3 : BishopLie → Poly.Vec3B
toVec3 v = Poly.vec3B
  (v P.coordinateX) (v P.coordinateY) (v P.coordinateZ)

fromVec3 : Poly.Vec3B → BishopLie
fromVec3 v P.coordinateX = Poly.x v
fromVec3 v P.coordinateY = Poly.y v
fromVec3 v P.coordinateZ = Poly.z v

twoB : B.ℝ
twoB = B._⋆ (+ 2 / 1)

halfB : B.ℝ
halfB = B._⋆ (+ 1 / 2)

ad : BishopLie → BishopLie → BishopLie
ad y v = fromVec3
  (Poly.bracket3 (Poly.scale3 twoB (toVec3 y)) (toVec3 v))

reducedApply : B.ℝ → B.ℝ → BishopLie → BishopLie → BishopLie
reducedApply a b y v = fromVec3
  (Poly.principalLogAdApply a b (Poly.scale3 twoB (toVec3 y)) (toVec3 v))

-- D+ = I + A ad + B ad^2.
rootFreeDexp : (BishopLie → B.ℝ) → (BishopLie → B.ℝ) →
  BishopLie → BishopLie → BishopLie
rootFreeDexp a b y = reducedApply (a y) (b y) y

-- Ad(exp Y) = I + (1-w B) ad + A ad^2,
-- where w = 4||Y||^2. No separate trigonometric coefficient authority.
adRadiusSquared : BishopLie → B.ℝ
adRadiusSquared y =
  B._*_ (B._⋆ (+ 4 / 1))
    (sumBishop P.lieCoordinates3 (λ c → B._*_ (y c) (y c)))

rootFreeAdjointExp : (BishopLie → B.ℝ) → (BishopLie → B.ℝ) →
  BishopLie → BishopLie → BishopLie
rootFreeAdjointExp a b y =
  reducedApply
    (B._-_ B.1ℝ (B._*_ (adRadiusSquared y) (b y)))
    (a y) y

-- J+ = I - ad/2 + beta ad^2, with beta on the SAME Bishop carrier.
rootFreeJplus : (BishopLie → B.ℝ) →
  BishopLie → BishopLie → BishopLie
rootFreeJplus beta y = reducedApply (B.- halfB) (beta y) y

-- Existing coefficient telescope now applies directly to this native carrier.
inverseCoefficientTelescope :
  ∀ beta beta0 y v →
  Poly.vec3Congruent
    (Poly.sub3 (toVec3 (rootFreeJplus (λ _ → beta) y v))
               (toVec3 (rootFreeJplus (λ _ → beta0) y v)))
    (Poly.scale3 (B._-_ beta beta0)
      (Poly.adSquare3 (Poly.scale3 twoB (toVec3 y)) (toVec3 v)))
inverseCoefficientTelescope beta beta0 y v =
  Poly.principalLogCoefficientTelescope
    (B.- halfB) beta beta0 (Poly.scale3 twoB (toVec3 y)) (toVec3 v)

-- Assemble only on the selected chart. The analytic coefficient producer
-- still owes inverse cancellation, not a new arbitrary matrix family.
fromReducedChart :
  (log : SU2.RationalUnitQuaternion → BishopLie) →
  (a b beta : BishopLie → B.ℝ) →
  (relevant : BishopLie → Set) →
  (∀ y → relevant y → ∀ v →
    rootFreeJplus beta y (rootFreeDexp a b y v) ≈v v) →
  LocalChart
fromReducedChart log a b beta relevant inverse = record
  { principalLog = log
  ; dexpPlus = rootFreeDexp a b
  ; jPlus = rootFreeJplus beta
  ; adjointExp = rootFreeAdjointExp a b
  ; Relevant = relevant
  ; inverseOnChart = inverse
  }
