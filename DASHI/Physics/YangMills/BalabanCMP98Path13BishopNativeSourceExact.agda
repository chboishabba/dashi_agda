module DASHI.Physics.YangMills.BalabanCMP98Path13BishopNativeSourceExact where

-- Bałaban CMP98 (1985), eqs. (119)--(121).
-- Reuse the existing two-carrier path compiler on actual Bishop coordinates.
-- No Bishop-to-legacy real transport or setoid-to-propositional equality.
-- The chart and selected physical background remain explicit source inputs.

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as Radius
import DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact as Length
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
import Sequence as Seq
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as AbsSquare
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iter
open import Data.Rational.Base as Rat using (ℚ; 0ℚ; 1ℚ; _≤_; _+_; _-_; _*_) renaming (_/_ to _/q_)
import Data.Rational.Properties as RP
import Data.Rational.Unnormalised.Properties as UP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (sym; subst)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Cast
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2BishopUnitaryWeldExact as Unit
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import Real as B
import RealProperties as BP
import DASHI.Physics.YangMills.BalabanCMP109BishopPrincipalLogAdPolynomialExact as Poly
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as Series
import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as Quaternion
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
open import Data.Unit using (⊤)
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
import DASHI.Physics.YangMills.BalabanPath13RadiusSixWalkAgreementExact as Walk
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
    LogAdmissible : SU2.RationalUnitQuaternion → Set
    principalLog : (q : SU2.RationalUnitQuaternion) → LogAdmissible q → BishopLie
    Relevant : BishopLie → Set
    dexpPlus adjointExp jPlus : (y : BishopLie) → Relevant y → BishopLie → BishopLie
    inverseOnChart : ∀ y (inChart : Relevant y) v →
      jPlus y inChart (dexpPlus y inChart v) ≈v v
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
      λ _ → Canonical.canonicalEmbeddingAtSite Walk.radiusSixWalkAgreement (Carrier.first bond)
  ; Geometry.Equation119GeometrySource.coarseSegment = λ _ → Family.coarseSegmentFor bond
  }

relativeUnit :
  ∀ {CoarseField} → NativeGeometry CoarseField →
  Family.Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  SU2.RationalUnitQuaternion
relativeUnit geometry bond = Geometry.relativeContourElement
  (nativeGeometryAt geometry bond)

PointAdmission : ∀ {C} → NativeGeometry C → LocalChart → Set
PointAdmission g ch = ∀ bond step point → LogAdmissible ch (relativeUnit g bond step point)

pointYFrom : ∀ {C} (g : NativeGeometry C) (ch : LocalChart) →
  PointAdmission g ch → Family.Path13PositiveBond → Nat →
  Centered.CenteredBlockPoint4 6 → BishopLie
pointYFrom g ch admission bond step point =
  principalLog ch (relativeUnit g bond step point) (admission bond step point)

outerYFrom : ∀ {C} (g : NativeGeometry C) (ch : LocalChart) →
  PointAdmission g ch → Family.Path13PositiveBond → Nat → BishopLie
outerYFrom g ch admission bond step c =
  sumBishop (Carrier.elements (Centered.centeredBlockFinite 6))
    (λ point → scale R147.siteWeightℚ (pointYFrom g ch admission bond step point) c)

record Inputs (CoarseField : Set) : Set₁ where
  field
    geometry : NativeGeometry CoarseField
    chart : LocalChart
    pointLogAdmissible : PointAdmission geometry chart
    pointRelevant : ∀ bond step point →
      Relevant chart (pointYFrom geometry chart pointLogAdmissible bond step point)
    outerRelevant : ∀ bond step →
      Relevant chart (outerYFrom geometry chart pointLogAdmissible bond step)
open Inputs public

pointY : ∀ {C} → Inputs C → Family.Path13PositiveBond → Nat →
  Centered.CenteredBlockPoint4 6 → BishopLie
pointY inputs = pointYFrom (geometry inputs) (chart inputs) (pointLogAdmissible inputs)

outerY : ∀ {C} → Inputs C → Family.Path13PositiveBond → Nat → BishopLie
outerY inputs = outerYFrom (geometry inputs) (chart inputs) (pointLogAdmissible inputs)

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
        (outerRelevant inputs bond step)
  ; Two.TwoCarrierEquation119PathData.inverseDexpMinusAt =
      λ step point → jPlus (chart inputs) (pointY inputs bond step point)
        (pointRelevant inputs bond step point)
  ; Two.TwoCarrierEquation119PathData.adjointExpAt =
      λ step point → adjointExp (chart inputs) (pointY inputs bond step point)
        (pointRelevant inputs bond step point)
  ; Two.TwoCarrierEquation119PathData.adjointExpOuter =
      λ step → adjointExp (chart inputs) (outerY inputs bond step)
        (outerRelevant inputs bond step)
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
    (pointRelevant inputs bond step point)
    (dexpPlus (chart inputs) (pointY inputs bond step point)
      (pointRelevant inputs bond step point) v) ≈v v
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
  { LogAdmissible = λ _ → ⊤
  ; principalLog = λ q _ → log q
  ; dexpPlus = λ y _ → rootFreeDexp a b y
  ; jPlus = λ y _ → rootFreeJplus beta y
  ; adjointExp = λ y _ → rootFreeAdjointExp a b y
  ; Relevant = relevant
  ; inverseOnChart = inverse
  }

-- Use the actual denominator-cleared polynomial theorem. This path does
-- not require an externally supplied beta coefficient or inverse identity.
physicalGenerator : BishopLie → Poly.Vec3B
physicalGenerator y = Poly.scale3 twoB (toVec3 y)

positiveReducedChart :
  (a b : BishopLie → B.ℝ) → BishopLie → Set
positiveReducedChart a b y =
  B._<_ B.0ℝ (Poly.reducedDelta (physicalGenerator y) (a y) (b y))

nativeReducedInverse :
  (a b : BishopLie → B.ℝ) → (y : BishopLie) →
  positiveReducedChart a b y → BishopLie → BishopLie
nativeReducedInverse a b y p v =
  fromVec3 (Poly.reducedInverse (physicalGenerator y) (a y) (b y) p (toVec3 v))

nativeReducedInverseCancels :
  ∀ a b y (p : positiveReducedChart a b y) v →
  nativeReducedInverse a b y p (rootFreeDexp a b y v) ≈v v
nativeReducedInverseCancels a b y p v P.coordinateX =
  proj₁ (Poly.reducedLeftInverse (physicalGenerator y) (a y) (b y) p (toVec3 v))
nativeReducedInverseCancels a b y p v P.coordinateY =
  proj₁ (proj₂ (Poly.reducedLeftInverse (physicalGenerator y) (a y) (b y) p (toVec3 v)))
nativeReducedInverseCancels a b y p v P.coordinateZ =
  proj₂ (proj₂ (Poly.reducedLeftInverse (physicalGenerator y) (a y) (b y) p (toVec3 v)))

fromPositiveReducedChart :
  (SU2.RationalUnitQuaternion → BishopLie) →
  (a b : BishopLie → B.ℝ) → LocalChart
fromPositiveReducedChart log a b = record
  { LogAdmissible = λ _ → ⊤
  ; principalLog = λ q _ → log q
  ; dexpPlus = λ y _ → rootFreeDexp a b y
  ; adjointExp = λ y _ → rootFreeAdjointExp a b y
  ; Relevant = positiveReducedChart a b
  ; jPlus = nativeReducedInverse a b
  ; inverseOnChart = nativeReducedInverseCancels a b
  }

------------------------------------------------------------------------
-- Fully constructed coefficient values, bounds and inverse cancellation
-- on the selected small-radius chart. Only geometric chart admission
-- remains an input. Functional identification with the source Frechet
-- derivative and the exp-log identity are separate semantic theorems.
------------------------------------------------------------------------

contourImaginary : SU2.RationalUnitQuaternion → Poly.Vec3B
contourImaginary q =
  Poly.vec3B (Scalar.rationalCoordinateToBishop (SU2.imagI q))
    (Scalar.rationalCoordinateToBishop (SU2.imagJ q))
    (Scalar.rationalCoordinateToBishop (SU2.imagK q))

contourImagSq : SU2.RationalUnitQuaternion → B.ℝ
contourImagSq q = Poly.generatorSq (contourImaginary q)

record SmallContour (q : SU2.RationalUnitQuaternion) : Set where
  field
    positiveScalar : B._<_ B.0ℝ (Scalar.rationalCoordinateToBishop (SU2.realPart q))
    imaginarySqInside : B._≤_ (B.∣_∣ (contourImagSq q)) Half.bishopQuarter
open SmallContour public

seriesPrincipalLog : (q : SU2.RationalUnitQuaternion) → SmallContour q → BishopLie
seriesPrincipalLog q p =
  fromVec3 (Poly.scale3 (Series.arcSeries (contourImagSq q) (imaginarySqInside p))
    (contourImaginary q))

physicalW : BishopLie → B.ℝ
physicalW y = Poly.generatorSq (physicalGenerator y)

record SmallLie (y : BishopLie) : Set where
  field
    wNonnegative : B._≤_ B.0ℝ (physicalW y)
    wBelowQuarter : B._≤_ (physicalW y) Half.bishopQuarter
open SmallLie public

signedWInside : ∀ y → SmallLie y →
  B._≤_ (B.∣_∣ (B.- (physicalW y))) Half.bishopQuarter
signedWInside y p =
  BP.≤-respˡ-≃
    (BP.≃-symm (BP.≃-trans BP.∣-x∣≃∣x∣ (Seq.0≤x⇒∣x∣≃x (wNonnegative p))))
    (wBelowQuarter p)

aAt bAt : (y : BishopLie) → SmallLie y → B.ℝ
aAt y p = Series.aSeries (B.- (physicalW y)) (signedWInside y p)
bAt y p = Series.bSeries (B.- (physicalW y)) (signedWInside y p)

seriesDexp : (y : BishopLie) → SmallLie y → BishopLie → BishopLie
seriesDexp y p = reducedApply (aAt y p) (bAt y p) y

seriesAdjoint : (y : BishopLie) → SmallLie y → BishopLie → BishopLie
seriesAdjoint y p =
  reducedApply (Poly.reducedH (physicalGenerator y) (bAt y p)) (aAt y p) y

seriesDeltaPositive : ∀ y (p : SmallLie y) →
  B._<_ B.0ℝ (Poly.reducedDelta (physicalGenerator y) (aAt y p) (bAt y p))
seriesDeltaPositive y p =
  let wn = BP.0≤x⇒nonNegx (wNonnegative p)
      inside = signedWInside y p
  in Poly.reducedDeltaPositiveFromBounds (physicalGenerator y) (aAt y p) (bAt y p)
    (wNonnegative p) (wBelowQuarter p)
    (Series.aNonnegative (physicalW y) wn inside)
    (Series.bNonnegative (physicalW y) wn inside)
    (Series.bBelowOneSixth (physicalW y) wn inside)

seriesInverse : (y : BishopLie) → SmallLie y → BishopLie → BishopLie
seriesInverse y p v =
  fromVec3 (Poly.reducedInverse (physicalGenerator y) (aAt y p) (bAt y p)
    (seriesDeltaPositive y p) (toVec3 v))

seriesInverseCancels : ∀ y (p : SmallLie y) v →
  seriesInverse y p (seriesDexp y p v) ≈v v
seriesInverseCancels y p v P.coordinateX =
  proj₁ (Poly.reducedLeftInverse (physicalGenerator y) (aAt y p) (bAt y p)
    (seriesDeltaPositive y p) (toVec3 v))
seriesInverseCancels y p v P.coordinateY =
  proj₁ (proj₂ (Poly.reducedLeftInverse (physicalGenerator y) (aAt y p) (bAt y p)
    (seriesDeltaPositive y p) (toVec3 v)))
seriesInverseCancels y p v P.coordinateZ =
  proj₂ (proj₂ (Poly.reducedLeftInverse (physicalGenerator y) (aAt y p) (bAt y p)
    (seriesDeltaPositive y p) (toVec3 v)))

nativeSeriesChart : LocalChart
nativeSeriesChart = record
  { LogAdmissible = SmallContour
  ; principalLog = seriesPrincipalLog
  ; Relevant = SmallLie
  ; dexpPlus = seriesDexp
  ; adjointExp = seriesAdjoint
  ; jPlus = seriesInverse
  ; inverseOnChart = seriesInverseCancels
  }

------------------------------------------------------------------------
-- Actual chord-square admission on the original rational unit carrier.
-- This accepts the SQUARE of the norm radius, never an identification
-- of the norm with its square. The selected path telescope must supply
-- the chord-square bound; no new chart predicate is assumed.
------------------------------------------------------------------------

relativeChordRadius : ℚ
relativeChordRadius = + 37 /q 1024

relativeChordRadiusSq : ℚ
relativeChordRadiusSq = relativeChordRadius * relativeChordRadius

rationalImagSq : SU2.RationalUnitQuaternion → ℚ
rationalImagSq q =
  SU2.imagI q * SU2.imagI q
  + (SU2.imagJ q * SU2.imagJ q + SU2.imagK q * SU2.imagK q)

rationalImagNN : ∀ q → 0ℚ ≤ rationalImagSq q
rationalImagNN q =
  L2.addNonnegative (L2.squareNonnegative (SU2.imagI q))
    (L2.addNonnegative (L2.squareNonnegative (SU2.imagJ q))
      (L2.squareNonnegative (SU2.imagK q)))

rationalImagBelowChord : ∀ q →
  rationalImagSq q ≤ SU2.literalChordalDistanceSq q
rationalImagBelowChord q =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst (λ a → 0ℚ ≤ a)
      (gap (SU2.realPart q) (SU2.imagI q) (SU2.imagJ q) (SU2.imagK q))
      (L2.squareNonnegative (SU2.realPart q - 1ℚ)))
  where
  gap : ∀ a x y z →
    (a - 1ℚ) * (a - 1ℚ) ≡
    ((a - 1ℚ) * (a - 1ℚ) + x * x + y * y + z * z)
    - (x * x + (y * y + z * z))
  gap = Ring.solve-∀

radiusSqBelowQuarter : relativeChordRadiusSq ≤ + 1 /q 4
radiusSqBelowQuarter =
  RP.<⇒≤ (RP.positive⁻¹ ((+ 1 /q 4) - relativeChordRadiusSq))

radiusSqBelowOne : relativeChordRadiusSq ≤ 1ℚ
radiusSqBelowOne =
  RP.<⇒≤ (RP.positive⁻¹ (1ℚ - relativeChordRadiusSq))

scalarHalfBelowFromChord : ∀ q →
  SU2.literalChordalDistanceSq q ≤ relativeChordRadiusSq →
  (+ 1 /q 2) ≤ SU2.realPart q
scalarHalfBelowFromChord q bound =
  let a = SU2.realPart q
      c = + 2 /q 1
      traceBound :
        c * (1ℚ - a) ≤ 1ℚ
      traceBound = subst (λ u → u ≤ 1ℚ)
        (SU2.unitChordalEqualsTwiceTraceDeficit q)
        (RP.≤-trans bound radiusSqBelowOne)
      shifted = RP.+-monoʳ-≤ (c * a - 1ℚ) traceBound
      corrected = subst (λ l → l ≤ (c * a - 1ℚ) + 1ℚ)
        (left a) shifted
  in RP.*-cancelˡ-≤-pos c
      (subst (λ rr → c * (+ 1 /q 2) ≤ rr) (right a) corrected)
  where
  left : ∀ a → ((+ 2 /q 1) * a - 1ℚ)
      + (+ 2 /q 1) * (1ℚ - a)
      ≡ (+ 2 /q 1) * (+ 1 /q 2)
  left = Ring.solve-∀
  right : ∀ a → ((+ 2 /q 1) * a - 1ℚ) + 1ℚ ≡ (+ 2 /q 1) * a
  right = Ring.solve-∀

imagSqEmbed : ∀ q →
  B._≃_ (Scalar.rationalCoordinateToBishop (rationalImagSq q))
    (contourImagSq q)
imagSqEmbed q =
  let x = SU2.imagI q
      y = SU2.imagJ q
      z = SU2.imagK q
  in BP.≃-trans (Unit.embedSum (x * x) (y * y + z * z))
    (BP.+-cong (Unit.embedProd x x)
      (BP.≃-trans (Unit.embedSum (y * y) (z * z))
        (BP.+-cong (Unit.embedProd y y) (Unit.embedProd z z))))

smallContourFromChordSq : ∀ q →
  SU2.literalChordalDistanceSq q ≤ relativeChordRadiusSq →
  SmallContour q
smallContourFromChordSq q bound =
  let nn = BP.≤-respʳ-≃ (imagSqEmbed q)
        (Cast.bishopEmbedOrder (rationalImagNN q))
      upper = BP.≤-respˡ-≃ (imagSqEmbed q)
        (Cast.bishopEmbedOrder
          (RP.≤-trans (rationalImagBelowChord q)
            (RP.≤-trans bound radiusSqBelowQuarter)))
  in record
    { positiveScalar = BP.<-≤-trans
        (BP.p<q⇒p⋆<q⋆ (+ 0 / 1) (+ 1 / 2) (UP.positive⁻¹ (+ 1 / 2)))
        (Cast.bishopEmbedOrder (scalarHalfBelowFromChord q bound))
    ; imaginarySqInside = BP.≤-respˡ-≃ (BP.≃-symm (Seq.0≤x⇒∣x∣≃x nn)) upper
    }

-- Convert a single physical chord-square bound on the selected contour
-- family to the actual native chart admissions without a legacy chart.
pointAdmissionFromChordSq :
  ∀ {C} (g : NativeGeometry C) →
  (∀ bond step point →
    SU2.literalChordalDistanceSq (relativeUnit g bond step point)
      ≤ relativeChordRadiusSq) →
  PointAdmission g nativeSeriesChart
pointAdmissionFromChordSq g bound bond step point =
  smallContourFromChordSq (relativeUnit g bond step point) (bound bond step point)

-- Native relative contour: bound the actual gamma and coarse holonomies
-- separately and use the squared-chord triangle on their product.
-- This avoids both the legacy chart and the independent rational-valued
-- operator-norm representation. The physical inverse-link radius is
-- the same selected-source input already used by Path13 coercivity.
relativeContourChordSqFromRadius :
  ∀ {C} (g : NativeGeometry C) →
  Background.SelectedInverseLinkRadius13 (nativeBackground g) →
  ∀ bond step point →
  SU2.literalChordalDistanceSq (relativeUnit g bond step point)
    ≤ relativeChordRadiusSq
relativeContourChordSqFromRadius g radius bond step point =
  let
    source = nativeGeometryAt g bond
    start = Embed.embeddingCentre (Geometry.minusEmbedding source step)
    gamma = Geometry.literalGammaWord source step point
    coarseWord = Periodic.segmentWord (Geometry.coarseSegment source step)
    gammaValue = Geometry.literalGammaHolonomy source step point
    coarseValue = Geometry.coarseBackgroundHolonomy source step
    coarseLength = Length.path13CoarseWordLengthIs13 bond
    gammaBound = Radius.pathChordSqBelowLengthBudget
      (nativeBackground g) radius start gamma 61
      (Length.gammaWordLengthAtMost61 source step point coarseLength)
    coarseBound = Radius.pathChordSqBelowLengthBudget
      (nativeBackground g) radius start coarseWord 13
      (subst (λ n → n Nat.≤ 13) (sym coarseLength) NP.≤-refl)
    inverseCoarseBound =
      subst (λ d → d ≤ Radius.chordBudget 13 * Radius.chordBudget 13)
        (sym (Radius.chordInverseExact coarseValue)) coarseBound
    productBound = Radius.unitProductChordBound gammaValue
      (Group.inverseRationalSU2 coarseValue)
      (Radius.chordBudget 61) (Radius.chordBudget 13)
      (Radius.chordBudgetPositive 60) (Radius.chordBudgetPositive 12)
      gammaBound inverseCoarseBound
    budgetExact :
      (Radius.chordBudget 61 + Radius.chordBudget 13)
        * (Radius.chordBudget 61 + Radius.chordBudget 13)
      ≡ relativeChordRadiusSq
    budgetExact = Ring.solve []
  in subst (λ upper →
      SU2.literalChordalDistanceSq (relativeUnit g bond step point) ≤ upper)
      budgetExact
      (subst (λ d → d ≤
        (Radius.chordBudget 61 + Radius.chordBudget 13)
        * (Radius.chordBudget 61 + Radius.chordBudget 13))
        (Radius.chordRadiusSqIsLiteral (relativeUnit g bond step point))
        productBound)

nativePointAdmissionFromPhysicalRadius :
  ∀ {C} (g : NativeGeometry C) →
  Background.SelectedInverseLinkRadius13 (nativeBackground g) →
  PointAdmission g nativeSeriesChart
nativePointAdmissionFromPhysicalRadius g radius =
  pointAdmissionFromChordSq g (relativeContourChordSqFromRadius g radius)

------------------------------------------------------------------------
-- Point AND outer selected chart relevance.  Reuse the original Bishop
-- square-reflection theorem and finite nat scaling.  No norm, convexity,
-- coefficient or independent outer-radius input is required.
------------------------------------------------------------------------

squareB : B.ℝ → B.ℝ
squareB x = B._*_ x x

vectorSqNonnegative : ∀ v → B.NonNegative (Poly.generatorSq (toVec3 v))
vectorSqNonnegative v =
  BP.nonNegx,y⇒nonNegx+y
    (SquareNN.bishopSquareNonnegative (v P.coordinateX))
    (BP.nonNegx,y⇒nonNegx+y
      (SquareNN.bishopSquareNonnegative (v P.coordinateY))
      (SquareNN.bishopSquareNonnegative (v P.coordinateZ)))

componentSqBelow : ∀ v k →
  B._≤_ (squareB (v k)) (Poly.generatorSq (toVec3 v))
componentSqBelow v P.coordinateX =
  BP.0≤y-x⇒x≤y
    (BP.≤-respʳ-≃
      (let open BP.ℝ-Solver in
       solve 3 (λ x y z → (y ⊕ z) ⊜ (x ⊕ (y ⊕ z)) ⊖ x)
         BP.≃-refl (squareB (v P.coordinateX))
           (squareB (v P.coordinateY)) (squareB (v P.coordinateZ)))
      (BP.nonNegx⇒0≤x (BP.nonNegx,y⇒nonNegx+y
        (SquareNN.bishopSquareNonnegative (v P.coordinateY))
        (SquareNN.bishopSquareNonnegative (v P.coordinateZ)))))
componentSqBelow v P.coordinateY =
  BP.0≤y-x⇒x≤y
    (BP.≤-respʳ-≃
      (let open BP.ℝ-Solver in
       solve 3 (λ x y z → (x ⊕ z) ⊜ (x ⊕ (y ⊕ z)) ⊖ y)
         BP.≃-refl (squareB (v P.coordinateX))
           (squareB (v P.coordinateY)) (squareB (v P.coordinateZ)))
      (BP.nonNegx⇒0≤x (BP.nonNegx,y⇒nonNegx+y
        (SquareNN.bishopSquareNonnegative (v P.coordinateX))
        (SquareNN.bishopSquareNonnegative (v P.coordinateZ)))))
componentSqBelow v P.coordinateZ =
  BP.0≤y-x⇒x≤y
    (BP.≤-respʳ-≃
      (let open BP.ℝ-Solver in
       solve 3 (λ x y z → (x ⊕ y) ⊜ (x ⊕ (y ⊕ z)) ⊖ z)
         BP.≃-refl (squareB (v P.coordinateX))
           (squareB (v P.coordinateY)) (squareB (v P.coordinateZ)))
      (BP.nonNegx⇒0≤x (BP.nonNegx,y⇒nonNegx+y
        (SquareNN.bishopSquareNonnegative (v P.coordinateX))
        (SquareNN.bishopSquareNonnegative (v P.coordinateY)))))

chordB : B.ℝ
chordB = Scalar.rationalCoordinateToBishop relativeChordRadius

logCoordBound : B.ℝ
logCoordBound = B._*_ twoB chordB

chordBNN : B.NonNegative chordB
chordBNN = BP.0≤x⇒nonNegx
  (Cast.bishopEmbedOrder (RP.nonNegative⁻¹ relativeChordRadius))

twoBNN : B.NonNegative twoB
twoBNN = BP.0≤x⇒nonNegx
  (Cast.bishopEmbedOrder (RP.nonNegative⁻¹ (+ 2 /q 1)))

logCoordBoundNN : B.NonNegative logCoordBound
logCoordBoundNN = BP.nonNegx,y⇒nonNegx*y twoBNN chordBNN

imaginaryAbsBound : ∀ q →
  SU2.literalChordalDistanceSq q ≤ relativeChordRadiusSq →
  ∀ k → B._≤_ (B.∣_∣ (fromVec3 (contourImaginary q) k)) chordB
imaginaryAbsBound q bound k =
  let
    v = fromVec3 (contourImaginary q)
    sqBound : B._≤_ (contourImagSq q) (squareB chordB)
    sqBound = BP.≤-respʳ-≃ (Unit.embedProd relativeChordRadius relativeChordRadius)
      (BP.≤-respˡ-≃ (imagSqEmbed q)
        (Cast.bishopEmbedOrder (RP.≤-trans (rationalImagBelowChord q) bound)))
  in Reflect.squareReflectsOnNonnegative
    (BP.nonNeg∣x∣ (v k)) chordBNN
    (BP.≤-respˡ-≃ (BP.≃-symm (AbsSquare.absoluteSquare (v k)))
      (BP.≤-trans (componentSqBelow v k) sqBound))

pointLogAbsBound : ∀ q (admission : SmallContour q) →
  SU2.literalChordalDistanceSq q ≤ relativeChordRadiusSq →
  ∀ k → B._≤_ (B.∣_∣ (seriesPrincipalLog q admission k)) logCoordBound
pointLogAbsBound q admission chord k =
  let
    s = contourImagSq q
    inside = imaginarySqInside admission
    v = fromVec3 (contourImaginary q)
    a = Series.arcSeries s inside
    sn = vectorSqNonnegative v
    an = BP.0≤x⇒nonNegx (Series.arcSeriesNonnegative s sn inside)
    absMul = BP.≃-trans (BP.∣x*y∣≃∣x∣*∣y∣ a (v k))
      (BP.*-congʳ (BP.nonNegx⇒∣x∣≃x an))
    ub = BP.*-mono-≤ an (BP.nonNeg∣x∣ (v k))
      (Series.arcSeriesBelowTwo s sn inside)
      (imaginaryAbsBound q chord k)
    coordinate : B._≃_ (seriesPrincipalLog q admission k) (B._*_ a (v k))
    coordinate = logCoordinate q admission k
  in BP.≤-respˡ-≃
    (BP.≃-symm (BP.≃-trans (BP.∣-∣-cong coordinate) absMul)) ub
  where
  logCoordinate : ∀ q (admission : SmallContour q) k →
    B._≃_ (seriesPrincipalLog q admission k)
      (B._*_ (Series.arcSeries (contourImagSq q) (imaginarySqInside admission))
        (fromVec3 (contourImaginary q) k))
  logCoordinate q admission P.coordinateX = BP.≃-refl
  logCoordinate q admission P.coordinateY = BP.≃-refl
  logCoordinate q admission P.coordinateZ = BP.≃-refl

squareFromAbsBound : ∀ x r → B._≤_ (B.∣_∣ x) r →
  B._≤_ (squareB x) (squareB r)
squareFromAbsBound x r bound =
  BP.≤-respˡ-≃ (AbsSquare.absoluteSquare x)
    (BP.*-mono-≤ (BP.nonNeg∣x∣ x) (BP.nonNeg∣x∣ x) bound bound)

scaledCoordinateSquareBound : ∀ x →
  B._≤_ (B.∣_∣ x) logCoordBound →
  B._≤_ (squareB (B._*_ twoB x)) (squareB (B._*_ twoB logCoordBound))
scaledCoordinateSquareBound x bound =
  squareFromAbsBound (B._*_ twoB x) (B._*_ twoB logCoordBound)
    (BP.≤-respˡ-≃
      (BP.≃-symm
        (BP.≃-trans (BP.∣x*y∣≃∣x∣*∣y∣ twoB x)
          (BP.*-congʳ (BP.nonNegx⇒∣x∣≃x twoBNN))))
      (BP.*-monoˡ-≤-nonNeg bound twoBNN))

coordinateBoundImpliesSmallLie : ∀ v →
  (∀ k → B._≤_ (B.∣_∣ (v k)) logCoordBound) → SmallLie v
coordinateBoundImpliesSmallLie v bound = record
  { wNonnegative = BP.nonNegx⇒0≤x
      (vectorSqNonnegative (λ k → B._*_ twoB (v k)))
  ; wBelowQuarter =
      BP.≤-trans
        (BP.≤-respʳ-≃
          (let open BP.ℝ-Solver in
           solve 0
             (let x = Κ (+ 2 / 1) ⊗ (Κ (+ 2 / 1) ⊗ Κ (+ 37 / 1024))
                  x2 = x ⊗ x
              in (x2 ⊕ (x2 ⊕ x2)) ⊜ Κ (+ 4107 / 65536))
             BP.≃-refl)
          (BP.+-mono-≤
            (scaledCoordinateSquareBound (v P.coordinateX) (bound P.coordinateX))
            (BP.+-mono-≤
              (scaledCoordinateSquareBound (v P.coordinateY) (bound P.coordinateY))
              (scaledCoordinateSquareBound (v P.coordinateZ) (bound P.coordinateZ)))))
        (Cast.bishopEmbedOrder
          (RP.<⇒≤ (RP.positive⁻¹ ((+ 1 /q 4) - (+ 4107 /q 65536)))))
  }

sumAbsUniform : ∀ {I : Set} (xs : List I) f r →
  (∀ i → B._≤_ (B.∣_∣ (f i)) r) →
  B._≤_ (B.∣_∣ (sumBishop xs f)) (Iter.natScale (length xs) r)
sumAbsUniform [] f r bound =
  BP.≤-reflexive (BP.nonNegx⇒∣x∣≃x BP.nonNeg0)
sumAbsUniform (i ∷ xs) f r bound =
  BP.≤-respʳ-≃ (BP.+-comm r (Iter.natScale (length xs) r))
    (BP.≤-trans (BP.∣x+y∣≤∣x∣+∣y∣ (f i) (sumBishop xs f))
      (BP.+-mono-≤ (bound i) (sumAbsUniform xs f r bound)))

weightB : B.ℝ
weightB = Scalar.rationalCoordinateToBishop R147.siteWeightℚ

weightBNN : B.NonNegative weightB
weightBNN = BP.0≤x⇒nonNegx
  (Cast.bishopEmbedOrder (RP.nonNegative⁻¹ R147.siteWeightℚ))

weightedPointLogAbsBound : ∀ v k →
  B._≤_ (B.∣_∣ (v k)) logCoordBound →
  B._≤_ (B.∣_∣ (scale R147.siteWeightℚ v k)) (B._*_ weightB logCoordBound)
weightedPointLogAbsBound v k bound =
  BP.≤-respˡ-≃
    (BP.≃-symm (BP.≃-trans (BP.∣x*y∣≃∣x∣*∣y∣ weightB (v k))
      (BP.*-congʳ (BP.nonNegx⇒∣x∣≃x weightBNN))))
    (BP.*-monoˡ-≤-nonNeg bound weightBNN)

blockWeightNormalized : B._≃_
  (Iter.natScale (length (Carrier.elements (Centered.centeredBlockFinite 6)))
    (B._*_ weightB logCoordBound)) logCoordBound
blockWeightNormalized rewrite Centered.centeredBlockEnumerationLength 6 =
  BP.≃-trans (Iter.natScaleAsEmbeddedNatMul 28561 (B._*_ weightB logCoordBound))
    (let open BP.ℝ-Solver in
     solve 1 (λ x → Κ (+ 28561 / 1) ⊗ (Κ (+ 1 / 28561) ⊗ x) ⊜ x)
       BP.≃-refl logCoordBound)

nativeInputsFromPhysicalRadius :
  ∀ {C} (g : NativeGeometry C) →
  Background.SelectedInverseLinkRadius13 (nativeBackground g) → Inputs C
nativeInputsFromPhysicalRadius g radius =
  let
    admission = nativePointAdmissionFromPhysicalRadius g radius
    pointBound = λ bond step point k →
      pointLogAbsBound (relativeUnit g bond step point) (admission bond step point)
        (relativeContourChordSqFromRadius g radius bond step point) k
    outerBound = λ bond step k →
      BP.≤-respʳ-≃ blockWeightNormalized
        (sumAbsUniform (Carrier.elements (Centered.centeredBlockFinite 6))
          (λ point → scale R147.siteWeightℚ
            (pointYFrom g nativeSeriesChart admission bond step point) k)
          (B._*_ weightB logCoordBound)
          (λ point → weightedPointLogAbsBound
            (pointYFrom g nativeSeriesChart admission bond step point) k
            (pointBound bond step point k)))
  in record
    { geometry = g
    ; chart = nativeSeriesChart
    ; pointLogAdmissible = admission
    ; pointRelevant = λ bond step point →
        coordinateBoundImpliesSmallLie
          (pointYFrom g nativeSeriesChart admission bond step point)
          (pointBound bond step point)
    ; outerRelevant = λ bond step →
        coordinateBoundImpliesSmallLie
          (outerYFrom g nativeSeriesChart admission bond step)
          (outerBound bond step)
    }

------------------------------------------------------------------------
-- Root-free quaternion candidate on the SAME native averaged vector.
-- The adjoint generator is 2y: do not evaluate quaternion coefficients
-- at physicalW y. Unit norm and exp/log semantic identification are
-- separate theorems, not fields installed by this constructor.
------------------------------------------------------------------------

quaternionW : BishopLie → B.ℝ
quaternionW y = Poly.generatorSq (toVec3 y)

quaternionWQuarterAdjoint : ∀ y →
  B._≃_ (quaternionW y) (B._*_ (B._⋆ (+ 1 / 4)) (physicalW y))
quaternionWQuarterAdjoint y =
  let open BP.ℝ-Solver in
  solve 3
    (λ x y z →
      (x ⊗ x) ⊕ ((y ⊗ y) ⊕ (z ⊗ z))
      ⊜ Κ (+ 1 / 4) ⊗
        (((Κ (+ 2 / 1) ⊗ x) ⊗ (Κ (+ 2 / 1) ⊗ x))
        ⊕ (((Κ (+ 2 / 1) ⊗ y) ⊗ (Κ (+ 2 / 1) ⊗ y))
        ⊕ ((Κ (+ 2 / 1) ⊗ z) ⊗ (Κ (+ 2 / 1) ⊗ z)))))
    BP.≃-refl (y P.coordinateX) (y P.coordinateY) (y P.coordinateZ)

quaternionWBelowSixteenth : ∀ y → SmallLie y →
  B._≤_ (quaternionW y) (B._⋆ (+ 1 / 16))
quaternionWBelowSixteenth y p =
  BP.≤-respˡ-≃ (BP.≃-symm (quaternionWQuarterAdjoint y))
    (BP.≤-respʳ-≃
      (let open BP.ℝ-Solver in
       solve 0 (Κ (+ 1 / 4) ⊗ Κ (+ 1 / 4) ⊜ Κ (+ 1 / 16)) BP.≃-refl)
      (BP.*-monoʳ-≤-nonNeg (wBelowQuarter p)
        (BP.0≤x⇒nonNegx
          (Cast.bishopEmbedOrder (RP.nonNegative⁻¹ (+ 1 /q 4))))))

quaternionSignedWInside : ∀ y → SmallLie y →
  B._≤_ (B.∣_∣ (B.- (quaternionW y))) Half.bishopQuarter
quaternionSignedWInside y p =
  BP.≤-respˡ-≃
    (BP.≃-symm (BP.≃-trans BP.∣-x∣≃∣x∣
      (BP.nonNegx⇒∣x∣≃x (vectorSqNonnegative y))))
    (BP.≤-trans (quaternionWBelowSixteenth y p)
      (Cast.bishopEmbedOrder
        (RP.<⇒≤ (RP.positive⁻¹ ((+ 1 /q 4) - (+ 1 /q 16))))))

quaternionA quaternionB : (y : BishopLie) → SmallLie y → B.ℝ
quaternionA y p = Series.aSeries (B.- (quaternionW y)) (quaternionSignedWInside y p)
quaternionB y p = Series.bSeries (B.- (quaternionW y)) (quaternionSignedWInside y p)

rootFreeQuaternionCandidate : (y : BishopLie) → SmallLie y → Quaternion.QuaternionB
rootFreeQuaternionCandidate y p =
  Quaternion.quaternionB
    (B._-_ B.1ℝ (B._*_ (quaternionW y) (quaternionA y p)))
    (Quaternion.scaleVecB
      (B._-_ B.1ℝ (B._*_ (quaternionW y) (quaternionB y p)))
      (Quaternion.vec3B (y P.coordinateX) (y P.coordinateY) (y P.coordinateZ)))

nativeAveragedQuaternionCandidate :
  ∀ {C} (g : NativeGeometry C) →
  Background.SelectedInverseLinkRadius13 (nativeBackground g) →
  Family.Path13PositiveBond → Nat → Quaternion.QuaternionB
nativeAveragedQuaternionCandidate g radius bond step =
  let inputs = nativeInputsFromPhysicalRadius g radius
  in rootFreeQuaternionCandidate (outerY inputs bond step)
       (outerRelevant inputs bond step)
