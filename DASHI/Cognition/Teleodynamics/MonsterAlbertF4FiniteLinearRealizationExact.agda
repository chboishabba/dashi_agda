module DASHI.Cognition.Teleodynamics.MonsterAlbertF4FiniteLinearRealizationExact where

------------------------------------------------------------------------
-- FINITE ALBERT-SHAPE 54 -> 53  INTO LITERAL RATIONAL ALBERT STATES
--
-- DASHI composition theorem.
--
-- This module composes two already-owned repository constructions:
--
--   1. the finite ternary Albert SHAPE
--        T3^3 <-> ScalarLine + NonOrigin26;
--   2. the canonical diagonal codebook
--        T3^3 -> H_3(O_Q),   (x,y,z) |-> diag(x,y,z),
--      which is injective and preserves the finite pointwise product and cubic
--      code inside the literal rational Albert algebra.
--
-- The result is an injective state realization of the finite 54/53 shape into
-- TWO copies of the literal rational Albert state carrier.  Transporting the
-- ternary product/cubic through the exact 27-point shape makes this realization
-- an exact finite-image Jordan/cubic intertwiner.
--
-- It is NOT a linear-span equivalence and it does not extend the transported
-- Monster permutation action to a rational-linear Albert automorphism.
--
-- Crucially, the distinguished `ScalarLine` point of the finite SHAPE is the
-- ternary ORIGIN.  Under the canonical diagonal codebook it maps to Albert ZERO.
-- The Albert UNIT is instead the positive ternary corner (1,1,1).  Thus the
-- finite shape label `ScalarLine` is a carrier partition, not the actual
-- scalar/unit summand of H_3(O_Q) under this product-preserving realization.
--
-- Historical/source attribution remains with the existing Albert/F4 sources;
-- this finite-to-linear embedding is a DASHI composition of repo-native maps.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape
import DASHI.Cognition.Teleodynamics.Ternary27AlbertDiagonalCodebookExact as Codebook
import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as Albert

------------------------------------------------------------------------
-- 1. Reconstruct the exact same finite pair shape used by the 54->53 lane.
------------------------------------------------------------------------

cubeAlbertPair : Exceptional.AlbertPairCarrier
Exceptional.AlbertPairCarrier.leftAlbert cubeAlbertPair = Shape.cubeAlbertCarrier
Exceptional.AlbertPairCarrier.rightAlbert cubeAlbertPair = Shape.cubeAlbertCarrier

CubeAlbertPair54 : Set
CubeAlbertPair54 = Exceptional.AlbertPair54 cubeAlbertPair

CubeReducedAlbert53 : Set
CubeReducedAlbert53 = Exceptional.ReducedAlbertPair53 cubeAlbertPair

RationalAlbertPair : Set
RationalAlbertPair = Albert.RationalAlbert ⊎ Albert.RationalAlbert

------------------------------------------------------------------------
-- 2. One finite Albert-shape summand -> literal rational Albert state.
------------------------------------------------------------------------

encodeAlbertShape : Shape.CubeAlbert27 → Albert.RationalAlbert
encodeAlbertShape shape = Codebook.encodePoint (Shape.fromAlbertShape shape)

encodeAlbertShapeInjective : ∀ {left right} →
  encodeAlbertShape left ≡ encodeAlbertShape right → left ≡ right
encodeAlbertShapeInjective {left} {right} equality =
  trans
    (sym (Shape.toAfterFrom left))
    (trans
      (cong Shape.toAlbertShape (Codebook.encodeInjective equality))
      (Shape.toAfterFrom right))

------------------------------------------------------------------------
-- 3. Transport the finite product/cubic through the exact 27-point shape.
------------------------------------------------------------------------

shapeProduct : Shape.CubeAlbert27 → Shape.CubeAlbert27 → Shape.CubeAlbert27
shapeProduct left right =
  Shape.toAlbertShape
    (Codebook.pointMul
      (Shape.fromAlbertShape left)
      (Shape.fromAlbertShape right))

shapeCubicCode : Shape.CubeAlbert27 → ℚ
shapeCubicCode shape =
  Codebook.ternaryCubicCode (Shape.fromAlbertShape shape)

encodeAlbertShapePreservesProduct : (left right : Shape.CubeAlbert27) →
  Albert.jordanProduct (encodeAlbertShape left) (encodeAlbertShape right)
  ≡ encodeAlbertShape (shapeProduct left right)
encodeAlbertShapePreservesProduct left right =
  trans
    (Codebook.encodePreservesProduct
      (Shape.fromAlbertShape left)
      (Shape.fromAlbertShape right))
    (cong Codebook.encodePoint
      (sym
        (Shape.fromAfterTo
          (Codebook.pointMul
            (Shape.fromAlbertShape left)
            (Shape.fromAlbertShape right)))))

encodeAlbertShapePreservesCubic : (shape : Shape.CubeAlbert27) →
  Albert.cubicNorm (encodeAlbertShape shape) ≡ shapeCubicCode shape
encodeAlbertShapePreservesCubic shape =
  Codebook.encodePreservesCubicNorm (Shape.fromAlbertShape shape)

------------------------------------------------------------------------
-- 4. Full 54-state embedding and injection.
------------------------------------------------------------------------

encodePair54 : CubeAlbertPair54 → RationalAlbertPair
encodePair54 (inj₁ left) = inj₁ (encodeAlbertShape left)
encodePair54 (inj₂ right) = inj₂ (encodeAlbertShape right)

leftAlbertOrZero : RationalAlbertPair → Albert.RationalAlbert
leftAlbertOrZero (inj₁ state) = state
leftAlbertOrZero (inj₂ _) = Codebook.zeroAlbert

rightAlbertOrZero : RationalAlbertPair → Albert.RationalAlbert
rightAlbertOrZero (inj₁ _) = Codebook.zeroAlbert
rightAlbertOrZero (inj₂ state) = state

encodePair54Injective : ∀ {left right} →
  encodePair54 left ≡ encodePair54 right → left ≡ right
encodePair54Injective {inj₁ left} {inj₁ right} equality =
  cong inj₁
    (encodeAlbertShapeInjective (cong leftAlbertOrZero equality))
encodePair54Injective {inj₁ left} {inj₂ right} ()
encodePair54Injective {inj₂ left} {inj₁ right} ()
encodePair54Injective {inj₂ left} {inj₂ right} equality =
  cong inj₂
    (encodeAlbertShapeInjective (cong rightAlbertOrZero equality))

------------------------------------------------------------------------
-- 5. Residual 53-state embedding and injection.
------------------------------------------------------------------------

encodeResidual53 : CubeReducedAlbert53 → RationalAlbertPair
encodeResidual53 (inj₁ leftJ0) =
  inj₁ (encodeAlbertShape (inj₂ leftJ0))
encodeResidual53 (inj₂ rightAlbert) =
  inj₂ (encodeAlbertShape rightAlbert)

shapeJ0OrDefault : Shape.CubeAlbert27 → Shape.NonOrigin26
shapeJ0OrDefault (inj₁ _) = Shape.nnn
shapeJ0OrDefault (inj₂ j0) = j0

encodeResidual53Injective : ∀ {left right} →
  encodeResidual53 left ≡ encodeResidual53 right → left ≡ right
encodeResidual53Injective {inj₁ left} {inj₁ right} equality =
  cong inj₁
    (cong shapeJ0OrDefault
      (encodeAlbertShapeInjective (cong leftAlbertOrZero equality)))
encodeResidual53Injective {inj₁ left} {inj₂ right} ()
encodeResidual53Injective {inj₂ left} {inj₁ right} ()
encodeResidual53Injective {inj₂ left} {inj₂ right} equality =
  cong inj₂
    (encodeAlbertShapeInjective (cong rightAlbertOrZero equality))

------------------------------------------------------------------------
-- 6. Distinguished-point audit: removed shape scalar -> zero, unit elsewhere.
------------------------------------------------------------------------

removedShapeScalar54 : CubeAlbertPair54
removedShapeScalar54 = inj₁ (inj₁ Exceptional.scalarLine)

removedShapeScalarMapsToZero :
  encodePair54 removedShapeScalar54 ≡ inj₁ Codebook.zeroAlbert
removedShapeScalarMapsToZero = refl

leftPositiveCornerUnit54 : CubeAlbertPair54
leftPositiveCornerUnit54 = inj₁ (Shape.toAlbertShape Geometry.positiveCorner)

leftPositiveCornerMapsToUnit :
  encodePair54 leftPositiveCornerUnit54 ≡ inj₁ Albert.albertUnit
leftPositiveCornerMapsToUnit = cong inj₁ Codebook.positiveCornerToUnit

------------------------------------------------------------------------
-- 7. What is and is not paid.
------------------------------------------------------------------------

record FiniteLinearRealizationBoundary : Set where
  constructor finite-linear-realization-boundary
  field
    finite54StateEmbeddingPaid : Bool
    finite54StateEmbeddingInjective : Bool
    residual53StateEmbeddingPaid : Bool
    residual53StateEmbeddingInjective : Bool
    finiteShapeProductIntertwinesAlbertJordan : Bool
    finiteShapeCubicIntertwinesAlbertCubic : Bool
    removedShapeScalarMapsToAlbertZero : Bool
    leftPositiveCornerMapsToAlbertUnit : Bool
    removedShapeScalarMapsToAlbertUnit : Bool
    shapeScalarSummandMatchesActualAlbertScalarUnit : Bool
    finiteImageEqualsWholeAlbertVectorSpace : Bool
    finiteActionLiftToLinearAlbertPaid : Bool
    cubicUnitRigidityApplicableToTransportedFiniteAction : Bool
    nextResidual : String
open FiniteLinearRealizationBoundary public

canonicalFiniteLinearRealizationBoundary : FiniteLinearRealizationBoundary
canonicalFiniteLinearRealizationBoundary =
  finite-linear-realization-boundary
    true true true true
    true true
    true true
    false false false false false
    "state-carrier realization is paid and the transported finite pointwise product/cubic agree exactly with the literal Albert Jordan product/cubic on the diagonal finite image. But the named finite Shape ScalarLine is the ternary origin, hence maps to Albert zero; the actual Albert unit is the positive corner. The current 1+26 SHAPE partition is therefore not the native scalar/unit + traceless decomposition under this algebra-preserving realization. The live action theorem is to extend/lift the transported finite Monster action and an independent classical-F4 comparator to same-object rational-linear Albert actions, with cubic-norm preservation, actual-unit fixation, and an explicit sheet action. Only after that can norm+unit rigidity discharge Jordan compatibility. Do not identify the removed-point stabilizer with the Albert-unit stabilizer."

------------------------------------------------------------------------
-- 8. Explicit non-promotions.
------------------------------------------------------------------------

data FiniteStateEmbeddingCreatesLinearAction : Set where
data FiniteImageCreatesWholeAlbertSpace : Set where
data RemovedShapeScalarCreatesAlbertUnit : Set where
data ShapeScalarLabelCreatesNativeScalarDecomposition : Set where
data StateEmbeddingCreatesClassicalF4Recognition : Set where

aStateEmbeddingDoesNotCreateLinearAction :
  FiniteStateEmbeddingCreatesLinearAction → ⊥
aStateEmbeddingDoesNotCreateLinearAction ()

finiteImageDoesNotCreateWholeAlbertSpace :
  FiniteImageCreatesWholeAlbertSpace → ⊥
finiteImageDoesNotCreateWholeAlbertSpace ()

removedShapeScalarDoesNotCreateAlbertUnit :
  RemovedShapeScalarCreatesAlbertUnit → ⊥
removedShapeScalarDoesNotCreateAlbertUnit ()

shapeScalarLabelDoesNotCreateNativeScalarDecomposition :
  ShapeScalarLabelCreatesNativeScalarDecomposition → ⊥
shapeScalarLabelDoesNotCreateNativeScalarDecomposition ()

stateEmbeddingDoesNotCreateClassicalF4Recognition :
  StateEmbeddingCreatesClassicalF4Recognition → ⊥
stateEmbeddingDoesNotCreateClassicalF4Recognition ()
