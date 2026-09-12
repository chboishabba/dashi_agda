module DASHI.Wikimedia.IbrahimMonster3BMathlibCyclotomicFieldScalarExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Wikimedia.IbrahimMonster3BCyclotomicScalarExtensionInteropExact as Scalar

------------------------------------------------------------------------
-- MATHLIB NATIVE CYCLOTOMIC-FIELD ROUTE FOR THE 3B SCALAR EXTENSION
------------------------------------------------------------------------

washington : Attribution.AttributedSource
washington = Attribution.mkDOISource
  "Lawrence C. Washington"
  "Introduction to Cyclotomic Fields, Second Edition"
  "Springer Graduate Texts in Mathematics 83"
  "1997"
  "10.1007/978-1-4612-1934-7"
  "https://doi.org/10.1007/978-1-4612-1934-7"
  Attribution.academicArticleSource
  "primary algebraic source for cyclotomic fields and primitive-root presentations; not authority for a cross-kernel type equivalence"
  Attribution.publicAttribution

washingtonAttribution = Snowball.canonicalSourceRoleSnowballReceipt washington

record MathlibCyclotomicFieldCoordinate : Set where
  constructor mathlib-cyclotomic-field-coordinate
  field
    repository : String
    sourceBlobSha : String
    cyclotomicSourceFile : String
    numberFieldCyclotomicSourceFile : String
    algebraicClosureSourceFile : String
    cyclotomicFieldType : String
    algebraicClosureType : String
    cyclotomicFieldCharZeroInstance : String
    cyclotomicExtensionInstance : String
    integralPowerBasisTheorem : String
    integralPowerBasisGeneratorTheorem : String
    integralPowerBasisDimensionTheorem : String
    algebraicClosureIsAlgClosedInstance : String
    phiThreeIsTwo : Bool
    upstreamKernelChecked : Bool
    replayedByAgdaKernelHere : Bool
open MathlibCyclotomicFieldCoordinate public

canonicalMathlibCyclotomicFieldCoordinate : MathlibCyclotomicFieldCoordinate
canonicalMathlibCyclotomicFieldCoordinate =
  mathlib-cyclotomic-field-coordinate
    "leanprover-community/mathlib4"
    "70f3f13433ba3d82a15a7cae679abac9128f102b"
    "Mathlib/NumberTheory/Cyclotomic/Basic.lean"
    "Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean"
    "Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean"
    "CyclotomicField 3 ℚ"
    "AlgebraicClosure (CyclotomicField 3 ℚ)"
    "CyclotomicField.instCharZero"
    "CyclotomicField.isCyclotomicExtension"
    "IsPrimitiveRoot.integralPowerBasisOfPrimePow"
    "IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen"
    "IsPrimitiveRoot.integralPowerBasisOfPrimePow_dim"
    "AlgebraicClosure.isAlgClosed"
    true true false

------------------------------------------------------------------------
-- Power-basis reading of the remaining transport.
--
-- Specializing p=3,k=1 gives φ(3)=2.  The selected primitive cubic root is the
-- power-basis generator.  Hence the remaining cross-kernel object is exactly
-- the coordinate equivalence (u,v) ↔ u + v*zeta, not an arbitrary abstract
-- two-dimensional-vector-space isomorphism.
------------------------------------------------------------------------

record DashiCyclotomic3ToMathlibCyclotomicFieldTransport : Set₁ where
  field
    MathlibCyclotomicField3 : Set
    primitiveZeta3 : MathlibCyclotomicField3
    addField : MathlibCyclotomicField3 → MathlibCyclotomicField3 → MathlibCyclotomicField3
    multiplyField : MathlibCyclotomicField3 → MathlibCyclotomicField3 → MathlibCyclotomicField3
    zeroField oneField : MathlibCyclotomicField3

    powerBasisDimensionIsTwo : Set
    primitiveZetaIsPowerBasisGenerator : Set
    everyElementHasUniquePairCoordinates : Set

    toCyclotomicField : C3.Cyclotomic3 → MathlibCyclotomicField3
    fromCyclotomicField : MathlibCyclotomicField3 → C3.Cyclotomic3

    fromAfterTo :
      (x : C3.Cyclotomic3) →
      fromCyclotomicField (toCyclotomicField x) ≡ x
    toAfterFrom :
      (x : MathlibCyclotomicField3) →
      toCyclotomicField (fromCyclotomicField x) ≡ x

    preservesZero : toCyclotomicField C3.zero ≡ zeroField
    preservesOne : toCyclotomicField C3.one ≡ oneField
    preservesZeta : toCyclotomicField C3.zeta ≡ primitiveZeta3

    preservesAddition :
      (x y : C3.Cyclotomic3) →
      toCyclotomicField (Schrodinger.addC3 x y)
      ≡ addField (toCyclotomicField x) (toCyclotomicField y)

    preservesMultiplication :
      (x y : C3.Cyclotomic3) →
      toCyclotomicField (C3.multiply x y)
      ≡ multiplyField (toCyclotomicField x) (toCyclotomicField y)

    primitiveZetaSquaredMatches :
      multiplyField primitiveZeta3 primitiveZeta3
      ≡ toCyclotomicField C3.zetaSquared

    primitiveZetaCubedIsOne :
      multiplyField (toCyclotomicField C3.zetaSquared) primitiveZeta3
      ≡ oneField
open DashiCyclotomic3ToMathlibCyclotomicFieldTransport public

record MathlibAlgebraicClosureLift
    (pairWeld : DashiCyclotomic3ToMathlibCyclotomicFieldTransport) : Set₁ where
  field
    algebraicClosureTargetIsAlgClosed : Set
    cyclotomicFieldToAlgebraicClosureInjective : Set
    pairPresentationIsCyclotomicField : Set
    dashiPairPresentationIsCyclotomicField : Set
    scalarExtension : Scalar.Cyclotomic3ScalarExtension
open MathlibAlgebraicClosureLift public

data DimensionTwoCreatesPairPresentationEquivalence : Set where
data PowerBasisDimensionCreatesCoordinateWeld : Set where
data CyclotomicFieldNameCreatesSelectedPrimitiveRoot : Set where
data AlgebraicClosureInstanceCreatesDashiTransport : Set where
data QidCreatesCyclotomicEquivalence : Set where
data DeweyCreatesCyclotomicEquivalence : Set where
data OeisCreatesCyclotomicEquivalence : Set where

pairPresentationDoesNotFollowFromDimensionTwo :
  DimensionTwoCreatesPairPresentationEquivalence → ⊥
pairPresentationDoesNotFollowFromDimensionTwo ()

powerBasisDimensionDoesNotCreateCoordinateWeld :
  PowerBasisDimensionCreatesCoordinateWeld → ⊥
powerBasisDimensionDoesNotCreateCoordinateWeld ()

cyclotomicFieldNameDoesNotSelectPrimitiveRoot :
  CyclotomicFieldNameCreatesSelectedPrimitiveRoot → ⊥
cyclotomicFieldNameDoesNotSelectPrimitiveRoot ()

algebraicClosureInstanceDoesNotCreateDashiTransport :
  AlgebraicClosureInstanceCreatesDashiTransport → ⊥
algebraicClosureInstanceDoesNotCreateDashiTransport ()

qidDoesNotCreateCyclotomicEquivalence : QidCreatesCyclotomicEquivalence → ⊥
qidDoesNotCreateCyclotomicEquivalence ()

deweyDoesNotCreateCyclotomicEquivalence : DeweyCreatesCyclotomicEquivalence → ⊥
deweyDoesNotCreateCyclotomicEquivalence ()

oeisDoesNotCreateCyclotomicEquivalence : OeisCreatesCyclotomicEquivalence → ⊥
oeisDoesNotCreateCyclotomicEquivalence ()

record MathlibCyclotomicExternalCoordinates : Set where
  constructor mathlib-cyclotomic-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasCyclotomicEquivalenceAuthority : Bool
open MathlibCyclotomicExternalCoordinates public

canonicalMathlibCyclotomicExternalCoordinates : MathlibCyclotomicExternalCoordinates
canonicalMathlibCyclotomicExternalCoordinates =
  mathlib-cyclotomic-external-coordinates
    "Q1055807"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no cyclotomic-field presentation, primitive-root, power-basis coordinate, algebraic-closure, scalar-extension, FDRep, character, or intertwiner authority"
    false

record MathlibCyclotomicScalarExtensionFrontier : Set where
  constructor mathlib-cyclotomic-scalar-extension-frontier
  field
    mathlibCyclotomicFieldConstructionLocated : Bool
    mathlibCyclotomicFieldCharZeroPaidUpstream : Bool
    mathlibCyclotomicExtensionPaidUpstream : Bool
    primitiveRootPowerBasisPaidUpstream : Bool
    powerBasisDimensionTwoPaidUpstream : Bool
    algebraicClosureTargetIsAlgClosedPaidUpstream : Bool
    dashiPairCoordinateWeldPaid : Bool
    selectedPrimitiveRootSameObjectPaid : Bool
    genericScalarExtensionInstantiated : Bool
    schrodingerScalarExtensionPaid : Bool
    nextResidual : String
open MathlibCyclotomicScalarExtensionFrontier public

currentMathlibCyclotomicScalarExtensionFrontier :
  MathlibCyclotomicScalarExtensionFrontier
currentMathlibCyclotomicScalarExtensionFrontier =
  mathlib-cyclotomic-scalar-extension-frontier
    true true true true true true
    false false false false
    "specialize the mathlib primitive-root power basis to p=3,k=1 and construct the cross-kernel coordinate weld sending DASHI cyclotomic3 u v to u + v*primitiveZeta3, with inverse given by the unique two power-basis coordinates. Prove the existing DASHI multiplication formula matches the cyclotomic relation zeta^2+zeta+1=0; then compose the canonical algebra map into AlgebraicClosure (CyclotomicField 3 ℚ) to inhabit Cyclotomic3ScalarExtension. Power-basis dimension two, Washington DOI/QID/Dewey/OEIS coordinates, or matching formulas do not by themselves create the cross-kernel equality."
