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
    algebraicClosureSourceFile : String
    cyclotomicFieldType : String
    algebraicClosureType : String
    cyclotomicFieldCharZeroInstance : String
    cyclotomicExtensionInstance : String
    algebraicClosureIsAlgClosedInstance : String
    upstreamKernelChecked : Bool
    replayedByAgdaKernelHere : Bool
open MathlibCyclotomicFieldCoordinate public

canonicalMathlibCyclotomicFieldCoordinate : MathlibCyclotomicFieldCoordinate
canonicalMathlibCyclotomicFieldCoordinate =
  mathlib-cyclotomic-field-coordinate
    "leanprover-community/mathlib4"
    "70f3f13433ba3d82a15a7cae679abac9128f102b"
    "Mathlib/NumberTheory/Cyclotomic/Basic.lean"
    "Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean"
    "CyclotomicField 3 ℚ"
    "AlgebraicClosure (CyclotomicField 3 ℚ)"
    "CyclotomicField.instCharZero"
    "CyclotomicField.isCyclotomicExtension"
    "AlgebraicClosure.isAlgClosed"
    true false

record DashiCyclotomic3ToMathlibCyclotomicFieldTransport : Set₁ where
  field
    MathlibCyclotomicField3 : Set
    primitiveZeta3 : MathlibCyclotomicField3
    addField : MathlibCyclotomicField3 → MathlibCyclotomicField3 → MathlibCyclotomicField3
    multiplyField : MathlibCyclotomicField3 → MathlibCyclotomicField3 → MathlibCyclotomicField3
    zeroField oneField : MathlibCyclotomicField3

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
data CyclotomicFieldNameCreatesSelectedPrimitiveRoot : Set where
data AlgebraicClosureInstanceCreatesDashiTransport : Set where
data QidCreatesCyclotomicEquivalence : Set where
data DeweyCreatesCyclotomicEquivalence : Set where
data OeisCreatesCyclotomicEquivalence : Set where

pairPresentationDoesNotFollowFromDimensionTwo :
  DimensionTwoCreatesPairPresentationEquivalence → ⊥
pairPresentationDoesNotFollowFromDimensionTwo ()

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
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no cyclotomic-field presentation, primitive-root, algebraic-closure, scalar-extension, FDRep, character, or intertwiner authority"
    false

record MathlibCyclotomicScalarExtensionFrontier : Set where
  constructor mathlib-cyclotomic-scalar-extension-frontier
  field
    mathlibCyclotomicFieldConstructionLocated : Bool
    mathlibCyclotomicFieldCharZeroPaidUpstream : Bool
    mathlibCyclotomicExtensionPaidUpstream : Bool
    algebraicClosureTargetIsAlgClosedPaidUpstream : Bool
    dashiPairPresentationEquivalencePaid : Bool
    selectedPrimitiveRootSameObjectPaid : Bool
    genericScalarExtensionInstantiated : Bool
    schrodingerScalarExtensionPaid : Bool
    nextResidual : String
open MathlibCyclotomicScalarExtensionFrontier public

currentMathlibCyclotomicScalarExtensionFrontier :
  MathlibCyclotomicScalarExtensionFrontier
currentMathlibCyclotomicScalarExtensionFrontier =
  mathlib-cyclotomic-scalar-extension-frontier
    true true true true
    false false false false
    "construct DashiCyclotomic3ToMathlibCyclotomicFieldTransport by identifying the rational-pair presentation u+v*zeta with CyclotomicField 3 ℚ at a selected primitive cubic root. Then compose the canonical algebra map into AlgebraicClosure (CyclotomicField 3 ℚ) to inhabit the existing Cyclotomic3ScalarExtension. After that, extend Schrodinger states pointwise and prove translation/modulation preservation. Washington DOI/QID/Dewey/OEIS coordinates, dimension two, and the existence of mathlib CyclotomicField do not create the pair-presentation equivalence."
