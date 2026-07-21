module DASHI.Topology.LocalGlobalMapDiagnostics where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational using (ℚ; 0ℚ)

open import Verification.JacobianCounterexampleKernel as J
  using
    ( Point3
    ; F
    ; Injective
    ; _≢_
    ; jacobianDeterminantAt
    ; alpogePolynomialMap
    ; jacobianEverywhereNonzero
    ; pZero
    ; pPositive
    ; pNegative
    ; target
    ; pZeroNotPositive
    ; pZeroPositiveCollision
    ; F-notInjective
    )

------------------------------------------------------------------------
-- Local and global properties are deliberately different types.

record LocallyNonsingular
    {X : Set}
    (determinantAt : X → ℚ)
    : Set where
  constructor locallyNonsingular
  field
    determinantNonzeroAt : (x : X) → determinantAt x ≢ 0ℚ

record DisplayedFiniteFibre
    {X Y : Set}
    (f : X → Y)
    : Set where
  constructor displayedFiniteFibre
  field
    targetValue : Y
    firstPoint secondPoint thirdPoint : X
    firstSecondDistinct : firstPoint ≢ secondPoint
    firstImage : f firstPoint ≡ targetValue
    secondImage : f secondPoint ≡ targetValue
    thirdImage : f thirdPoint ≡ targetValue

record GlobalMapDiagnostics
    {X Y : Set}
    (f : X → Y)
    : Set₁ where
  field
    localDifferentialCertificate : Set
    properAtInfinityCertificate : Set
    genericFibreDegreeCertificate : Set
    monodromyCertificate : Set
    globalInjectivityCertificate : Set

-- The open analytic/topological quantities are packaged separately.  A local
-- determinant calculation must not manufacture any of them.
record GlobalGeometryAuthority : Set₁ where
  field
    properAtInfinity : Set
    genericFibreDegree : Nat
    genericFibreDegreeLaw : Set
    monodromyRepresentation : Set
    boundaryEscapeClassification : Set

record LocalWithoutGlobalInjectivity : Set₁ where
  constructor localWithoutGlobalInjectivity
  field
    X Y : Set
    map : X → Y
    determinantAt : X → ℚ
    localNonsingularity : LocallyNonsingular determinantAt
    notGloballyInjective : (Injective map → ⊥)

alpogeLocalNonsingularity :
  LocallyNonsingular
    (jacobianDeterminantAt alpogePolynomialMap)
alpogeLocalNonsingularity =
  locallyNonsingular jacobianEverywhereNonzero

alpogeDisplayedThreePointFibre : DisplayedFiniteFibre F
alpogeDisplayedThreePointFibre =
  displayedFiniteFibre
    target
    pZero
    pPositive
    pNegative
    pZeroNotPositive
    J.pZeroImage
    J.pPositiveImage
    J.pNegativeImage

localNonsingularityDoesNotImplyGlobalInjectivity :
  LocalWithoutGlobalInjectivity
localNonsingularityDoesNotImplyGlobalInjectivity =
  localWithoutGlobalInjectivity
    Point3
    Point3
    F
    (jacobianDeterminantAt alpogePolynomialMap)
    alpogeLocalNonsingularity
    F-notInjective

record LocalGlobalDiagnosticsReceipt : Set where
  constructor localGlobalDiagnosticsReceipt
  field
    localNonsingularityChecked : Bool
    displayedThreePointFibreChecked : Bool
    globalNoninjectivityChecked : Bool
    propernessInferredFromLocalJacobian : Bool
    propernessInferredFromLocalJacobianIsFalse :
      propernessInferredFromLocalJacobian ≡ false
    monodromyInferredFromLocalJacobian : Bool
    monodromyInferredFromLocalJacobianIsFalse :
      monodromyInferredFromLocalJacobian ≡ false
    genericFibreDegreeInferredFromOneFibre : Bool
    genericFibreDegreeInferredFromOneFibreIsFalse :
      genericFibreDegreeInferredFromOneFibre ≡ false
    interpretation : String

localGlobalDiagnosticsReceipt : LocalGlobalDiagnosticsReceipt
localGlobalDiagnosticsReceipt =
  localGlobalDiagnosticsReceipt
    true true true
    false refl
    false refl
    false refl
    "everywhere local nonsingularity and one exact three-point fibre are checked; properness, generic degree, monodromy and boundary escape remain separately evidenced global properties"
