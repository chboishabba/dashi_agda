module DASHI.Geometry.DifferentialGeometryParity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

------------------------------------------------------------------------
-- Differential-geometry parity layer.
--
-- This module records the checked DASHI-side parity surface for the
-- PhysLean differential-geometry vocabulary.  It names the interfaces and
-- standard identity obligations that downstream work must discharge, but it
-- deliberately does not assert imported theorem authority.  The canonical
-- receipt is fail-closed: every theorem/promotion flag is explicit and false
-- unless a constructorless authority token is supplied from outside.

data DifferentialGeometryParityStatus : Set where
  differentialGeometryTargetsOnlyNoPromotion :
    DifferentialGeometryParityStatus

data DifferentialGeometryConcept : Set where
  manifoldConcept :
    DifferentialGeometryConcept

  smoothMapConcept :
    DifferentialGeometryConcept

  tangentBundleConcept :
    DifferentialGeometryConcept

  cotangentBundleConcept :
    DifferentialGeometryConcept

  differentialFormConcept :
    DifferentialGeometryConcept

  vectorFieldConcept :
    DifferentialGeometryConcept

  metricConcept :
    DifferentialGeometryConcept

  connectionConcept :
    DifferentialGeometryConcept

  curvatureConcept :
    DifferentialGeometryConcept

data DifferentialGeometryIdentityTarget : Set where
  exteriorDerivativeSquaresToZeroTarget :
    DifferentialGeometryIdentityTarget

  cartanFormulaTarget :
    DifferentialGeometryIdentityTarget

  stokesTheoremTarget :
    DifferentialGeometryIdentityTarget

  poincareLemmaTarget :
    DifferentialGeometryIdentityTarget

  bianchiIdentityTarget :
    DifferentialGeometryIdentityTarget

data DifferentialGeometryOpenObligation : Set where
  missingManifoldAdapter :
    DifferentialGeometryOpenObligation

  missingSmoothMapAdapter :
    DifferentialGeometryOpenObligation

  missingTangentBundleAdapter :
    DifferentialGeometryOpenObligation

  missingCotangentBundleAdapter :
    DifferentialGeometryOpenObligation

  missingDifferentialFormAdapter :
    DifferentialGeometryOpenObligation

  missingVectorFieldAdapter :
    DifferentialGeometryOpenObligation

  missingMetricAdapter :
    DifferentialGeometryOpenObligation

  missingConnectionAdapter :
    DifferentialGeometryOpenObligation

  missingCurvatureAdapter :
    DifferentialGeometryOpenObligation

  missingExteriorDerivativeSquaresToZeroProof :
    DifferentialGeometryOpenObligation

  missingCartanFormulaProof :
    DifferentialGeometryOpenObligation

  missingStokesTheoremProof :
    DifferentialGeometryOpenObligation

  missingPoincareLemmaProof :
    DifferentialGeometryOpenObligation

  missingBianchiIdentityProof :
    DifferentialGeometryOpenObligation

  missingPhysLeanParityAuthority :
    DifferentialGeometryOpenObligation

canonicalDifferentialGeometryConcepts :
  List DifferentialGeometryConcept
canonicalDifferentialGeometryConcepts =
  manifoldConcept
  ∷ smoothMapConcept
  ∷ tangentBundleConcept
  ∷ cotangentBundleConcept
  ∷ differentialFormConcept
  ∷ vectorFieldConcept
  ∷ metricConcept
  ∷ connectionConcept
  ∷ curvatureConcept
  ∷ []

canonicalDifferentialGeometryIdentityTargets :
  List DifferentialGeometryIdentityTarget
canonicalDifferentialGeometryIdentityTargets =
  exteriorDerivativeSquaresToZeroTarget
  ∷ cartanFormulaTarget
  ∷ stokesTheoremTarget
  ∷ poincareLemmaTarget
  ∷ bianchiIdentityTarget
  ∷ []

canonicalDifferentialGeometryOpenObligations :
  List DifferentialGeometryOpenObligation
canonicalDifferentialGeometryOpenObligations =
  missingManifoldAdapter
  ∷ missingSmoothMapAdapter
  ∷ missingTangentBundleAdapter
  ∷ missingCotangentBundleAdapter
  ∷ missingDifferentialFormAdapter
  ∷ missingVectorFieldAdapter
  ∷ missingMetricAdapter
  ∷ missingConnectionAdapter
  ∷ missingCurvatureAdapter
  ∷ missingExteriorDerivativeSquaresToZeroProof
  ∷ missingCartanFormulaProof
  ∷ missingStokesTheoremProof
  ∷ missingPoincareLemmaProof
  ∷ missingBianchiIdentityProof
  ∷ missingPhysLeanParityAuthority
  ∷ []

-- Constructorless: this module cannot manufacture parity promotion authority.
data DifferentialGeometryParityAuthorityToken : Set where

record CoreDifferentialGeometryInterfaceSurface : Setω where
  field
    Manifold :
      Set

    SmoothMap :
      Manifold →
      Manifold →
      Set

    TangentBundle :
      Manifold →
      Set

    CotangentBundle :
      Manifold →
      Set

    DifferentialForm :
      Manifold →
      Set

    VectorField :
      Manifold →
      Set

    Metric :
      Manifold →
      Set

    Connection :
      (M : Manifold) →
      TangentBundle M →
      Set

    Curvature :
      (M : Manifold) →
      (TM : TangentBundle M) →
      Connection M TM →
      Set

    interfaceTargetName :
      String

    interfaceTargetName-v :
      interfaceTargetName
      ≡
      "target-only-PhysLean-differential-geometry-core-interface"

    interfacesNamed :
      Bool

    interfacesNamedIsTrue :
      interfacesNamed ≡ true

    concreteAdaptersImported :
      Bool

    concreteAdaptersImportedIsFalse :
      concreteAdaptersImported ≡ false

open CoreDifferentialGeometryInterfaceSurface public

record ManifoldIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    Point :
      Manifold core →
      Set

    dimension :
      Manifold core →
      Nat

    LocalChart :
      (M : Manifold core) →
      Point M →
      Set

    chartInverse :
      (M : Manifold core) →
      (point : Point M) →
      LocalChart M point →
      Set

    chart :
      (M : Manifold core) →
      Point M →
      Set

    chartInv :
      (M : Manifold core) →
      (point : Point M) →
      chart M point →
      Point M

    roundtrip :
      (M : Manifold core) →
      (point : Point M) →
      (coordinate : chart M point) →
      chartInv M point coordinate ≡ point

    roundtripShape :
      String

    roundtripShape-v :
      roundtripShape
      ≡
      "roundtrip: chartInv M p (chart-coordinate-at p) = p; chart/chartInv are checked target fields only"

    manifoldIntakeTargetName :
      String

    manifoldIntakeTargetName-v :
      manifoldIntakeTargetName
      ≡
      "intake-Manifold-Point-dimension-chart-chartInv-roundtrip"

    manifoldShapeChecked :
      Bool

    manifoldShapeCheckedIsTrue :
      manifoldShapeChecked ≡ true

    manifoldAdapterImported :
      Bool

    manifoldAdapterImportedIsFalse :
      manifoldAdapterImported ≡ false

open ManifoldIntakeSurface public

record SmoothMapIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    identitySmoothMap :
      (M : Manifold core) →
      SmoothMap core M M

    smoothId :
      (M : Manifold core) →
      SmoothMap core M M

    composeSmoothMap :
      {M N P : Manifold core} →
      SmoothMap core N P →
      SmoothMap core M N →
      SmoothMap core M P

    smoothComp :
      {M N P : Manifold core} →
      SmoothMap core N P →
      SmoothMap core M N →
      SmoothMap core M P

    smoothMapIntakeTargetName :
      String

    smoothMapIntakeTargetName-v :
      smoothMapIntakeTargetName
      ≡
      "intake-SmoothMap-smoothId-smoothComp"

    smoothMapShapeChecked :
      Bool

    smoothMapShapeCheckedIsTrue :
      smoothMapShapeChecked ≡ true

    smoothMapLawsProved :
      Bool

    smoothMapLawsProvedIsFalse :
      smoothMapLawsProved ≡ false

open SmoothMapIntakeSurface public

record BundleFiberIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    (manifoldIntake : ManifoldIntakeSurface core)
    : Setω where
  field
    TangentFiber :
      (M : Manifold core) →
      TangentBundle core M →
      Point manifoldIntake M →
      Set

    CotangentFiber :
      (M : Manifold core) →
      CotangentBundle core M →
      Point manifoldIntake M →
      Set

    bundleFiberIntakeTargetName :
      String

    bundleFiberIntakeTargetName-v :
      bundleFiberIntakeTargetName
      ≡
      "intake-TangentBundle-CotangentBundle-fibers"

    bundleFiberShapeChecked :
      Bool

    bundleFiberShapeCheckedIsTrue :
      bundleFiberShapeChecked ≡ true

    bundleFiberAdaptersImported :
      Bool

    bundleFiberAdaptersImportedIsFalse :
      bundleFiberAdaptersImported ≡ false

open BundleFiberIntakeSurface public

record MetricAuthorityIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    metricSymmetryAuthority :
      (M : Manifold core) →
      Metric core M →
      Set

    metricNondegenerateAuthority :
      (M : Manifold core) →
      Metric core M →
      Set

    metricSmoothAuthority :
      (M : Manifold core) →
      Metric core M →
      Set

    metricAuthorityTargetName :
      String

    metricAuthorityTargetName-v :
      metricAuthorityTargetName
      ≡
      "authority-target-Metric-symmetry-nondegenerate-smooth"

    metricAuthorityFieldsNamed :
      Bool

    metricAuthorityFieldsNamedIsTrue :
      metricAuthorityFieldsNamed ≡ true

    metricAuthorityImported :
      Bool

    metricAuthorityImportedIsFalse :
      metricAuthorityImported ≡ false

open MetricAuthorityIntakeSurface public

record ConnectionAuthorityIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    ChristoffelSymbolAuthority :
      (M : Manifold core) →
      (TM : TangentBundle core M) →
      Connection core M TM →
      Set

    connectionTransformAuthority :
      (M : Manifold core) →
      (TM : TangentBundle core M) →
      Connection core M TM →
      Set

    connectionChartTransformAuthority :
      (M : Manifold core) →
      (TM : TangentBundle core M) →
      Connection core M TM →
      Set

    christoffelChartTransformFormula :
      String

    christoffelChartTransformFormula-v :
      christoffelChartTransformFormula
      ≡
      "Gamma'^k_ij = (dy^k/dx^r)(dx^p/dy^i)(dx^q/dy^j) Gamma^r_pq + (dy^k/dx^r)(d^2 x^r / dy^i dy^j)"

    connectionAuthorityTargetName :
      String

    connectionAuthorityTargetName-v :
      connectionAuthorityTargetName
      ≡
      "authority-target-Connection-Christoffel-connectionChartTransformAuthority"

    connectionAuthorityFieldsNamed :
      Bool

    connectionAuthorityFieldsNamedIsTrue :
      connectionAuthorityFieldsNamed ≡ true

    connectionAuthorityImported :
      Bool

    connectionAuthorityImportedIsFalse :
      connectionAuthorityImported ≡ false

open ConnectionAuthorityIntakeSurface public

record CurvatureAuthorityIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    curvatureRXYZAuthority :
      (M : Manifold core) →
      (TM : TangentBundle core M) →
      (connection : Connection core M TM) →
      Curvature core M TM connection →
      VectorField core M →
      VectorField core M →
      VectorField core M →
      Set

    curvatureAuthorityTargetName :
      String

    curvatureAuthorityTargetName-v :
      curvatureAuthorityTargetName
      ≡
      "authority-target-Curvature-R-X-Y-Z"

    curvatureAuthorityFieldNamed :
      Bool

    curvatureAuthorityFieldNamedIsTrue :
      curvatureAuthorityFieldNamed ≡ true

    curvatureAuthorityImported :
      Bool

    curvatureAuthorityImportedIsFalse :
      curvatureAuthorityImported ≡ false

open CurvatureAuthorityIntakeSurface public

record DifferentialFormCalculusSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    ExteriorDerivative :
      (M : Manifold core) →
      DifferentialForm core M →
      DifferentialForm core M

    InteriorProduct :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    LieDerivative :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    Boundary :
      Manifold core →
      Set

    DeRhamCohomologyClass :
      Manifold core →
      Set

    calculusTargetName :
      String

    calculusTargetName-v :
      calculusTargetName
      ≡
      "target-only-exterior-calculus-d-iX-LX-boundary-deRham"

    calculusAdaptersImported :
      Bool

    calculusAdaptersImportedIsFalse :
      calculusAdaptersImported ≡ false

open DifferentialFormCalculusSurface public

record ExteriorCalculusOperationIntakeSurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    WedgeProduct :
      (M : Manifold core) →
      DifferentialForm core M →
      DifferentialForm core M →
      DifferentialForm core M

    exteriorDerivativeOperation :
      (M : Manifold core) →
      DifferentialForm core M →
      DifferentialForm core M

    interiorProductOperation :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    lieDerivativeOperation :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      DifferentialForm core M

    pullbackFormOperation :
      {M N : Manifold core} →
      SmoothMap core M N →
      DifferentialForm core N →
      DifferentialForm core M

    exteriorCalculusOperationTargetName :
      String

    exteriorCalculusOperationTargetName-v :
      exteriorCalculusOperationTargetName
      ≡
      "intake-exterior-calculus-d-wedge-interior-Lie-pullback"

    exteriorCalculusOperationsNamed :
      Bool

    exteriorCalculusOperationsNamedIsTrue :
      exteriorCalculusOperationsNamed ≡ true

    exteriorCalculusOperationLawsProved :
      Bool

    exteriorCalculusOperationLawsProvedIsFalse :
      exteriorCalculusOperationLawsProved ≡ false

open ExteriorCalculusOperationIntakeSurface public

record ExteriorDerivativeSquaresToZeroTheoremShape
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    dSquaredTarget :
      (M : Manifold core) →
      DifferentialForm core M →
      Set

    dSquaredTargetName :
      String

    dSquaredTargetName-v :
      dSquaredTargetName
      ≡
      "theorem-shape-exterior-derivative-squares-to-zero"

    dSquaredFormula :
      String

    dSquaredFormula-v :
      dSquaredFormula
      ≡
      "d (d omega) = 0"

    schwarzSymmetryContent :
      String

    schwarzSymmetryContent-v :
      schwarzSymmetryContent
      ≡
      "Schwarz content: mixed second partials commute, partial_i partial_j omega_I = partial_j partial_i omega_I"

    antisymmetryCancellationContent :
      String

    antisymmetryCancellationContent-v :
      antisymmetryCancellationContent
      ≡
      "antisymmetry content: symmetric second-partial coefficients are paired with antisymmetric wedge slots, so the paired terms cancel"

    dSquaredShapeNamed :
      Bool

    dSquaredShapeNamedIsTrue :
      dSquaredShapeNamed ≡ true

    dSquaredProved :
      Bool

    dSquaredProvedIsFalse :
      dSquaredProved ≡ false

open ExteriorDerivativeSquaresToZeroTheoremShape public

record CartanFormulaTheoremShape
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    cartanFormulaTheoremTarget :
      (M : Manifold core) →
      VectorField core M →
      DifferentialForm core M →
      Set

    cartanFormulaTargetName :
      String

    cartanFormulaTargetName-v :
      cartanFormulaTargetName
      ≡
      "theorem-shape-Cartan-LX-equals-d-iX-plus-iX-d"

    cartanFormulaStatement :
      String

    cartanFormulaStatement-v :
      cartanFormulaStatement
      ≡
      "L_X omega = d (i_X omega) + i_X (d omega)"

    cartanDerivationAgreementStructure :
      String

    cartanDerivationAgreementStructure-v :
      cartanDerivationAgreementStructure
      ≡
      "derivation-agrees-on-generators: check functions and one-forms, then extend by graded derivation and wedge compatibility"

    cartanAgreesOnGenerators :
      Bool

    cartanAgreesOnGeneratorsIsTrue :
      cartanAgreesOnGenerators ≡ true

    cartanShapeNamed :
      Bool

    cartanShapeNamedIsTrue :
      cartanShapeNamed ≡ true

    cartanFormulaAuthorityImported :
      Bool

    cartanFormulaAuthorityImportedIsFalse :
      cartanFormulaAuthorityImported ≡ false

open CartanFormulaTheoremShape public

record StokesTheoremWithOrientationShape
    (core : CoreDifferentialGeometryInterfaceSurface)
    (manifoldIntake : ManifoldIntakeSurface core)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    Orientation :
      Manifold core →
      Set

    stokesWithOrientationTarget :
      (M : Manifold core) →
      Orientation M →
      Boundary calculus M →
      DifferentialForm core M →
      Set

    stokesWithOrientationTargetName :
      String

    stokesWithOrientationTargetName-v :
      stokesWithOrientationTargetName
      ≡
      "theorem-shape-Stokes-with-orientation"

    orientationConvention :
      String

    orientationConvention-v :
      orientationConvention
      ≡
      "boundary orientation is outward-normal-first: (normal, boundary frame) gives the ambient orientation"

    stokesStatement :
      String

    stokesStatement-v :
      stokesStatement
      ≡
      "integral_M d omega = integral_boundary(M) omega, with the induced boundary orientation"

    stokesAuthorityName :
      String

    stokesAuthorityName-v :
      stokesAuthorityName
      ≡
      "StokesTheoremWithOrientation"

    stokesAuthoritySlot :
      Bool

    stokesAuthoritySlotIsFalse :
      stokesAuthoritySlot ≡ false

    stokesOrientationShapeNamed :
      Bool

    stokesOrientationShapeNamedIsTrue :
      stokesOrientationShapeNamed ≡ true

    stokesWithOrientationProved :
      Bool

    stokesWithOrientationProvedIsFalse :
      stokesWithOrientationProved ≡ false

open StokesTheoremWithOrientationShape public

record PoincareHomotopyOperatorShape
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    HomotopyOperator :
      (M : Manifold core) →
      DifferentialForm core M →
      DifferentialForm core M

    poincareHomotopyTarget :
      (M : Manifold core) →
      DifferentialForm core M →
      Set

    poincareHomotopyTargetName :
      String

    poincareHomotopyTargetName-v :
      poincareHomotopyTargetName
      ≡
      "theorem-shape-Poincare-homotopy-operator"

    homotopyOperatorKFormula :
      String

    homotopyOperatorKFormula-v :
      homotopyOperatorKFormula
      ≡
      "K omega at x = integral_0^1 t^(k-1) i_R omega(t x) dt for k-forms on a star-shaped domain"

    radialVectorFieldFormula :
      String

    radialVectorFieldFormula-v :
      radialVectorFieldFormula
      ≡
      "R_x = sum_i x^i partial_i"

    poincareHomotopyIdentity :
      String

    poincareHomotopyIdentity-v :
      poincareHomotopyIdentity
      ≡
      "d K + K d = id on positive-degree closed forms; constants are the degree-zero kernel"

    poincareHomotopyShapeNamed :
      Bool

    poincareHomotopyShapeNamedIsTrue :
      poincareHomotopyShapeNamed ≡ true

    poincareHomotopyProved :
      Bool

    poincareHomotopyProvedIsFalse :
      poincareHomotopyProved ≡ false

open PoincareHomotopyOperatorShape public

record BianchiIdentityTheoremShape
    (core : CoreDifferentialGeometryInterfaceSurface)
    : Setω where
  field
    bianchiIdentityTheoremTarget :
      (M : Manifold core) →
      (TM : TangentBundle core M) →
      (connection : Connection core M TM) →
      Curvature core M TM connection →
      Set

    bianchiIdentityTargetName :
      String

    bianchiIdentityTargetName-v :
      bianchiIdentityTargetName
      ≡
      "theorem-shape-Bianchi-identity"

    secondBianchiCyclicExpansion :
      String

    secondBianchiCyclicExpansion-v :
      secondBianchiCyclicExpansion
      ≡
      "(nabla_X R)(Y,Z) + (nabla_Y R)(Z,X) + (nabla_Z R)(X,Y) = 0"

    bianchiTorsionFreeDependency :
      String

    bianchiTorsionFreeDependency-v :
      bianchiTorsionFreeDependency
      ≡
      "torsion-free dependency: [X,Y] = nabla_X Y - nabla_Y X is used in the cyclic expansion"

    bianchiJacobiDependency :
      String

    bianchiJacobiDependency-v :
      bianchiJacobiDependency
      ≡
      "Jacobi dependency: cyclic cancellation uses [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0"

    bianchiShapeNamed :
      Bool

    bianchiShapeNamedIsTrue :
      bianchiShapeNamed ≡ true

    bianchiAuthorityImported :
      Bool

    bianchiAuthorityImportedIsFalse :
      bianchiAuthorityImported ≡ false

open BianchiIdentityTheoremShape public

record DifferentialGeometryIdentitySurface
    (core : CoreDifferentialGeometryInterfaceSurface)
    (calculus : DifferentialFormCalculusSurface core)
    : Setω where
  field
    exteriorDerivativeSquaresToZeroNamed :
      Bool

    exteriorDerivativeSquaresToZeroNamedIsTrue :
      exteriorDerivativeSquaresToZeroNamed ≡ true

    exteriorDerivativeSquaresToZeroProved :
      Bool

    exteriorDerivativeSquaresToZeroProvedIsFalse :
      exteriorDerivativeSquaresToZeroProved ≡ false

    cartanFormulaNamed :
      Bool

    cartanFormulaNamedIsTrue :
      cartanFormulaNamed ≡ true

    cartanFormulaProved :
      Bool

    cartanFormulaProvedIsFalse :
      cartanFormulaProved ≡ false

    stokesTheoremNamed :
      Bool

    stokesTheoremNamedIsTrue :
      stokesTheoremNamed ≡ true

    stokesTheoremProved :
      Bool

    stokesTheoremProvedIsFalse :
      stokesTheoremProved ≡ false

    poincareLemmaNamed :
      Bool

    poincareLemmaNamedIsTrue :
      poincareLemmaNamed ≡ true

    poincareLemmaProved :
      Bool

    poincareLemmaProvedIsFalse :
      poincareLemmaProved ≡ false

    bianchiIdentityNamed :
      Bool

    bianchiIdentityNamedIsTrue :
      bianchiIdentityNamed ≡ true

    bianchiIdentityProved :
      Bool

    bianchiIdentityProvedIsFalse :
      bianchiIdentityProved ≡ false

    identityTargetNames :
      List DifferentialGeometryIdentityTarget

    identityTargetNamesAreCanonical :
      identityTargetNames
      ≡
      canonicalDifferentialGeometryIdentityTargets

open DifferentialGeometryIdentitySurface public

record DifferentialGeometryParityReceipt : Setω where
  field
    status :
      DifferentialGeometryParityStatus

    coreInterface :
      CoreDifferentialGeometryInterfaceSurface

    manifoldIntake :
      ManifoldIntakeSurface coreInterface

    smoothMapIntake :
      SmoothMapIntakeSurface coreInterface

    bundleFiberIntake :
      BundleFiberIntakeSurface coreInterface manifoldIntake

    metricAuthorityIntake :
      MetricAuthorityIntakeSurface coreInterface

    connectionAuthorityIntake :
      ConnectionAuthorityIntakeSurface coreInterface

    curvatureAuthorityIntake :
      CurvatureAuthorityIntakeSurface coreInterface

    formCalculus :
      DifferentialFormCalculusSurface coreInterface

    exteriorCalculusOperationIntake :
      ExteriorCalculusOperationIntakeSurface coreInterface formCalculus

    dSquaredTheoremShape :
      ExteriorDerivativeSquaresToZeroTheoremShape coreInterface formCalculus

    cartanTheoremShape :
      CartanFormulaTheoremShape coreInterface formCalculus

    stokesWithOrientationShape :
      StokesTheoremWithOrientationShape
        coreInterface
        manifoldIntake
        formCalculus

    poincareHomotopyShape :
      PoincareHomotopyOperatorShape coreInterface formCalculus

    bianchiTheoremShape :
      BianchiIdentityTheoremShape coreInterface

    identitySurface :
      DifferentialGeometryIdentitySurface coreInterface formCalculus

    coveredConcepts :
      List DifferentialGeometryConcept

    coveredConceptsAreCanonical :
      coveredConcepts
      ≡
      canonicalDifferentialGeometryConcepts

    openObligations :
      List DifferentialGeometryOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalDifferentialGeometryOpenObligations

    physLeanParityLayerNamed :
      Bool

    physLeanParityLayerNamedIsTrue :
      physLeanParityLayerNamed ≡ true

    physLeanAdaptersImported :
      Bool

    physLeanAdaptersImportedIsFalse :
      physLeanAdaptersImported ≡ false

    identityProofsImported :
      Bool

    identityProofsImportedIsFalse :
      identityProofsImported ≡ false

    parityPromoted :
      Bool

    parityPromotedIsFalse :
      parityPromoted ≡ false

    noPromotionWithoutAuthority :
      DifferentialGeometryParityAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DifferentialGeometryParityReceipt public

canonicalCoreDifferentialGeometryInterfaceSurface :
  CoreDifferentialGeometryInterfaceSurface
canonicalCoreDifferentialGeometryInterfaceSurface =
  record
    { Manifold =
        ⊥
    ; SmoothMap =
        λ ()
    ; TangentBundle =
        λ ()
    ; CotangentBundle =
        λ ()
    ; DifferentialForm =
        λ ()
    ; VectorField =
        λ ()
    ; Metric =
        λ ()
    ; Connection =
        λ ()
    ; Curvature =
        λ ()
    ; interfaceTargetName =
        "target-only-PhysLean-differential-geometry-core-interface"
    ; interfaceTargetName-v =
        refl
    ; interfacesNamed =
        true
    ; interfacesNamedIsTrue =
        refl
    ; concreteAdaptersImported =
        false
    ; concreteAdaptersImportedIsFalse =
        refl
    }

canonicalManifoldIntakeSurface :
  ManifoldIntakeSurface canonicalCoreDifferentialGeometryInterfaceSurface
canonicalManifoldIntakeSurface =
  record
    { Point =
        λ ()
    ; dimension =
        λ ()
    ; LocalChart =
        λ ()
    ; chartInverse =
        λ ()
    ; chart =
        λ ()
    ; chartInv =
        λ ()
    ; roundtrip =
        λ ()
    ; roundtripShape =
        "roundtrip: chartInv M p (chart-coordinate-at p) = p; chart/chartInv are checked target fields only"
    ; roundtripShape-v =
        refl
    ; manifoldIntakeTargetName =
        "intake-Manifold-Point-dimension-chart-chartInv-roundtrip"
    ; manifoldIntakeTargetName-v =
        refl
    ; manifoldShapeChecked =
        true
    ; manifoldShapeCheckedIsTrue =
        refl
    ; manifoldAdapterImported =
        false
    ; manifoldAdapterImportedIsFalse =
        refl
    }

canonicalSmoothMapIntakeSurface :
  SmoothMapIntakeSurface canonicalCoreDifferentialGeometryInterfaceSurface
canonicalSmoothMapIntakeSurface =
  record
    { identitySmoothMap =
        λ ()
    ; smoothId =
        λ ()
    ; composeSmoothMap =
        λ { {M = ()} }
    ; smoothComp =
        λ { {M = ()} }
    ; smoothMapIntakeTargetName =
        "intake-SmoothMap-smoothId-smoothComp"
    ; smoothMapIntakeTargetName-v =
        refl
    ; smoothMapShapeChecked =
        true
    ; smoothMapShapeCheckedIsTrue =
        refl
    ; smoothMapLawsProved =
        false
    ; smoothMapLawsProvedIsFalse =
        refl
    }

canonicalBundleFiberIntakeSurface :
  BundleFiberIntakeSurface
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalManifoldIntakeSurface
canonicalBundleFiberIntakeSurface =
  record
    { TangentFiber =
        λ ()
    ; CotangentFiber =
        λ ()
    ; bundleFiberIntakeTargetName =
        "intake-TangentBundle-CotangentBundle-fibers"
    ; bundleFiberIntakeTargetName-v =
        refl
    ; bundleFiberShapeChecked =
        true
    ; bundleFiberShapeCheckedIsTrue =
        refl
    ; bundleFiberAdaptersImported =
        false
    ; bundleFiberAdaptersImportedIsFalse =
        refl
    }

canonicalMetricAuthorityIntakeSurface :
  MetricAuthorityIntakeSurface canonicalCoreDifferentialGeometryInterfaceSurface
canonicalMetricAuthorityIntakeSurface =
  record
    { metricSymmetryAuthority =
        λ ()
    ; metricNondegenerateAuthority =
        λ ()
    ; metricSmoothAuthority =
        λ ()
    ; metricAuthorityTargetName =
        "authority-target-Metric-symmetry-nondegenerate-smooth"
    ; metricAuthorityTargetName-v =
        refl
    ; metricAuthorityFieldsNamed =
        true
    ; metricAuthorityFieldsNamedIsTrue =
        refl
    ; metricAuthorityImported =
        false
    ; metricAuthorityImportedIsFalse =
        refl
    }

canonicalConnectionAuthorityIntakeSurface :
  ConnectionAuthorityIntakeSurface canonicalCoreDifferentialGeometryInterfaceSurface
canonicalConnectionAuthorityIntakeSurface =
  record
    { ChristoffelSymbolAuthority =
        λ ()
    ; connectionTransformAuthority =
        λ ()
    ; connectionChartTransformAuthority =
        λ ()
    ; christoffelChartTransformFormula =
        "Gamma'^k_ij = (dy^k/dx^r)(dx^p/dy^i)(dx^q/dy^j) Gamma^r_pq + (dy^k/dx^r)(d^2 x^r / dy^i dy^j)"
    ; christoffelChartTransformFormula-v =
        refl
    ; connectionAuthorityTargetName =
        "authority-target-Connection-Christoffel-connectionChartTransformAuthority"
    ; connectionAuthorityTargetName-v =
        refl
    ; connectionAuthorityFieldsNamed =
        true
    ; connectionAuthorityFieldsNamedIsTrue =
        refl
    ; connectionAuthorityImported =
        false
    ; connectionAuthorityImportedIsFalse =
        refl
    }

canonicalCurvatureAuthorityIntakeSurface :
  CurvatureAuthorityIntakeSurface canonicalCoreDifferentialGeometryInterfaceSurface
canonicalCurvatureAuthorityIntakeSurface =
  record
    { curvatureRXYZAuthority =
        λ ()
    ; curvatureAuthorityTargetName =
        "authority-target-Curvature-R-X-Y-Z"
    ; curvatureAuthorityTargetName-v =
        refl
    ; curvatureAuthorityFieldNamed =
        true
    ; curvatureAuthorityFieldNamedIsTrue =
        refl
    ; curvatureAuthorityImported =
        false
    ; curvatureAuthorityImportedIsFalse =
        refl
    }

canonicalDifferentialFormCalculusSurface :
  DifferentialFormCalculusSurface
    canonicalCoreDifferentialGeometryInterfaceSurface
canonicalDifferentialFormCalculusSurface =
  record
    { ExteriorDerivative =
        λ ()
    ; InteriorProduct =
        λ ()
    ; LieDerivative =
        λ ()
    ; Boundary =
        λ ()
    ; DeRhamCohomologyClass =
        λ ()
    ; calculusTargetName =
        "target-only-exterior-calculus-d-iX-LX-boundary-deRham"
    ; calculusTargetName-v =
        refl
    ; calculusAdaptersImported =
        false
    ; calculusAdaptersImportedIsFalse =
        refl
    }

canonicalExteriorCalculusOperationIntakeSurface :
  ExteriorCalculusOperationIntakeSurface
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalExteriorCalculusOperationIntakeSurface =
  record
    { WedgeProduct =
        λ ()
    ; exteriorDerivativeOperation =
        λ ()
    ; interiorProductOperation =
        λ ()
    ; lieDerivativeOperation =
        λ ()
    ; pullbackFormOperation =
        λ { {M = ()} }
    ; exteriorCalculusOperationTargetName =
        "intake-exterior-calculus-d-wedge-interior-Lie-pullback"
    ; exteriorCalculusOperationTargetName-v =
        refl
    ; exteriorCalculusOperationsNamed =
        true
    ; exteriorCalculusOperationsNamedIsTrue =
        refl
    ; exteriorCalculusOperationLawsProved =
        false
    ; exteriorCalculusOperationLawsProvedIsFalse =
        refl
    }

canonicalExteriorDerivativeSquaresToZeroTheoremShape :
  ExteriorDerivativeSquaresToZeroTheoremShape
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalExteriorDerivativeSquaresToZeroTheoremShape =
  record
    { dSquaredTarget =
        λ ()
    ; dSquaredTargetName =
        "theorem-shape-exterior-derivative-squares-to-zero"
    ; dSquaredTargetName-v =
        refl
    ; dSquaredFormula =
        "d (d omega) = 0"
    ; dSquaredFormula-v =
        refl
    ; schwarzSymmetryContent =
        "Schwarz content: mixed second partials commute, partial_i partial_j omega_I = partial_j partial_i omega_I"
    ; schwarzSymmetryContent-v =
        refl
    ; antisymmetryCancellationContent =
        "antisymmetry content: symmetric second-partial coefficients are paired with antisymmetric wedge slots, so the paired terms cancel"
    ; antisymmetryCancellationContent-v =
        refl
    ; dSquaredShapeNamed =
        true
    ; dSquaredShapeNamedIsTrue =
        refl
    ; dSquaredProved =
        false
    ; dSquaredProvedIsFalse =
        refl
    }

canonicalCartanFormulaTheoremShape :
  CartanFormulaTheoremShape
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalCartanFormulaTheoremShape =
  record
    { cartanFormulaTheoremTarget =
        λ ()
    ; cartanFormulaTargetName =
        "theorem-shape-Cartan-LX-equals-d-iX-plus-iX-d"
    ; cartanFormulaTargetName-v =
        refl
    ; cartanFormulaStatement =
        "L_X omega = d (i_X omega) + i_X (d omega)"
    ; cartanFormulaStatement-v =
        refl
    ; cartanDerivationAgreementStructure =
        "derivation-agrees-on-generators: check functions and one-forms, then extend by graded derivation and wedge compatibility"
    ; cartanDerivationAgreementStructure-v =
        refl
    ; cartanAgreesOnGenerators =
        true
    ; cartanAgreesOnGeneratorsIsTrue =
        refl
    ; cartanShapeNamed =
        true
    ; cartanShapeNamedIsTrue =
        refl
    ; cartanFormulaAuthorityImported =
        false
    ; cartanFormulaAuthorityImportedIsFalse =
        refl
    }

canonicalStokesTheoremWithOrientationShape :
  StokesTheoremWithOrientationShape
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalManifoldIntakeSurface
    canonicalDifferentialFormCalculusSurface
canonicalStokesTheoremWithOrientationShape =
  record
    { Orientation =
        λ ()
    ; stokesWithOrientationTarget =
        λ ()
    ; stokesWithOrientationTargetName =
        "theorem-shape-Stokes-with-orientation"
    ; stokesWithOrientationTargetName-v =
        refl
    ; orientationConvention =
        "boundary orientation is outward-normal-first: (normal, boundary frame) gives the ambient orientation"
    ; orientationConvention-v =
        refl
    ; stokesStatement =
        "integral_M d omega = integral_boundary(M) omega, with the induced boundary orientation"
    ; stokesStatement-v =
        refl
    ; stokesAuthorityName =
        "StokesTheoremWithOrientation"
    ; stokesAuthorityName-v =
        refl
    ; stokesAuthoritySlot =
        false
    ; stokesAuthoritySlotIsFalse =
        refl
    ; stokesOrientationShapeNamed =
        true
    ; stokesOrientationShapeNamedIsTrue =
        refl
    ; stokesWithOrientationProved =
        false
    ; stokesWithOrientationProvedIsFalse =
        refl
    }

canonicalPoincareHomotopyOperatorShape :
  PoincareHomotopyOperatorShape
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalPoincareHomotopyOperatorShape =
  record
    { HomotopyOperator =
        λ ()
    ; poincareHomotopyTarget =
        λ ()
    ; poincareHomotopyTargetName =
        "theorem-shape-Poincare-homotopy-operator"
    ; poincareHomotopyTargetName-v =
        refl
    ; homotopyOperatorKFormula =
        "K omega at x = integral_0^1 t^(k-1) i_R omega(t x) dt for k-forms on a star-shaped domain"
    ; homotopyOperatorKFormula-v =
        refl
    ; radialVectorFieldFormula =
        "R_x = sum_i x^i partial_i"
    ; radialVectorFieldFormula-v =
        refl
    ; poincareHomotopyIdentity =
        "d K + K d = id on positive-degree closed forms; constants are the degree-zero kernel"
    ; poincareHomotopyIdentity-v =
        refl
    ; poincareHomotopyShapeNamed =
        true
    ; poincareHomotopyShapeNamedIsTrue =
        refl
    ; poincareHomotopyProved =
        false
    ; poincareHomotopyProvedIsFalse =
        refl
    }

canonicalBianchiIdentityTheoremShape :
  BianchiIdentityTheoremShape canonicalCoreDifferentialGeometryInterfaceSurface
canonicalBianchiIdentityTheoremShape =
  record
    { bianchiIdentityTheoremTarget =
        λ ()
    ; bianchiIdentityTargetName =
        "theorem-shape-Bianchi-identity"
    ; bianchiIdentityTargetName-v =
        refl
    ; secondBianchiCyclicExpansion =
        "(nabla_X R)(Y,Z) + (nabla_Y R)(Z,X) + (nabla_Z R)(X,Y) = 0"
    ; secondBianchiCyclicExpansion-v =
        refl
    ; bianchiTorsionFreeDependency =
        "torsion-free dependency: [X,Y] = nabla_X Y - nabla_Y X is used in the cyclic expansion"
    ; bianchiTorsionFreeDependency-v =
        refl
    ; bianchiJacobiDependency =
        "Jacobi dependency: cyclic cancellation uses [X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0"
    ; bianchiJacobiDependency-v =
        refl
    ; bianchiShapeNamed =
        true
    ; bianchiShapeNamedIsTrue =
        refl
    ; bianchiAuthorityImported =
        false
    ; bianchiAuthorityImportedIsFalse =
        refl
    }

canonicalDifferentialGeometryIdentitySurface :
  DifferentialGeometryIdentitySurface
    canonicalCoreDifferentialGeometryInterfaceSurface
    canonicalDifferentialFormCalculusSurface
canonicalDifferentialGeometryIdentitySurface =
  record
    { exteriorDerivativeSquaresToZeroNamed =
        true
    ; exteriorDerivativeSquaresToZeroNamedIsTrue =
        refl
    ; exteriorDerivativeSquaresToZeroProved =
        false
    ; exteriorDerivativeSquaresToZeroProvedIsFalse =
        refl
    ; cartanFormulaNamed =
        true
    ; cartanFormulaNamedIsTrue =
        refl
    ; cartanFormulaProved =
        false
    ; cartanFormulaProvedIsFalse =
        refl
    ; stokesTheoremNamed =
        true
    ; stokesTheoremNamedIsTrue =
        refl
    ; stokesTheoremProved =
        false
    ; stokesTheoremProvedIsFalse =
        refl
    ; poincareLemmaNamed =
        true
    ; poincareLemmaNamedIsTrue =
        refl
    ; poincareLemmaProved =
        false
    ; poincareLemmaProvedIsFalse =
        refl
    ; bianchiIdentityNamed =
        true
    ; bianchiIdentityNamedIsTrue =
        refl
    ; bianchiIdentityProved =
        false
    ; bianchiIdentityProvedIsFalse =
        refl
    ; identityTargetNames =
        canonicalDifferentialGeometryIdentityTargets
    ; identityTargetNamesAreCanonical =
        refl
    }

canonicalDifferentialGeometryParityReceipt :
  DifferentialGeometryParityReceipt
canonicalDifferentialGeometryParityReceipt =
  record
    { status =
        differentialGeometryTargetsOnlyNoPromotion
    ; coreInterface =
        canonicalCoreDifferentialGeometryInterfaceSurface
    ; manifoldIntake =
        canonicalManifoldIntakeSurface
    ; smoothMapIntake =
        canonicalSmoothMapIntakeSurface
    ; bundleFiberIntake =
        canonicalBundleFiberIntakeSurface
    ; metricAuthorityIntake =
        canonicalMetricAuthorityIntakeSurface
    ; connectionAuthorityIntake =
        canonicalConnectionAuthorityIntakeSurface
    ; curvatureAuthorityIntake =
        canonicalCurvatureAuthorityIntakeSurface
    ; formCalculus =
        canonicalDifferentialFormCalculusSurface
    ; exteriorCalculusOperationIntake =
        canonicalExteriorCalculusOperationIntakeSurface
    ; dSquaredTheoremShape =
        canonicalExteriorDerivativeSquaresToZeroTheoremShape
    ; cartanTheoremShape =
        canonicalCartanFormulaTheoremShape
    ; stokesWithOrientationShape =
        canonicalStokesTheoremWithOrientationShape
    ; poincareHomotopyShape =
        canonicalPoincareHomotopyOperatorShape
    ; bianchiTheoremShape =
        canonicalBianchiIdentityTheoremShape
    ; identitySurface =
        canonicalDifferentialGeometryIdentitySurface
    ; coveredConcepts =
        canonicalDifferentialGeometryConcepts
    ; coveredConceptsAreCanonical =
        refl
    ; openObligations =
        canonicalDifferentialGeometryOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; physLeanParityLayerNamed =
        true
    ; physLeanParityLayerNamedIsTrue =
        refl
    ; physLeanAdaptersImported =
        false
    ; physLeanAdaptersImportedIsFalse =
        refl
    ; identityProofsImported =
        false
    ; identityProofsImportedIsFalse =
        refl
    ; parityPromoted =
        false
    ; parityPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "PhysLean differential-geometry vocabulary is named as a DASHI parity target only"
        ∷ "Manifold Point/dimension/chart/chartInv/roundtrip, SmoothMap/smoothId/smoothComp, and tangent/cotangent fibers are checked intake shapes"
        ∷ "Connection includes connectionChartTransformAuthority with Gamma'^k_ij chart-transform formula text; no connection authority is imported"
        ∷ "Exterior derivative square records Schwarz symmetry plus antisymmetry cancellation content, but d(d omega)=0 remains unproved here"
        ∷ "Cartan records L_X=d i_X+i_X d and derivation-agrees-on-generators structure; Stokes records orientationConvention/stokesStatement/stokesAuthorityName/stokesAuthoritySlot"
        ∷ "Poincare records K, radial vector R, and dK+Kd=id shape; Bianchi records cyclic second Bianchi with torsion-free and Jacobi dependencies"
        ∷ "physLeanAdaptersImported, identityProofsImported, and parityPromoted remain false without external authority"
        ∷ []
    }

differentialGeometryParityPromotedIsFalse :
  parityPromoted canonicalDifferentialGeometryParityReceipt
  ≡
  false
differentialGeometryParityPromotedIsFalse =
  refl

differentialGeometryIdentityProofsImportedIsFalse :
  identityProofsImported canonicalDifferentialGeometryParityReceipt
  ≡
  false
differentialGeometryIdentityProofsImportedIsFalse =
  refl

differentialGeometryOpenObligationsCanonical :
  openObligations canonicalDifferentialGeometryParityReceipt
  ≡
  canonicalDifferentialGeometryOpenObligations
differentialGeometryOpenObligationsCanonical =
  refl
