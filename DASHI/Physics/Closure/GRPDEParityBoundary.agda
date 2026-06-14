module DASHI.Physics.Closure.GRPDEParityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.List using (List; _∷_; [])

------------------------------------------------------------------------
-- GR / PDE parity boundary.
--
-- This module names reusable Agda-side interfaces for the PhysLean-adjacent
-- GR and PDE surface requested by the parallel round.  It is intentionally a
-- checked boundary: local DASHI receipts may be recorded as typed surfaces,
-- while continuum GR/PDE theorems, PhysLean parity, Clay claims, and external
-- theorem imports remain blocked until explicit authority tokens are supplied.

data ParityAuthoritySource : Set where
  localDASHIReceipt :
    ParityAuthoritySource

  externalFormalLibrary :
    ParityAuthoritySource

  peerReviewedContinuumTheorem :
    ParityAuthoritySource

  diagnosticPlaceholder :
    ParityAuthoritySource

data ParityPromotionStatus : Set where
  interfaceBoundaryOnly :
    ParityPromotionStatus

  localReceiptOnly :
    ParityPromotionStatus

  externallyAuthorized :
    ParityPromotionStatus

data GeometrySignature : Set where
  riemannian :
    GeometrySignature

  lorentzian :
    GeometrySignature

  pseudoRiemannian :
    GeometrySignature

data PDEClass : Set where
  hyperbolicPDE :
    PDEClass

  parabolicPDE :
    PDEClass

  ellipticPDE :
    PDEClass

  mixedTypePDE :
    PDEClass

data BoundaryConditionKind : Set where
  cauchyBoundary :
    BoundaryConditionKind

  dirichletBoundary :
    BoundaryConditionKind

  neumannBoundary :
    BoundaryConditionKind

  gaugeBoundary :
    BoundaryConditionKind

  weakBoundary :
    BoundaryConditionKind

data GRComponent : Set where
  manifoldComponent :
    GRComponent

  metricTensorComponent :
    GRComponent

  inverseMetricComponent :
    GRComponent

  leviCivitaConnectionComponent :
    GRComponent

  riemannCurvatureComponent :
    GRComponent

  ricciCurvatureComponent :
    GRComponent

  scalarCurvatureComponent :
    GRComponent

  einsteinTensorComponent :
    GRComponent

  stressEnergyComponent :
    GRComponent

  einsteinEquationComponent :
    GRComponent

canonicalGRComponents :
  List GRComponent
canonicalGRComponents =
  manifoldComponent
  ∷ metricTensorComponent
  ∷ inverseMetricComponent
  ∷ leviCivitaConnectionComponent
  ∷ riemannCurvatureComponent
  ∷ ricciCurvatureComponent
  ∷ scalarCurvatureComponent
  ∷ einsteinTensorComponent
  ∷ stressEnergyComponent
  ∷ einsteinEquationComponent
  ∷ []

data PDEComponent : Set where
  differentialOperatorComponent :
    PDEComponent

  boundaryConditionComponent :
    PDEComponent

  initialConditionComponent :
    PDEComponent

  weakFormulationComponent :
    PDEComponent

  weakSolutionComponent :
    PDEComponent

  energyFunctionalComponent :
    PDEComponent

  energyEstimateComponent :
    PDEComponent

  regularityCriterionComponent :
    PDEComponent

  navierStokesBoundaryComponent :
    PDEComponent

  yangMillsBoundaryComponent :
    PDEComponent

canonicalPDEComponents :
  List PDEComponent
canonicalPDEComponents =
  differentialOperatorComponent
  ∷ boundaryConditionComponent
  ∷ initialConditionComponent
  ∷ weakFormulationComponent
  ∷ weakSolutionComponent
  ∷ energyFunctionalComponent
  ∷ energyEstimateComponent
  ∷ regularityCriterionComponent
  ∷ navierStokesBoundaryComponent
  ∷ yangMillsBoundaryComponent
  ∷ []

data ExternalTheoremBlocker : Set where
  missingPhysLeanManifoldMetricImport :
    ExternalTheoremBlocker

  missingLeviCivitaUniquenessAuthority :
    ExternalTheoremBlocker

  missingCurvatureConventionAuthority :
    ExternalTheoremBlocker

  missingEinsteinEquationAuthority :
    ExternalTheoremBlocker

  missingStressEnergyUnitAuthority :
    ExternalTheoremBlocker

  missingWeakSolutionExistenceAuthority :
    ExternalTheoremBlocker

  missingEnergyEstimateAuthority :
    ExternalTheoremBlocker

  missingNavierStokesContinuumAuthority :
    ExternalTheoremBlocker

  missingYangMillsContinuumAuthority :
    ExternalTheoremBlocker

canonicalExternalTheoremBlockers :
  List ExternalTheoremBlocker
canonicalExternalTheoremBlockers =
  missingPhysLeanManifoldMetricImport
  ∷ missingLeviCivitaUniquenessAuthority
  ∷ missingCurvatureConventionAuthority
  ∷ missingEinsteinEquationAuthority
  ∷ missingStressEnergyUnitAuthority
  ∷ missingWeakSolutionExistenceAuthority
  ∷ missingEnergyEstimateAuthority
  ∷ missingNavierStokesContinuumAuthority
  ∷ missingYangMillsContinuumAuthority
  ∷ []

record GRManifoldMetricInterface : Setω where
  field
    Manifold :
      Set

    Point :
      Set

    Scalar :
      Set

    TangentVector :
      Point →
      Set

    CotangentVector :
      Point →
      Set

    TwoTensor :
      Point →
      Set

    signature :
      GeometrySignature

    dimension :
      Nat

    metric :
      (p : Point) →
      TwoTensor p

    inverseMetric :
      (p : Point) →
      TwoTensor p

    pairMetric :
      (p : Point) →
      TangentVector p →
      TangentVector p →
      Scalar

    raiseIndex :
      (p : Point) →
      CotangentVector p →
      TangentVector p

    lowerIndex :
      (p : Point) →
      TangentVector p →
      CotangentVector p

    metricBoundary :
      List String

record LeviCivitaConnectionInterface
  (geometry : GRManifoldMetricInterface) : Setω where
  open GRManifoldMetricInterface geometry

  field
    VectorField :
      Set

    Connection :
      Set

    connection :
      Connection

    covariantDerivative :
      VectorField →
      VectorField →
      VectorField

    torsion :
      VectorField →
      VectorField →
      VectorField

    metricCompatibility :
      Set

    torsionFree :
      Set

    leviCivitaUniquenessAuthority :
      Bool

    leviCivitaUniquenessAuthorityIsFalse :
      leviCivitaUniquenessAuthority ≡ false

    connectionBoundary :
      List String

record CurvatureInterface
  (geometry : GRManifoldMetricInterface)
  (connection : LeviCivitaConnectionInterface geometry) : Setω where
  open GRManifoldMetricInterface geometry
  open LeviCivitaConnectionInterface connection

  field
    RiemannTensor :
      Set

    RicciTensor :
      Set

    ScalarCurvature :
      Set

    EinsteinTensor :
      Set

    riemann :
      Connection →
      RiemannTensor

    ricci :
      RiemannTensor →
      RicciTensor

    scalarCurvature :
      RicciTensor →
      ScalarCurvature

    einsteinTensor :
      RicciTensor →
      ScalarCurvature →
      EinsteinTensor

    bianchiIdentity :
      Set

    contractedBianchiIdentity :
      Set

    curvatureConventionAuthority :
      Bool

    curvatureConventionAuthorityIsFalse :
      curvatureConventionAuthority ≡ false

    curvatureBoundary :
      List String

record StressEnergyInterface
  (geometry : GRManifoldMetricInterface) : Setω where
  open GRManifoldMetricInterface geometry

  field
    MatterField :
      Set

    StressEnergyTensor :
      MatterField →
      Set

    matterField :
      MatterField

    stressEnergy :
      StressEnergyTensor matterField

    divergenceFreeStressEnergy :
      Set

    energyDensityUnitAuthority :
      Bool

    pressureUnitAuthority :
      Bool

    stressEnergyUnitAuthorityPresent :
      Bool

    stressEnergyUnitAuthorityPresentIsFalse :
      stressEnergyUnitAuthorityPresent ≡ false

    stressEnergyBoundary :
      List String

record EinsteinEquationInterface
  (geometry : GRManifoldMetricInterface)
  (connection : LeviCivitaConnectionInterface geometry)
  (curvature : CurvatureInterface geometry connection)
  (matter : StressEnergyInterface geometry) : Setω where
  open CurvatureInterface curvature
  open StressEnergyInterface matter

  field
    CosmologicalConstant :
      Set

    CouplingConstant :
      Set

    cosmologicalConstant :
      CosmologicalConstant

    gravitationalCoupling :
      CouplingConstant

    leftHandSide :
      EinsteinTensor →
      CosmologicalConstant →
      EinsteinTensor

    rightHandSide :
      StressEnergyTensor matterField →
      CouplingConstant →
      StressEnergyTensor matterField

    einsteinEquationLaw :
      Set

    vacuumEinsteinEquationLaw :
      Set

    sourcedEinsteinAuthority :
      Bool

    sourcedEinsteinAuthorityIsFalse :
      sourcedEinsteinAuthority ≡ false

    einsteinBoundary :
      List String

record PDEOperatorInterface : Setω where
  field
    Domain :
      Set

    Time :
      Set

    Scalar :
      Set

    State :
      Set

    TestFunction :
      Set

    Operator :
      Set

    pdeClass :
      PDEClass

    boundaryKind :
      BoundaryConditionKind

    operator :
      Operator

    residual :
      Operator →
      State →
      TestFunction →
      Scalar

    zeroResidual :
      Scalar

    pdeBoundary :
      List String

record WeakSolutionInterface
  (pde : PDEOperatorInterface) : Setω where
  open PDEOperatorInterface pde

  field
    TrialSpace :
      Set

    TestSpace :
      Set

    WeakSolution :
      TrialSpace →
      Set

    selectedTrial :
      TrialSpace

    selectedWeakSolution :
      WeakSolution selectedTrial

    weakResidualLaw :
      Set

    boundaryTraceLaw :
      Set

    externalExistenceAuthority :
      Bool

    externalExistenceAuthorityIsFalse :
      externalExistenceAuthority ≡ false

    weakSolutionBoundary :
      List String

record EnergyEstimateInterface
  (pde : PDEOperatorInterface)
  (weak : WeakSolutionInterface pde) : Setω where
  open PDEOperatorInterface pde
  open WeakSolutionInterface weak

  field
    Energy :
      Set

    energy :
      TrialSpace →
      Energy

    energyOrder :
      Energy →
      Energy →
      Set

    aPrioriBound :
      Set

    gronwallStep :
      Set

    dissipationTerm :
      Set

    estimateCloses :
      Bool

    estimateClosesIsFalse :
      estimateCloses ≡ false

    energyEstimateBoundary :
      List String

record NavierStokesPDEBoundaryInterface : Setω where
  field
    velocityFieldName :
      String

    pressureFieldName :
      String

    incompressibilityLawName :
      String

    weakLerayHopfLawName :
      String

    globalRegularityAuthority :
      Bool

    globalRegularityAuthorityIsFalse :
      globalRegularityAuthority ≡ false

    nsBoundary :
      List String

record YangMillsPDEBoundaryInterface : Setω where
  field
    connectionFieldName :
      String

    curvatureFieldName :
      String

    covariantEquationName :
      String

    bianchiLawName :
      String

    massGapAuthority :
      Bool

    massGapAuthorityIsFalse :
      massGapAuthority ≡ false

    ymBoundary :
      List String

record ExternalTheoremAuthorityToken : Setω where
  field
    source :
      ParityAuthoritySource

    libraryOrPaperName :
      String

    theoremName :
      String

    importedAsCheckedAgda :
      Bool

    externalTheoremAccepted :
      Bool

    authorityBoundary :
      List String

record GRPDEParityPromotion : Setω where
  field
    grAuthority :
      ExternalTheoremAuthorityToken

    pdeAuthority :
      ExternalTheoremAuthorityToken

    grTokenAccepted :
      ExternalTheoremAuthorityToken.externalTheoremAccepted grAuthority
      ≡
      true

    pdeTokenAccepted :
      ExternalTheoremAuthorityToken.externalTheoremAccepted pdeAuthority
      ≡
      true

    grTokenImported :
      ExternalTheoremAuthorityToken.importedAsCheckedAgda grAuthority
      ≡
      true

    pdeTokenImported :
      ExternalTheoremAuthorityToken.importedAsCheckedAgda pdeAuthority
      ≡
      true

    promotionStatus :
      ParityPromotionStatus

    promotionBoundary :
      List String

record GRPDEParityBoundaryReceipt : Setω where
  field
    receiptName :
      String

    status :
      ParityPromotionStatus

    grComponents :
      List GRComponent

    grComponentsAreCanonical :
      grComponents ≡ canonicalGRComponents

    pdeComponents :
      List PDEComponent

    pdeComponentsAreCanonical :
      pdeComponents ≡ canonicalPDEComponents

    externalBlockers :
      List ExternalTheoremBlocker

    externalBlockersAreCanonical :
      externalBlockers ≡ canonicalExternalTheoremBlockers

    namesGRInterface :
      Bool

    namesGRInterfaceIsTrue :
      namesGRInterface ≡ true

    namesPDEInterface :
      Bool

    namesPDEInterfaceIsTrue :
      namesPDEInterface ≡ true

    namesNavierStokesBoundary :
      Bool

    namesNavierStokesBoundaryIsTrue :
      namesNavierStokesBoundary ≡ true

    namesYangMillsBoundary :
      Bool

    namesYangMillsBoundaryIsTrue :
      namesYangMillsBoundary ≡ true

    hasLocalDASHIReceipts :
      Bool

    hasLocalDASHIReceiptsIsTrue :
      hasLocalDASHIReceipts ≡ true

    hasExternalGRTheoremAuthority :
      Bool

    hasExternalGRTheoremAuthorityIsFalse :
      hasExternalGRTheoremAuthority ≡ false

    hasExternalPDETheoremAuthority :
      Bool

    hasExternalPDETheoremAuthorityIsFalse :
      hasExternalPDETheoremAuthority ≡ false

    importsPhysLeanParity :
      Bool

    importsPhysLeanParityIsFalse :
      importsPhysLeanParity ≡ false

    promotesEinsteinEquation :
      Bool

    promotesEinsteinEquationIsFalse :
      promotesEinsteinEquation ≡ false

    promotesWeakSolutionExistence :
      Bool

    promotesWeakSolutionExistenceIsFalse :
      promotesWeakSolutionExistence ≡ false

    promotesEnergyEstimate :
      Bool

    promotesEnergyEstimateIsFalse :
      promotesEnergyEstimate ≡ false

    promotesNavierStokesClayClaim :
      Bool

    promotesNavierStokesClayClaimIsFalse :
      promotesNavierStokesClayClaim ≡ false

    promotesYangMillsClayClaim :
      Bool

    promotesYangMillsClayClaimIsFalse :
      promotesYangMillsClayClaim ≡ false

    promotesPhysLeanParity :
      Bool

    promotesPhysLeanParityIsFalse :
      promotesPhysLeanParity ≡ false

    noPromotionWithoutGRAuthority :
      hasExternalGRTheoremAuthority ≡ false →
      promotesEinsteinEquation ≡ false

    noPromotionWithoutPDEAuthority :
      hasExternalPDETheoremAuthority ≡ false →
      promotesWeakSolutionExistence ≡ false

    noPhysLeanParityWithoutImport :
      importsPhysLeanParity ≡ false →
      promotesPhysLeanParity ≡ false

    boundaryNotes :
      List String

canonicalGRPDEParityBoundaryReceipt :
  GRPDEParityBoundaryReceipt
canonicalGRPDEParityBoundaryReceipt =
  record
    { receiptName =
        "GR/PDE parity boundary: interface names only, fail-closed theorem authority"
    ; status =
        interfaceBoundaryOnly
    ; grComponents =
        canonicalGRComponents
    ; grComponentsAreCanonical =
        refl
    ; pdeComponents =
        canonicalPDEComponents
    ; pdeComponentsAreCanonical =
        refl
    ; externalBlockers =
        canonicalExternalTheoremBlockers
    ; externalBlockersAreCanonical =
        refl
    ; namesGRInterface =
        true
    ; namesGRInterfaceIsTrue =
        refl
    ; namesPDEInterface =
        true
    ; namesPDEInterfaceIsTrue =
        refl
    ; namesNavierStokesBoundary =
        true
    ; namesNavierStokesBoundaryIsTrue =
        refl
    ; namesYangMillsBoundary =
        true
    ; namesYangMillsBoundaryIsTrue =
        refl
    ; hasLocalDASHIReceipts =
        true
    ; hasLocalDASHIReceiptsIsTrue =
        refl
    ; hasExternalGRTheoremAuthority =
        false
    ; hasExternalGRTheoremAuthorityIsFalse =
        refl
    ; hasExternalPDETheoremAuthority =
        false
    ; hasExternalPDETheoremAuthorityIsFalse =
        refl
    ; importsPhysLeanParity =
        false
    ; importsPhysLeanParityIsFalse =
        refl
    ; promotesEinsteinEquation =
        false
    ; promotesEinsteinEquationIsFalse =
        refl
    ; promotesWeakSolutionExistence =
        false
    ; promotesWeakSolutionExistenceIsFalse =
        refl
    ; promotesEnergyEstimate =
        false
    ; promotesEnergyEstimateIsFalse =
        refl
    ; promotesNavierStokesClayClaim =
        false
    ; promotesNavierStokesClayClaimIsFalse =
        refl
    ; promotesYangMillsClayClaim =
        false
    ; promotesYangMillsClayClaimIsFalse =
        refl
    ; promotesPhysLeanParity =
        false
    ; promotesPhysLeanParityIsFalse =
        refl
    ; noPromotionWithoutGRAuthority =
        λ _ → refl
    ; noPromotionWithoutPDEAuthority =
        λ _ → refl
    ; noPhysLeanParityWithoutImport =
        λ _ → refl
    ; boundaryNotes =
        "GR interfaces name manifold, metric, inverse metric, Levi-Civita connection, curvature, Einstein tensor, stress-energy, and Einstein equation targets"
        ∷ "PDE interfaces name hyperbolic, parabolic, elliptic, weak-solution, and energy-estimate targets"
        ∷ "Navier-Stokes and Yang-Mills are represented as boundary interfaces only"
        ∷ "Local DASHI receipts are separated from external formal-library or continuum-theorem authority"
        ∷ "No PhysLean parity import is claimed by this module"
        ∷ "No Einstein equation, weak solution theorem, energy estimate, Navier-Stokes Clay result, or Yang-Mills mass-gap result is promoted here"
        ∷ []
    }

canonicalGRPDEParityFirstExternalBlocker :
  GRPDEParityBoundaryReceipt.externalBlockers
    canonicalGRPDEParityBoundaryReceipt
  ≡
  canonicalExternalTheoremBlockers
canonicalGRPDEParityFirstExternalBlocker =
  refl

canonicalGRPDEParityNoEinsteinPromotion :
  GRPDEParityBoundaryReceipt.promotesEinsteinEquation
    canonicalGRPDEParityBoundaryReceipt
  ≡
  false
canonicalGRPDEParityNoEinsteinPromotion =
  refl

canonicalGRPDEParityNoPhysLeanPromotion :
  GRPDEParityBoundaryReceipt.promotesPhysLeanParity
    canonicalGRPDEParityBoundaryReceipt
  ≡
  false
canonicalGRPDEParityNoPhysLeanPromotion =
  refl
