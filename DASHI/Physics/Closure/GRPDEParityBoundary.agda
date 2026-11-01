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

  leviCivitaKoszulFormulaComponent :
    GRComponent

  curvatureConventionComponent :
    GRComponent

  contractedBianchiAuthorityComponent :
    GRComponent

  kappaUnitConventionComponent :
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
  ∷ leviCivitaKoszulFormulaComponent
  ∷ curvatureConventionComponent
  ∷ contractedBianchiAuthorityComponent
  ∷ kappaUnitConventionComponent
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

  weakTestPairingComponent :
    PDEComponent

  externalExistenceAuthorityComponent :
    PDEComponent

  energyInequalityComponent :
    PDEComponent

  continuumClayBlockerComponent :
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
  ∷ weakTestPairingComponent
  ∷ externalExistenceAuthorityComponent
  ∷ energyInequalityComponent
  ∷ continuumClayBlockerComponent
  ∷ []

data LeviCivitaIntakeShape : Set where
  torsionFreeMetricCompatibleUniquenessShape :
    LeviCivitaIntakeShape

  koszulFormulaShape :
    LeviCivitaIntakeShape

canonicalLeviCivitaIntakeShapes :
  List LeviCivitaIntakeShape
canonicalLeviCivitaIntakeShapes =
  torsionFreeMetricCompatibleUniquenessShape
  ∷ koszulFormulaShape
  ∷ []

data CurvatureConventionIntakeShape : Set where
  riemannRhoSigmaMuNuShape :
    CurvatureConventionIntakeShape

  ricciTraceShape :
    CurvatureConventionIntakeShape

  scalarCurvatureTraceShape :
    CurvatureConventionIntakeShape

  einsteinTensorConventionShape :
    CurvatureConventionIntakeShape

  contractedBianchiAuthorityShape :
    CurvatureConventionIntakeShape

canonicalCurvatureConventionIntakeShapes :
  List CurvatureConventionIntakeShape
canonicalCurvatureConventionIntakeShapes =
  riemannRhoSigmaMuNuShape
  ∷ ricciTraceShape
  ∷ scalarCurvatureTraceShape
  ∷ einsteinTensorConventionShape
  ∷ contractedBianchiAuthorityShape
  ∷ []

data EinsteinEquationIntakeShape : Set where
  einsteinLambdaKappaEquationShape :
    EinsteinEquationIntakeShape

  kappaUnitConventionShape :
    EinsteinEquationIntakeShape

canonicalEinsteinEquationIntakeShapes :
  List EinsteinEquationIntakeShape
canonicalEinsteinEquationIntakeShapes =
  einsteinLambdaKappaEquationShape
  ∷ kappaUnitConventionShape
  ∷ []

data WeakPDEIntakeShape : Set where
  navierStokesWeakTestPairingShape :
    WeakPDEIntakeShape

  yangMillsWeakTestPairingShape :
    WeakPDEIntakeShape

  externalExistenceAuthorityShape :
    WeakPDEIntakeShape

  energyInequalityShape :
    WeakPDEIntakeShape

  navierStokesGlobalRegularityBlockerShape :
    WeakPDEIntakeShape

  yangMillsMassGapBlockerShape :
    WeakPDEIntakeShape

canonicalWeakPDEIntakeShapes :
  List WeakPDEIntakeShape
canonicalWeakPDEIntakeShapes =
  navierStokesWeakTestPairingShape
  ∷ yangMillsWeakTestPairingShape
  ∷ externalExistenceAuthorityShape
  ∷ energyInequalityShape
  ∷ navierStokesGlobalRegularityBlockerShape
  ∷ yangMillsMassGapBlockerShape
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

  missingKappaUnitConventionAuthority :
    ExternalTheoremBlocker

  missingContractedBianchiAuthority :
    ExternalTheoremBlocker

  missingWeakSolutionExistenceAuthority :
    ExternalTheoremBlocker

  missingEnergyEstimateAuthority :
    ExternalTheoremBlocker

  missingEnergyInequalityAuthority :
    ExternalTheoremBlocker

  missingNavierStokesContinuumAuthority :
    ExternalTheoremBlocker

  missingNavierStokesGlobalRegularityAuthority :
    ExternalTheoremBlocker

  missingYangMillsContinuumAuthority :
    ExternalTheoremBlocker

  missingYangMillsMassGapAuthority :
    ExternalTheoremBlocker

canonicalExternalTheoremBlockers :
  List ExternalTheoremBlocker
canonicalExternalTheoremBlockers =
  missingPhysLeanManifoldMetricImport
  ∷ missingLeviCivitaUniquenessAuthority
  ∷ missingCurvatureConventionAuthority
  ∷ missingEinsteinEquationAuthority
  ∷ missingStressEnergyUnitAuthority
  ∷ missingKappaUnitConventionAuthority
  ∷ missingContractedBianchiAuthority
  ∷ missingWeakSolutionExistenceAuthority
  ∷ missingEnergyEstimateAuthority
  ∷ missingEnergyInequalityAuthority
  ∷ missingNavierStokesContinuumAuthority
  ∷ missingNavierStokesGlobalRegularityAuthority
  ∷ missingYangMillsContinuumAuthority
  ∷ missingYangMillsMassGapAuthority
  ∷ []

data SIDimensionExponent : Set where
  minusOneExponent :
    SIDimensionExponent

  plusOneExponent :
    SIDimensionExponent

  minusTwoExponent :
    SIDimensionExponent

  zeroExponent :
    SIDimensionExponent

record SIDimensionVector : Set where
  field
    lengthExponent :
      SIDimensionExponent

    massExponent :
      SIDimensionExponent

    timeExponent :
      SIDimensionExponent

    electricCurrentExponent :
      SIDimensionExponent

    thermodynamicTemperatureExponent :
      SIDimensionExponent

    amountOfSubstanceExponent :
      SIDimensionExponent

    luminousIntensityExponent :
      SIDimensionExponent

canonicalStressEnergySIDimensionVector :
  SIDimensionVector
canonicalStressEnergySIDimensionVector =
  record
    { lengthExponent =
        minusOneExponent
    ; massExponent =
        plusOneExponent
    ; timeExponent =
        minusTwoExponent
    ; electricCurrentExponent =
        zeroExponent
    ; thermodynamicTemperatureExponent =
        zeroExponent
    ; amountOfSubstanceExponent =
        zeroExponent
    ; luminousIntensityExponent =
        zeroExponent
    }

canonicalStressEnergySIDimensionVectorString :
  String
canonicalStressEnergySIDimensionVectorString =
  "(-1,1,-2,0,0,0,0)"

record ContractedBianchiAuthorityRow : Set where
  field
    contractedBianchiAuthorityRowName :
      String

    contractedBianchiAuthorityRowNameIsExact :
      contractedBianchiAuthorityRowName ≡ "contractedBianchiAuthority"

    contractedBianchiConventionSource :
      ParityAuthoritySource

    contractedBianchiDerivationText :
      String

    contractedBianchiAuthorityAccepted :
      Bool

    contractedBianchiAuthorityAcceptedIsFalse :
      contractedBianchiAuthorityAccepted ≡ false

    contractedBianchiPromotionStatus :
      ParityPromotionStatus

    contractedBianchiRowNotes :
      List String

contractedBianchiAuthority :
  ContractedBianchiAuthorityRow
contractedBianchiAuthority =
  record
    { contractedBianchiAuthorityRowName =
        "contractedBianchiAuthority"
    ; contractedBianchiAuthorityRowNameIsExact =
        refl
    ; contractedBianchiConventionSource =
        diagnosticPlaceholder
    ; contractedBianchiDerivationText =
        "contracted Bianchi derivation: second Bianchi identity -> contract first and third indices -> nabla^mu G_munu = 0"
    ; contractedBianchiAuthorityAccepted =
        false
    ; contractedBianchiAuthorityAcceptedIsFalse =
        refl
    ; contractedBianchiPromotionStatus =
        interfaceBoundaryOnly
    ; contractedBianchiRowNotes =
        "The row name is exactly contractedBianchiAuthority"
        ∷ "The derivation text is recorded, but no external GR theorem authority is accepted here"
        ∷ []
    }

record LeviCivitaCanonicalPayloadRow : Set where
  field
    leviCivitaPayloadIntakeShapes :
      List LeviCivitaIntakeShape

    leviCivitaPayloadIntakeShapesAreCanonical :
      leviCivitaPayloadIntakeShapes ≡ canonicalLeviCivitaIntakeShapes

    leviCivitaPayloadKoszulFormulaExactText :
      String

    leviCivitaPayloadKoszulFormulaShapeText :
      String

    leviCivitaPayloadTorsionFree :
      Bool

    leviCivitaPayloadTorsionFreeIsTrue :
      leviCivitaPayloadTorsionFree ≡ true

    leviCivitaPayloadTorsionFreeExactText :
      String

    leviCivitaPayloadMetricCompatible :
      Bool

    leviCivitaPayloadMetricCompatibleIsTrue :
      leviCivitaPayloadMetricCompatible ≡ true

    leviCivitaPayloadMetricCompatibleExactText :
      String

    leviCivitaPayloadUniquenessProof :
      String

    leviCivitaPayloadUniquenessProofAuthority :
      Bool

    leviCivitaPayloadUniquenessProofAuthorityIsFalse :
      leviCivitaPayloadUniquenessProofAuthority ≡ false

    leviCivitaPayloadNondegeneracyProofRoute :
      String

canonicalLeviCivitaPayloadRow :
  LeviCivitaCanonicalPayloadRow
canonicalLeviCivitaPayloadRow =
  record
    { leviCivitaPayloadIntakeShapes =
        canonicalLeviCivitaIntakeShapes
    ; leviCivitaPayloadIntakeShapesAreCanonical =
        refl
    ; leviCivitaPayloadKoszulFormulaExactText =
        "2*g(nabla_X Y,Z) = X(g(Y,Z)) + Y(g(Z,X)) - Z(g(X,Y)) - g(X,[Y,Z]) + g(Y,[Z,X]) + g(Z,[X,Y])"
    ; leviCivitaPayloadKoszulFormulaShapeText =
        "Koszul formula exact text/shape: (X,Y,Z) |-> 2*g(nabla_X Y,Z)"
    ; leviCivitaPayloadTorsionFree =
        true
    ; leviCivitaPayloadTorsionFreeIsTrue =
        refl
    ; leviCivitaPayloadTorsionFreeExactText =
        "torsionFree: T(X,Y) = nabla_X Y - nabla_Y X - [X,Y] = 0"
    ; leviCivitaPayloadMetricCompatible =
        true
    ; leviCivitaPayloadMetricCompatibleIsTrue =
        refl
    ; leviCivitaPayloadMetricCompatibleExactText =
        "metricCompatible: X(g(Y,Z)) = g(nabla_X Y,Z) + g(Y,nabla_X Z)"
    ; leviCivitaPayloadUniquenessProof =
        "uniquenessProof: torsionFree + metricCompatible + nondegenerate metric -> Koszul formula determines g(nabla_X Y,Z) for every Z; nondegeneracy determines nabla_X Y uniquely"
    ; leviCivitaPayloadUniquenessProofAuthority =
        false
    ; leviCivitaPayloadUniquenessProofAuthorityIsFalse =
        refl
    ; leviCivitaPayloadNondegeneracyProofRoute =
        "nondegeneracy proof route: if g(V,Z) = g(W,Z) for every Z, then g(V-W,Z) = 0 for every Z, and metric nondegeneracy gives V = W"
    }

record CurvatureConventionCanonicalPayloadRow : Set where
  field
    curvaturePayloadIntakeShapes :
      List CurvatureConventionIntakeShape

    curvaturePayloadIntakeShapesAreCanonical :
      curvaturePayloadIntakeShapes ≡ canonicalCurvatureConventionIntakeShapes

    curvaturePayloadMTWPositiveRiemannSignConventionExactString :
      String

    curvaturePayloadRicciConvention :
      String

    curvaturePayloadScalarConvention :
      String

    curvaturePayloadEinsteinTensorConvention :
      String

    curvaturePayloadContractedBianchiDerivation :
      String

    curvaturePayloadContractedBianchiAuthorityRow :
      ContractedBianchiAuthorityRow

    curvaturePayloadConventionAuthority :
      Bool

    curvaturePayloadConventionAuthorityIsFalse :
      curvaturePayloadConventionAuthority ≡ false

canonicalCurvatureConventionPayloadRow :
  CurvatureConventionCanonicalPayloadRow
canonicalCurvatureConventionPayloadRow =
  record
    { curvaturePayloadIntakeShapes =
        canonicalCurvatureConventionIntakeShapes
    ; curvaturePayloadIntakeShapesAreCanonical =
        refl
    ; curvaturePayloadMTWPositiveRiemannSignConventionExactString =
        "MTW positive Riemann sign convention: R^rho_sigma_mu_nu = partial_mu Gamma^rho_nu_sigma - partial_nu Gamma^rho_mu_sigma + Gamma^rho_mu_lambda Gamma^lambda_nu_sigma - Gamma^rho_nu_lambda Gamma^lambda_mu_sigma"
    ; curvaturePayloadRicciConvention =
        "Ricci convention: Ric_munu = R^rho_mu_rho_nu"
    ; curvaturePayloadScalarConvention =
        "scalar curvature convention: R = g^munu Ric_munu"
    ; curvaturePayloadEinsteinTensorConvention =
        "Einstein tensor convention: G_munu = Ric_munu - (1/2) R g_munu"
    ; curvaturePayloadContractedBianchiDerivation =
        "contracted Bianchi derivation: second Bianchi identity -> contract first and third indices -> nabla^mu G_munu = 0"
    ; curvaturePayloadContractedBianchiAuthorityRow =
        contractedBianchiAuthority
    ; curvaturePayloadConventionAuthority =
        false
    ; curvaturePayloadConventionAuthorityIsFalse =
        refl
    }

record EinsteinEquationCanonicalPayloadRow : Set where
  field
    einsteinPayloadIntakeShapes :
      List EinsteinEquationIntakeShape

    einsteinPayloadIntakeShapesAreCanonical :
      einsteinPayloadIntakeShapes ≡ canonicalEinsteinEquationIntakeShapes

    einsteinPayloadEquationExactText :
      String

    einsteinPayloadKappaDefinition :
      String

    einsteinPayloadStressEnergyUnits :
      String

    einsteinPayloadStressEnergySIDimensionVector :
      SIDimensionVector

    einsteinPayloadStressEnergySIDimensionVectorIsCanonical :
      einsteinPayloadStressEnergySIDimensionVector
      ≡
      canonicalStressEnergySIDimensionVector

    einsteinPayloadStressEnergySIDimensionVectorExactText :
      String

    einsteinPayloadLambdaConvention :
      String

    einsteinPayloadSourcedEinsteinAuthority :
      Bool

    einsteinPayloadSourcedEinsteinAuthorityIsFalse :
      einsteinPayloadSourcedEinsteinAuthority ≡ false

canonicalEinsteinEquationPayloadRow :
  EinsteinEquationCanonicalPayloadRow
canonicalEinsteinEquationPayloadRow =
  record
    { einsteinPayloadIntakeShapes =
        canonicalEinsteinEquationIntakeShapes
    ; einsteinPayloadIntakeShapesAreCanonical =
        refl
    ; einsteinPayloadEquationExactText =
        "G_munu + Lambda g_munu = kappa T_munu"
    ; einsteinPayloadKappaDefinition =
        "8*pi*G/c^4"
    ; einsteinPayloadStressEnergyUnits =
        "J/m^3 = kg/(m*s^2)"
    ; einsteinPayloadStressEnergySIDimensionVector =
        canonicalStressEnergySIDimensionVector
    ; einsteinPayloadStressEnergySIDimensionVectorIsCanonical =
        refl
    ; einsteinPayloadStressEnergySIDimensionVectorExactText =
        canonicalStressEnergySIDimensionVectorString
    ; einsteinPayloadLambdaConvention =
        "Lambda convention: Lambda g_munu is on the geometric left-hand side in G_munu + Lambda g_munu = kappa T_munu"
    ; einsteinPayloadSourcedEinsteinAuthority =
        false
    ; einsteinPayloadSourcedEinsteinAuthorityIsFalse =
        refl
    }

record EnergyInequalityExactRow : Set where
  field
    energyInequalityExactRowName :
      String

    energyInequalityExactRowText :
      String

    energyInequalityExactRowAuthorityAccepted :
      Bool

    energyInequalityExactRowAuthorityAcceptedIsFalse :
      energyInequalityExactRowAuthorityAccepted ≡ false

canonicalNSEnergyInequalityExactRow :
  EnergyInequalityExactRow
canonicalNSEnergyInequalityExactRow =
  record
    { energyInequalityExactRowName =
        "Navier-Stokes energy inequality exact row"
    ; energyInequalityExactRowText =
        "1/2||u(t)||_L2^2 + nu integral_0^t ||grad u(s)||_L2^2 ds <= 1/2||u(0)||_L2^2 + integral_0^t <f(s),u(s)> ds"
    ; energyInequalityExactRowAuthorityAccepted =
        false
    ; energyInequalityExactRowAuthorityAcceptedIsFalse =
        refl
    }

record WeakPDECanonicalPayloadRow : Set where
  field
    weakPDEPayloadIntakeShapes :
      List WeakPDEIntakeShape

    weakPDEPayloadIntakeShapesAreCanonical :
      weakPDEPayloadIntakeShapes ≡ canonicalWeakPDEIntakeShapes

    weakPDEPayloadNavierStokesWeakFormulationExactPairing :
      String

    weakPDEPayloadNavierStokesTrilinearForm :
      String

    weakPDEPayloadNavierStokesEnergyInequalityRow :
      EnergyInequalityExactRow

    weakPDEPayloadYangMillsWeakFormulationExactL2Pairing :
      String

    weakPDEPayloadNSGlobalRegularityAuthority :
      Bool

    weakPDEPayloadNSGlobalRegularityAuthorityIsFalse :
      weakPDEPayloadNSGlobalRegularityAuthority ≡ false

    weakPDEPayloadYMMassGapAuthority :
      Bool

    weakPDEPayloadYMMassGapAuthorityIsFalse :
      weakPDEPayloadYMMassGapAuthority ≡ false

canonicalWeakPDEPayloadRow :
  WeakPDECanonicalPayloadRow
canonicalWeakPDEPayloadRow =
  record
    { weakPDEPayloadIntakeShapes =
        canonicalWeakPDEIntakeShapes
    ; weakPDEPayloadIntakeShapesAreCanonical =
        refl
    ; weakPDEPayloadNavierStokesWeakFormulationExactPairing =
        "NS weak formulation exact pairing: <partial_t u,v> + nu (grad u,grad v)_L2 + b(u,u,v) - (p,div v)_L2 = <f,v>, with (div u,q)_L2 = 0"
    ; weakPDEPayloadNavierStokesTrilinearForm =
        "b(u,v,w) = integral_Omega ((u . grad) v) . w dx"
    ; weakPDEPayloadNavierStokesEnergyInequalityRow =
        canonicalNSEnergyInequalityExactRow
    ; weakPDEPayloadYangMillsWeakFormulationExactL2Pairing =
        "YM weak formulation exact L2 pairing: <D_A^* F_A,a>_L2 = <F_A,D_A a>_L2 = 0 for all compactly supported Lie-algebra-valued 1-forms a"
    ; weakPDEPayloadNSGlobalRegularityAuthority =
        false
    ; weakPDEPayloadNSGlobalRegularityAuthorityIsFalse =
        refl
    ; weakPDEPayloadYMMassGapAuthority =
        false
    ; weakPDEPayloadYMMassGapAuthorityIsFalse =
        refl
    }

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

    leviCivitaInterfaceTorsionFreeExactText :
      String

    leviCivitaIntakeShapes :
      List LeviCivitaIntakeShape

    koszulFormula :
      Set

    leviCivitaInterfaceKoszulFormulaExactText :
      String

    leviCivitaInterfaceMetricCompatibleExactText :
      String

    leviCivitaInterfaceUniquenessProofExactText :
      String

    leviCivitaInterfaceNondegeneracyProofRoute :
      String

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

    curvatureConventionIntakeShapes :
      List CurvatureConventionIntakeShape

    riemannRhoSigmaMuNuConvention :
      Set

    curvatureInterfaceMTWPositiveRiemannSignConventionExactString :
      String

    ricciTraceConvention :
      Set

    curvatureInterfaceRicciTensorConventionExactText :
      String

    scalarCurvatureTraceConvention :
      Set

    curvatureInterfaceScalarCurvatureConventionExactText :
      String

    einsteinTensorConvention :
      Set

    curvatureInterfaceEinsteinTensorConventionExactText :
      String

    bianchiIdentity :
      Set

    contractedBianchiIdentity :
      Set

    curvatureInterfaceContractedBianchiDerivationExactText :
      String

    curvatureInterfaceContractedBianchiAuthorityRow :
      ContractedBianchiAuthorityRow

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

    einsteinEquationIntakeShapes :
      List EinsteinEquationIntakeShape

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

    einsteinInterfaceEquationExactText :
      String

    vacuumEinsteinEquationLaw :
      Set

    einsteinInterfaceKappaDefinition :
      String

    einsteinInterfaceStressEnergyUnits :
      String

    einsteinInterfaceStressEnergySIDimensionVector :
      SIDimensionVector

    einsteinInterfaceStressEnergySIDimensionVectorExactText :
      String

    einsteinInterfaceLambdaConvention :
      String

    sourcedEinsteinAuthority :
      Bool

    kappaUnitConventionAuthority :
      Bool

    kappaUnitConventionAuthorityIsFalse :
      kappaUnitConventionAuthority ≡ false

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

    weakPDEIntakeShapes :
      List WeakPDEIntakeShape

    testFunctionPairing :
      TrialSpace →
      TestSpace →
      Scalar

    WeakSolution :
      TrialSpace →
      Set

    selectedTrial :
      TrialSpace

    selectedWeakSolution :
      WeakSolution selectedTrial

    weakResidualLaw :
      Set

    weakSolutionInterfaceWeakResidualLawExactText :
      String

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

    energyInequality :
      Set

    energyEstimateInterfaceEnergyInequalityExactRow :
      EnergyInequalityExactRow

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

    weakTestPairingLawName :
      String

    nsBoundaryWeakTestPairingExactText :
      String

    nsBoundaryTrilinearFormExactText :
      String

    energyInequalityLawName :
      String

    nsBoundaryEnergyInequalityExactRow :
      EnergyInequalityExactRow

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

    weakTestPairingLawName :
      String

    ymBoundaryWeakTestPairingExactText :
      String

    energyInequalityLawName :
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

    leviCivitaIntakeShapes :
      List LeviCivitaIntakeShape

    leviCivitaIntakeShapesAreCanonical :
      leviCivitaIntakeShapes ≡ canonicalLeviCivitaIntakeShapes

    curvatureConventionIntakeShapes :
      List CurvatureConventionIntakeShape

    curvatureConventionIntakeShapesAreCanonical :
      curvatureConventionIntakeShapes ≡ canonicalCurvatureConventionIntakeShapes

    einsteinEquationIntakeShapes :
      List EinsteinEquationIntakeShape

    einsteinEquationIntakeShapesAreCanonical :
      einsteinEquationIntakeShapes ≡ canonicalEinsteinEquationIntakeShapes

    weakPDEIntakeShapes :
      List WeakPDEIntakeShape

    weakPDEIntakeShapesAreCanonical :
      weakPDEIntakeShapes ≡ canonicalWeakPDEIntakeShapes

    leviCivitaPayloadRow :
      LeviCivitaCanonicalPayloadRow

    leviCivitaPayloadRowIsCanonical :
      leviCivitaPayloadRow ≡ canonicalLeviCivitaPayloadRow

    curvatureConventionPayloadRow :
      CurvatureConventionCanonicalPayloadRow

    curvatureConventionPayloadRowIsCanonical :
      curvatureConventionPayloadRow ≡ canonicalCurvatureConventionPayloadRow

    einsteinEquationPayloadRow :
      EinsteinEquationCanonicalPayloadRow

    einsteinEquationPayloadRowIsCanonical :
      einsteinEquationPayloadRow ≡ canonicalEinsteinEquationPayloadRow

    weakPDEPayloadRow :
      WeakPDECanonicalPayloadRow

    weakPDEPayloadRowIsCanonical :
      weakPDEPayloadRow ≡ canonicalWeakPDEPayloadRow

    receiptContractedBianchiAuthorityRow :
      ContractedBianchiAuthorityRow

    receiptContractedBianchiAuthorityRowIsCanonical :
      receiptContractedBianchiAuthorityRow ≡ contractedBianchiAuthority

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

    promotesNavierStokesGlobalRegularity :
      Bool

    promotesNavierStokesGlobalRegularityIsFalse :
      promotesNavierStokesGlobalRegularity ≡ false

    promotesYangMillsMassGap :
      Bool

    promotesYangMillsMassGapIsFalse :
      promotesYangMillsMassGap ≡ false

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

    noNavierStokesGlobalRegularityWithoutAuthority :
      hasExternalPDETheoremAuthority ≡ false →
      promotesNavierStokesGlobalRegularity ≡ false

    noYangMillsMassGapWithoutAuthority :
      hasExternalPDETheoremAuthority ≡ false →
      promotesYangMillsMassGap ≡ false

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
    ; leviCivitaIntakeShapes =
        canonicalLeviCivitaIntakeShapes
    ; leviCivitaIntakeShapesAreCanonical =
        refl
    ; curvatureConventionIntakeShapes =
        canonicalCurvatureConventionIntakeShapes
    ; curvatureConventionIntakeShapesAreCanonical =
        refl
    ; einsteinEquationIntakeShapes =
        canonicalEinsteinEquationIntakeShapes
    ; einsteinEquationIntakeShapesAreCanonical =
        refl
    ; weakPDEIntakeShapes =
        canonicalWeakPDEIntakeShapes
    ; weakPDEIntakeShapesAreCanonical =
        refl
    ; leviCivitaPayloadRow =
        canonicalLeviCivitaPayloadRow
    ; leviCivitaPayloadRowIsCanonical =
        refl
    ; curvatureConventionPayloadRow =
        canonicalCurvatureConventionPayloadRow
    ; curvatureConventionPayloadRowIsCanonical =
        refl
    ; einsteinEquationPayloadRow =
        canonicalEinsteinEquationPayloadRow
    ; einsteinEquationPayloadRowIsCanonical =
        refl
    ; weakPDEPayloadRow =
        canonicalWeakPDEPayloadRow
    ; weakPDEPayloadRowIsCanonical =
        refl
    ; receiptContractedBianchiAuthorityRow =
        contractedBianchiAuthority
    ; receiptContractedBianchiAuthorityRowIsCanonical =
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
    ; promotesNavierStokesGlobalRegularity =
        false
    ; promotesNavierStokesGlobalRegularityIsFalse =
        refl
    ; promotesYangMillsMassGap =
        false
    ; promotesYangMillsMassGapIsFalse =
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
    ; noNavierStokesGlobalRegularityWithoutAuthority =
        λ _ → refl
    ; noYangMillsMassGapWithoutAuthority =
        λ _ → refl
    ; boundaryNotes =
        "GR interfaces name manifold, metric, inverse metric, Levi-Civita uniqueness, Koszul formula, curvature convention, Einstein tensor, stress-energy, and Einstein equation targets"
        ∷ "Curvature intake names R^rho_sigma_mu_nu, Ricci trace, scalar trace, Einstein tensor, and contracted Bianchi authority shapes"
        ∷ "Einstein intake names G + Lambda g = kappa T and kappa/unit convention shapes"
        ∷ "PDE interfaces name hyperbolic, parabolic, elliptic, weak-solution, weak test-function pairing, energy-estimate, and energy-inequality targets"
        ∷ "Navier-Stokes and Yang-Mills are represented as weak boundary interfaces only"
        ∷ "Local DASHI receipts are separated from external formal-library or continuum-theorem authority"
        ∷ "No PhysLean parity import is claimed by this module"
        ∷ "No Einstein equation, weak solution theorem, energy estimate, Navier-Stokes global-regularity result, or Yang-Mills mass-gap result is promoted here"
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

canonicalGRPDEParityLeviCivitaIntake :
  GRPDEParityBoundaryReceipt.leviCivitaIntakeShapes
    canonicalGRPDEParityBoundaryReceipt
  ≡
  canonicalLeviCivitaIntakeShapes
canonicalGRPDEParityLeviCivitaIntake =
  refl

canonicalGRPDEParityCurvatureConventionIntake :
  GRPDEParityBoundaryReceipt.curvatureConventionIntakeShapes
    canonicalGRPDEParityBoundaryReceipt
  ≡
  canonicalCurvatureConventionIntakeShapes
canonicalGRPDEParityCurvatureConventionIntake =
  refl

canonicalGRPDEParityEinsteinEquationIntake :
  GRPDEParityBoundaryReceipt.einsteinEquationIntakeShapes
    canonicalGRPDEParityBoundaryReceipt
  ≡
  canonicalEinsteinEquationIntakeShapes
canonicalGRPDEParityEinsteinEquationIntake =
  refl

canonicalGRPDEParityWeakPDEIntake :
  GRPDEParityBoundaryReceipt.weakPDEIntakeShapes
    canonicalGRPDEParityBoundaryReceipt
  ≡
  canonicalWeakPDEIntakeShapes
canonicalGRPDEParityWeakPDEIntake =
  refl

canonicalGRPDEParityNoNavierStokesGlobalRegularity :
  GRPDEParityBoundaryReceipt.promotesNavierStokesGlobalRegularity
    canonicalGRPDEParityBoundaryReceipt
  ≡
  false
canonicalGRPDEParityNoNavierStokesGlobalRegularity =
  refl

canonicalGRPDEParityNoYangMillsMassGap :
  GRPDEParityBoundaryReceipt.promotesYangMillsMassGap
    canonicalGRPDEParityBoundaryReceipt
  ≡
  false
canonicalGRPDEParityNoYangMillsMassGap =
  refl

canonicalLeviCivitaKoszulFormulaExactText :
  LeviCivitaCanonicalPayloadRow.leviCivitaPayloadKoszulFormulaExactText
    canonicalLeviCivitaPayloadRow
  ≡
  "2*g(nabla_X Y,Z) = X(g(Y,Z)) + Y(g(Z,X)) - Z(g(X,Y)) - g(X,[Y,Z]) + g(Y,[Z,X]) + g(Z,[X,Y])"
canonicalLeviCivitaKoszulFormulaExactText =
  refl

canonicalLeviCivitaUniquenessProofAuthorityFalse :
  LeviCivitaCanonicalPayloadRow.leviCivitaPayloadUniquenessProofAuthority
    canonicalLeviCivitaPayloadRow
  ≡
  false
canonicalLeviCivitaUniquenessProofAuthorityFalse =
  refl

contractedBianchiAuthorityNameExact :
  ContractedBianchiAuthorityRow.contractedBianchiAuthorityRowName
    contractedBianchiAuthority
  ≡
  "contractedBianchiAuthority"
contractedBianchiAuthorityNameExact =
  refl

contractedBianchiAuthorityFailClosed :
  ContractedBianchiAuthorityRow.contractedBianchiAuthorityAccepted
    contractedBianchiAuthority
  ≡
  false
contractedBianchiAuthorityFailClosed =
  refl

canonicalCurvatureMTWPositiveConventionExactText :
  CurvatureConventionCanonicalPayloadRow.curvaturePayloadMTWPositiveRiemannSignConventionExactString
    canonicalCurvatureConventionPayloadRow
  ≡
  "MTW positive Riemann sign convention: R^rho_sigma_mu_nu = partial_mu Gamma^rho_nu_sigma - partial_nu Gamma^rho_mu_sigma + Gamma^rho_mu_lambda Gamma^lambda_nu_sigma - Gamma^rho_nu_lambda Gamma^lambda_mu_sigma"
canonicalCurvatureMTWPositiveConventionExactText =
  refl

canonicalEinsteinEquationExactText :
  EinsteinEquationCanonicalPayloadRow.einsteinPayloadEquationExactText
    canonicalEinsteinEquationPayloadRow
  ≡
  "G_munu + Lambda g_munu = kappa T_munu"
canonicalEinsteinEquationExactText =
  refl

canonicalEinsteinKappaDefinitionExactText :
  EinsteinEquationCanonicalPayloadRow.einsteinPayloadKappaDefinition
    canonicalEinsteinEquationPayloadRow
  ≡
  "8*pi*G/c^4"
canonicalEinsteinKappaDefinitionExactText =
  refl

canonicalEinsteinStressEnergyUnitsExactText :
  EinsteinEquationCanonicalPayloadRow.einsteinPayloadStressEnergyUnits
    canonicalEinsteinEquationPayloadRow
  ≡
  "J/m^3 = kg/(m*s^2)"
canonicalEinsteinStressEnergyUnitsExactText =
  refl

canonicalEinsteinStressEnergySIDimensionVectorExactText :
  EinsteinEquationCanonicalPayloadRow.einsteinPayloadStressEnergySIDimensionVectorExactText
    canonicalEinsteinEquationPayloadRow
  ≡
  "(-1,1,-2,0,0,0,0)"
canonicalEinsteinStressEnergySIDimensionVectorExactText =
  refl

canonicalNSWeakFormulationExactPairing :
  WeakPDECanonicalPayloadRow.weakPDEPayloadNavierStokesWeakFormulationExactPairing
    canonicalWeakPDEPayloadRow
  ≡
  "NS weak formulation exact pairing: <partial_t u,v> + nu (grad u,grad v)_L2 + b(u,u,v) - (p,div v)_L2 = <f,v>, with (div u,q)_L2 = 0"
canonicalNSWeakFormulationExactPairing =
  refl

canonicalNSTrilinearFormExactText :
  WeakPDECanonicalPayloadRow.weakPDEPayloadNavierStokesTrilinearForm
    canonicalWeakPDEPayloadRow
  ≡
  "b(u,v,w) = integral_Omega ((u . grad) v) . w dx"
canonicalNSTrilinearFormExactText =
  refl

canonicalNSEnergyInequalityExactText :
  EnergyInequalityExactRow.energyInequalityExactRowText
    canonicalNSEnergyInequalityExactRow
  ≡
  "1/2||u(t)||_L2^2 + nu integral_0^t ||grad u(s)||_L2^2 ds <= 1/2||u(0)||_L2^2 + integral_0^t <f(s),u(s)> ds"
canonicalNSEnergyInequalityExactText =
  refl

canonicalYMWeakL2PairingExactText :
  WeakPDECanonicalPayloadRow.weakPDEPayloadYangMillsWeakFormulationExactL2Pairing
    canonicalWeakPDEPayloadRow
  ≡
  "YM weak formulation exact L2 pairing: <D_A^* F_A,a>_L2 = <F_A,D_A a>_L2 = 0 for all compactly supported Lie-algebra-valued 1-forms a"
canonicalYMWeakL2PairingExactText =
  refl

canonicalWeakPDENoNSGlobalRegularityAuthority :
  WeakPDECanonicalPayloadRow.weakPDEPayloadNSGlobalRegularityAuthority
    canonicalWeakPDEPayloadRow
  ≡
  false
canonicalWeakPDENoNSGlobalRegularityAuthority =
  refl

canonicalWeakPDENoYMMassGapAuthority :
  WeakPDECanonicalPayloadRow.weakPDEPayloadYMMassGapAuthority
    canonicalWeakPDEPayloadRow
  ≡
  false
canonicalWeakPDENoYMMassGapAuthority =
  refl
