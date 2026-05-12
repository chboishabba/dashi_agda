module DASHI.Physics.Closure.GRDiscreteBianchiFiniteR where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Combinatorics.String.LieAlgebra as StringLie
import DASHI.Physics.Constraints.Bracket as Bracket
import DASHI.Physics.Constraints.Generators as GEN
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRFirstOrderGravityScope as G4

------------------------------------------------------------------------
-- GR finite-r discrete Bianchi sidecar.
--
-- This file does not claim vacuum Einstein closure.  It records the smallest
-- missing bridge from carrier-level Jacobi data to a finite-r Bianchi law,
-- while pointing at the existing GR, Einstein-equation, curvature, CRT
-- connection, and Lie-algebra surfaces.

data GRDiscreteBianchiFiniteRReadiness : Set where
  blockedBeforeFiniteRConnectionAndJacobiBridge :
    GRDiscreteBianchiFiniteRReadiness

data GRDiscreteBianchiFiniteRMissingIngredient : Set where
  missingFiniteRBaseCarrier :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRNeighbourhoodOrCellComplex :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRDerivationCarrier :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRCarrierLieBracket :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRJacobiWitness :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRConnectionOrShiftLaw :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingMetricCompatibility :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingCarrierConnectionIsLeviCivita :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingStandardLeviCivitaAlgebraLaw :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingSixTermRicciIdentityCancellation :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingCurvatureAsBracketDefect :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingCovariantExteriorDerivativeOrCyclicSum :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingJacobiToBianchiBridge :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingFiniteRBianchiLaw :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingCurvatureToRicciEinsteinContractionBoundary :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingMetricContractionForRicci :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingTraceEqualsFourVacuumReduction :
    GRDiscreteBianchiFiniteRMissingIngredient

  missingStressEnergyCompatibilityForContractedBianchi :
    GRDiscreteBianchiFiniteRMissingIngredient

canonicalGRDiscreteBianchiFiniteRMissingIngredients :
  List GRDiscreteBianchiFiniteRMissingIngredient
canonicalGRDiscreteBianchiFiniteRMissingIngredients =
  missingFiniteRBaseCarrier
  ∷ missingFiniteRNeighbourhoodOrCellComplex
  ∷ missingFiniteRDerivationCarrier
  ∷ missingFiniteRCarrierLieBracket
  ∷ missingFiniteRJacobiWitness
  ∷ missingFiniteRConnectionOrShiftLaw
  ∷ missingMetricCompatibility
  ∷ missingCarrierConnectionIsLeviCivita
  ∷ missingStandardLeviCivitaAlgebraLaw
  ∷ missingSixTermRicciIdentityCancellation
  ∷ missingCurvatureAsBracketDefect
  ∷ missingCovariantExteriorDerivativeOrCyclicSum
  ∷ missingJacobiToBianchiBridge
  ∷ missingFiniteRBianchiLaw
  ∷ missingCurvatureToRicciEinsteinContractionBoundary
  ∷ missingMetricContractionForRicci
  ∷ missingTraceEqualsFourVacuumReduction
  ∷ missingStressEnergyCompatibilityForContractedBianchi
  ∷ []

data GRDiscreteBianchiFiniteRUnsupportedClaim : Set where
  unsupportedVacuumEinsteinClosureClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedFiniteRGRPromotionClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedCurvatureRicciContractionClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedRicciFromBianchiClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedVacuumRicciZeroClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedSourcedEinsteinLawClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

  unsupportedGRQFTPromotionClaim :
    GRDiscreteBianchiFiniteRUnsupportedClaim

canonicalGRDiscreteBianchiFiniteRUnsupportedClaims :
  List GRDiscreteBianchiFiniteRUnsupportedClaim
canonicalGRDiscreteBianchiFiniteRUnsupportedClaims =
  unsupportedVacuumEinsteinClosureClaim
  ∷ unsupportedFiniteRGRPromotionClaim
  ∷ unsupportedCurvatureRicciContractionClaim
  ∷ unsupportedRicciFromBianchiClaim
  ∷ unsupportedVacuumRicciZeroClaim
  ∷ unsupportedSourcedEinsteinLawClaim
  ∷ unsupportedGRQFTPromotionClaim
  ∷ []

record GRStringLieJacobiToBianchiBridgeObligation : Set₁ where
  field
    finiteRCarrierLieAlgebra :
      StringLie.LieAlgebra

    ConnectionCarrier :
      Set

    CurvatureCarrier :
      Set

    BianchiExpressionCarrier :
      Set

    curvatureAsBracketDefect :
      ConnectionCarrier →
      StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra →
      StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra →
      CurvatureCarrier

    bianchiExpression :
      ConnectionCarrier →
      StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra →
      StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra →
      StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra →
      BianchiExpressionCarrier

    finiteRBianchiLaw :
      BianchiExpressionCarrier →
      Set

    finiteRJacobiWitness :
      (x y z :
        StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra) →
      StringLie.LieAlgebra._bracket_ finiteRCarrierLieAlgebra x
        (StringLie.LieAlgebra._bracket_ finiteRCarrierLieAlgebra y z)
      ≡
      StringLie.LieAlgebra._bracket_ finiteRCarrierLieAlgebra
        (StringLie.LieAlgebra._bracket_ finiteRCarrierLieAlgebra x y)
        z

    jacobiToBianchiBridge :
      (connection : ConnectionCarrier) →
      (x y z :
        StringLie.LieAlgebra.Carrier finiteRCarrierLieAlgebra) →
      finiteRBianchiLaw
        (bianchiExpression connection x y z)

    bridgeBoundary :
      List String

record GRConstraintLieLikeJacobiPrerequisite
  (CS : GEN.ConstraintSystem)
  (L : Bracket.LieLike CS) : Set₁ where
  field
    constraintJacobiWitness :
      Bracket.LieLike.jacobi L

    prerequisiteBoundary :
      List String

record GRFiniteRRicciFromBianchiObligation : Set₁ where
  field
    FiniteRBaseCarrier :
      Set

    MetricCarrier :
      Set

    ConnectionCarrier :
      Set

    CurvatureCarrier :
      Set

    BianchiExpressionCarrier :
      Set

    RicciCarrier :
      Set

    ScalarTraceCarrier :
      Set

    VacuumEinsteinCarrier :
      Set

    metricContractionForRicci :
      MetricCarrier →
      CurvatureCarrier →
      RicciCarrier

    traceOfMetricIsFour :
      MetricCarrier →
      ScalarTraceCarrier →
      Set

    finiteRBianchiLaw :
      BianchiExpressionCarrier →
      Set

    ricciZero :
      RicciCarrier →
      Set

    vacuumEinsteinSurface :
      VacuumEinsteinCarrier →
      Set

    ricciFromBianchi :
      (metric : MetricCarrier) →
      (curvature : CurvatureCarrier) →
      (trace : ScalarTraceCarrier) →
      traceOfMetricIsFour metric trace →
      ricciZero (metricContractionForRicci metric curvature)

    vacuumRicciZero :
      (vacuum : VacuumEinsteinCarrier) →
      vacuumEinsteinSurface vacuum →
      Set

    boundary :
      List String

record GRMetricCompatibleLeviCivitaCarrierObligation : Set₁ where
  field
    FiniteRBaseCarrier :
      Set

    MetricCarrier :
      Set

    ConnectionCarrier :
      Set

    metricAt :
      FiniteRBaseCarrier →
      MetricCarrier

    carrierConnection :
      FiniteRBaseCarrier →
      ConnectionCarrier

    metricCompatibility :
      MetricCarrier →
      ConnectionCarrier →
      Set

    carrierMetricCompatibility :
      (base : FiniteRBaseCarrier) →
      metricCompatibility
        (metricAt base)
        (carrierConnection base)

    carrierConnectionIsLeviCivita :
      (base : FiniteRBaseCarrier) →
      Set

    leviCivitaCompatibilityBoundary :
      List String

record GRStandardLeviCivitaAlgebraLawObligation : Set₁ where
  field
    FiniteRBaseCarrier :
      Set

    MetricCarrier :
      Set

    ConnectionCarrier :
      Set

    CoordinateIndex :
      Set

    AlgebraScalar :
      Set

    metricAt :
      FiniteRBaseCarrier →
      MetricCarrier

    connectionAt :
      FiniteRBaseCarrier →
      ConnectionCarrier

    christoffelSymbol :
      ConnectionCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      AlgebraScalar

    covariantDerivativeOfMetric :
      ConnectionCarrier →
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      AlgebraScalar

    metricSymmetryLaw :
      (base : FiniteRBaseCarrier) →
      (mu nu : CoordinateIndex) →
      Set

    christoffelSymmetryLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      christoffelSymbol (connectionAt base) lambda mu nu
      ≡
      christoffelSymbol (connectionAt base) lambda nu mu

    metricCompatibilityLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      Set

    sixTermRicciIdentityCancellation :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      Set

    traceEqualsFourLaw :
      MetricCarrier →
      Set

    lawBoundary :
      List String

record GRCarrierConnectionLeviCivitaDependency : Set₁ where
  field
    metricCompatibleCarrier :
      GRMetricCompatibleLeviCivitaCarrierObligation

    standardLeviCivitaAlgebraLaw :
      GRStandardLeviCivitaAlgebraLawObligation

    selectedMetricConnectionMatch :
      List String

    dependencyBoundary :
      List String

record GRMetricCompatibilityLeviCivitaPressureSurface : Set where
  field
    metricCompatibilityObligationName :
      String

    carrierConnectionIsLeviCivitaObligationName :
      String

    standardLeviCivitaAlgebraLawObligationName :
      String

    sixTermRicciIdentityCancellationObligationName :
      String

    missingMetricCompatibilityMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingCarrierConnectionIsLeviCivitaMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingStandardLeviCivitaAlgebraLawMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingSixTermRicciIdentityCancellationMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    boundary :
      List String

canonicalGRMetricCompatibilityLeviCivitaPressureSurface :
  GRMetricCompatibilityLeviCivitaPressureSurface
canonicalGRMetricCompatibilityLeviCivitaPressureSurface =
  record
    { metricCompatibilityObligationName =
        "GRMetricCompatibleLeviCivitaCarrierObligation.metricCompatibility"
    ; carrierConnectionIsLeviCivitaObligationName =
        "GRMetricCompatibleLeviCivitaCarrierObligation.carrierConnectionIsLeviCivita"
    ; standardLeviCivitaAlgebraLawObligationName =
        "GRStandardLeviCivitaAlgebraLawObligation"
    ; sixTermRicciIdentityCancellationObligationName =
        "GRStandardLeviCivitaAlgebraLawObligation.sixTermRicciIdentityCancellation"
    ; missingMetricCompatibilityMarker =
        missingMetricCompatibility
    ; missingCarrierConnectionIsLeviCivitaMarker =
        missingCarrierConnectionIsLeviCivita
    ; missingStandardLeviCivitaAlgebraLawMarker =
        missingStandardLeviCivitaAlgebraLaw
    ; missingSixTermRicciIdentityCancellationMarker =
        missingSixTermRicciIdentityCancellation
    ; boundary =
        "metricCompatibility must be proved for the selected finite-r metric and carrier connection"
        ∷ "carrierConnectionIsLeviCivita must identify the selected connection as the Levi-Civita connection for that metric"
        ∷ "The Levi-Civita dependency must expose the standard Christoffel algebra law: metric symmetry, torsion-free symmetry, and metric compatibility"
        ∷ "The Ricci reduction must expose the six-term cancellation obtained by expanding the covariant derivative of the selected metric"
        ∷ "Without these witnesses, Ricci contraction and vacuum Ricci-zero reduction remain obligation surfaces"
        ∷ []
    }

data GRFiniteRRicciVacuumSurfaceStatus : Set where
  ricciVacuumSurfaceObligationOnly :
    GRFiniteRRicciVacuumSurfaceStatus

record GRFiniteRRicciVacuumZeroObligationSurface : Setω where
  field
    status :
      GRFiniteRRicciVacuumSurfaceStatus

    ricciFromBianchiObligationName :
      String

    vacuumRicciZeroObligationName :
      String

    metricCompatibilityLeviCivitaPressure :
      GRMetricCompatibilityLeviCivitaPressureSurface

    missingMetricContraction :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingTraceEqualsFour :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingCurvatureContractionBoundary :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingIngredients :
      List GRDiscreteBianchiFiniteRMissingIngredient

    unsupportedClaims :
      List GRDiscreteBianchiFiniteRUnsupportedClaim

    obligationBoundary :
      List String

canonicalGRFiniteRRicciVacuumZeroObligationSurface :
  GRFiniteRRicciVacuumZeroObligationSurface
canonicalGRFiniteRRicciVacuumZeroObligationSurface =
  record
    { status =
        ricciVacuumSurfaceObligationOnly
    ; ricciFromBianchiObligationName =
        "GRFiniteRRicciFromBianchiObligation.ricciFromBianchi"
    ; vacuumRicciZeroObligationName =
        "GRFiniteRRicciFromBianchiObligation.vacuumRicciZero"
    ; metricCompatibilityLeviCivitaPressure =
        canonicalGRMetricCompatibilityLeviCivitaPressureSurface
    ; missingMetricContraction =
        missingMetricContractionForRicci
    ; missingTraceEqualsFour =
        missingTraceEqualsFourVacuumReduction
    ; missingCurvatureContractionBoundary =
        missingCurvatureToRicciEinsteinContractionBoundary
    ; missingIngredients =
        missingMetricCompatibility
        ∷ missingCarrierConnectionIsLeviCivita
        ∷ missingStandardLeviCivitaAlgebraLaw
        ∷ missingSixTermRicciIdentityCancellation
        ∷ missingCurvatureToRicciEinsteinContractionBoundary
        ∷ missingMetricContractionForRicci
        ∷ missingTraceEqualsFourVacuumReduction
        ∷ missingStressEnergyCompatibilityForContractedBianchi
        ∷ []
    ; unsupportedClaims =
        unsupportedRicciFromBianchiClaim
        ∷ unsupportedVacuumRicciZeroClaim
        ∷ unsupportedVacuumEinsteinClosureClaim
        ∷ []
    ; obligationBoundary =
        "ricciFromBianchi requires a metric contraction from finite-r curvature to Ricci"
        ∷ "metricCompatibility and carrierConnectionIsLeviCivita are required before the selected connection can support Levi-Civita Ricci contraction"
        ∷ "carrierConnectionIsLeviCivita now factors through GRStandardLeviCivitaAlgebraLawObligation rather than a black-box theorem"
        ∷ "sixTermRicciIdentityCancellation is the exact algebraic first-missing item for metric compatibility once a concrete metric and connection are selected"
        ∷ "vacuum Ricci-zero reduction requires the trace=4 contraction law for the selected metric/signature surface"
        ∷ "The current flat-vacuum diagnostic is not a finite-r Ricci contraction theorem"
        ∷ "No contracted Bianchi, covariant conservation, or sourced Einstein law is produced here"
        ∷ []
    }

record GRDiscreteBianchiFiniteRObligationSurface : Setω where
  field
    readiness :
      GRDiscreteBianchiFiniteRReadiness

    firstOrderGRScope :
      G4.GRFirstOrderGravityScope

    finiteRW4BianchiMatterSurface :
      G4.GRFiniteRW4BianchiMatterObligationSurface

    einsteinEquationCandidate :
      EEC.EinsteinEquationCandidateObligationSurface

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    crtConnectionDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    ricciVacuumZeroSurface :
      GRFiniteRRicciVacuumZeroObligationSurface

    metricCompatibilityLeviCivitaPressure :
      GRMetricCompatibilityLeviCivitaPressureSurface

    inspectedJacobiSurfaces :
      List String

    jacobiToBianchiBridgeObligationName :
      String

    bridgeInputShape :
      String

    bridgeOutputShape :
      String

    ricciFromBianchiObligationName :
      String

    vacuumRicciZeroObligationName :
      String

    firstMissing :
      GRDiscreteBianchiFiniteRMissingIngredient

    firstMissingIsFiniteRBaseCarrier :
      firstMissing
      ≡
      missingFiniteRBaseCarrier

    missingIngredients :
      List GRDiscreteBianchiFiniteRMissingIngredient

    missingIngredientsAreCanonical :
      missingIngredients
      ≡
      canonicalGRDiscreteBianchiFiniteRMissingIngredients

    unsupportedClaims :
      List GRDiscreteBianchiFiniteRUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalGRDiscreteBianchiFiniteRUnsupportedClaims

    finiteRIngredientBoundary :
      List String

    nonPromotionBoundary :
      List String

canonicalGRDiscreteBianchiFiniteRObligationSurface :
  GRDiscreteBianchiFiniteRObligationSurface
canonicalGRDiscreteBianchiFiniteRObligationSurface =
  record
    { readiness =
        blockedBeforeFiniteRConnectionAndJacobiBridge
    ; firstOrderGRScope =
        G4.canonicalGRFirstOrderGravityScope
    ; finiteRW4BianchiMatterSurface =
        G4.canonicalGRFiniteRW4BianchiMatterObligationSurface
    ; einsteinEquationCandidate =
        EEC.canonicalEinsteinEquationCandidateObligationSurface
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; crtConnectionDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; ricciVacuumZeroSurface =
        canonicalGRFiniteRRicciVacuumZeroObligationSurface
    ; metricCompatibilityLeviCivitaPressure =
        canonicalGRMetricCompatibilityLeviCivitaPressureSurface
    ; inspectedJacobiSurfaces =
        "DASHI.Combinatorics.String.LieAlgebra exposes Carrier, bracket, antisym, and a Jacobi equality over a carrier"
        ∷ "DASHI.Physics.Constraints.Bracket.LieLike exposes a constraint bracket plus abstract antisym and jacobi fields"
        ∷ "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate exposes only flat-vacuum curvature diagnostics and missing non-flat connection/Ricci/Einstein fields"
        ∷ "DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT records no CRT-derived non-flat connection or Bianchi witness"
        ∷ "DASHI.Physics.Closure.GRFirstOrderGravityScope records finite-r Bianchi as an obligation, not as an inhabited law"
        ∷ []
    ; jacobiToBianchiBridgeObligationName =
        "GRStringLieJacobiToBianchiBridgeObligation.jacobiToBianchiBridge"
    ; bridgeInputShape =
        "finite-r carrier Lie bracket with Jacobi witness, finite-r connection/shift, and curvature-as-bracket-defect data"
    ; bridgeOutputShape =
        "finite-r Bianchi law over the covariant cyclic-sum or exterior-derivative expression for the selected curvature carrier"
    ; ricciFromBianchiObligationName =
        "GRFiniteRRicciFromBianchiObligation.ricciFromBianchi"
    ; vacuumRicciZeroObligationName =
        "GRFiniteRRicciFromBianchiObligation.vacuumRicciZero"
    ; firstMissing =
        missingFiniteRBaseCarrier
    ; firstMissingIsFiniteRBaseCarrier =
        refl
    ; missingIngredients =
        canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; missingIngredientsAreCanonical =
        refl
    ; unsupportedClaims =
        canonicalGRDiscreteBianchiFiniteRUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; finiteRIngredientBoundary =
        "The current repo has abstract Jacobi vocabulary, but no selected finite-r base carrier for GR Bianchi"
        ∷ "No finite-r cell/neighbourhood layer or derivation carrier is bound to the GR curvature route"
        ∷ "No finite-r connection or shift law is available as a carrier-internal non-flat connection"
        ∷ "No metricCompatibility witness is available for the selected finite-r metric and carrier connection"
        ∷ "No carrierConnectionIsLeviCivita witness identifies the selected carrier connection as Levi-Civita"
        ∷ "No standard Levi-Civita algebra law is bound to the selected finite-r metric, Christoffel expression, and connection"
        ∷ "No six-term Ricci identity cancellation is supplied for the selected metric/connection pair"
        ∷ "No curvature-as-bracket-defect construction is supplied for the finite-r carrier"
        ∷ "No covariant exterior derivative or cyclic-sum expression is supplied for the Bianchi law"
        ∷ "Therefore the Jacobi-to-Bianchi bridge is named here only as an obligation"
        ∷ "No metric contraction from finite-r curvature to Ricci is supplied"
        ∷ "No trace=4 law is supplied for reducing the vacuum Einstein surface to Ricci zero"
        ∷ []
    ; nonPromotionBoundary =
        "This sidecar does not construct a vacuum Einstein closure theorem"
        ∷ "This sidecar does not convert the flat-vacuum diagnostic into finite-r GR"
        ∷ "This sidecar does not construct a non-flat connection, Ricci contraction, ricciFromBianchi theorem, vacuum Ricci-zero theorem, Einstein tensor law, or sourced Einstein law"
        ∷ "This sidecar does not construct W4MatterStressEnergyInterfaceReceipt"
        ∷ "This sidecar does not promote GR, G4, G6, W4, W5, or GR/QFT closure"
        ∷ []
    }

grDiscreteBianchiFiniteRFirstMissingIsFiniteRBaseCarrier :
  GRDiscreteBianchiFiniteRObligationSurface.firstMissing
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  missingFiniteRBaseCarrier
grDiscreteBianchiFiniteRFirstMissingIsFiniteRBaseCarrier = refl

grDiscreteBianchiFiniteRReadinessIsBlocked :
  GRDiscreteBianchiFiniteRObligationSurface.readiness
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  blockedBeforeFiniteRConnectionAndJacobiBridge
grDiscreteBianchiFiniteRReadinessIsBlocked = refl
