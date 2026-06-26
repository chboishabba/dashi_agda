module DASHI.Physics.Closure.GRDiscreteBianchiFiniteR where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Rational as R using (_/_)
open import Data.Unit using (⊤; tt)
open import DASHI.Core.Q using (ℚ; _+ℚ_; _*ℚ_; zeroℚ; oneℚ; twoℚ)

import DASHI.Combinatorics.String.LieAlgebra as StringLie
import DASHI.Physics.Constraints.Bracket as Bracket
import DASHI.Physics.Constraints.Generators as GEN
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.FactorVecDiscreteMetricTensorSurface as FVMetric
import DASHI.Physics.Closure.GRFirstOrderGravityScope as G4
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar
import DASHI.Physics.Closure.GRSelectedNonFlatMetricInstance as SelectedMetric
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4Stress

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

  missingFiniteRScalarAlgebra :
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
  missingFiniteRScalarAlgebra
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

record GRChristoffelFromMetricSixTermRicciIdentityRequest
  (law : GRStandardLeviCivitaAlgebraLawObligation) : Set₁ where
  open GRStandardLeviCivitaAlgebraLawObligation law

  field
    _+_ :
      AlgebraScalar →
      AlgebraScalar →
      AlgebraScalar

    _-_ :
      AlgebraScalar →
      AlgebraScalar →
      AlgebraScalar

    _*_ :
      AlgebraScalar →
      AlgebraScalar →
      AlgebraScalar

    twoScalar :
      AlgebraScalar

    metricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      AlgebraScalar

    inverseMetricComponent :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      AlgebraScalar

    partialDerivativeOfMetric :
      MetricCarrier →
      CoordinateIndex →
      CoordinateIndex →
      CoordinateIndex →
      AlgebraScalar

    contractCoordinateIndex :
      (CoordinateIndex → AlgebraScalar) →
      AlgebraScalar

    christoffelFromMetricLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      (twoScalar *
        christoffelSymbol (connectionAt base) lambda mu nu)
      ≡
      contractCoordinateIndex
        (λ rho →
          inverseMetricComponent (metricAt base) lambda rho *
          ((partialDerivativeOfMetric (metricAt base) mu nu rho
            + partialDerivativeOfMetric (metricAt base) nu mu rho)
            - partialDerivativeOfMetric (metricAt base) rho mu nu))

    sixTermMetricCompatibilityExpansion :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      covariantDerivativeOfMetric
        (connectionAt base)
        (metricAt base)
        lambda
        mu
        nu
      ≡
      (partialDerivativeOfMetric (metricAt base) lambda mu nu
        - contractCoordinateIndex
          (λ rho →
            christoffelSymbol (connectionAt base) rho lambda mu *
            metricComponent (metricAt base) rho nu))
      - contractCoordinateIndex
        (λ rho →
          christoffelSymbol (connectionAt base) rho lambda nu *
          metricComponent (metricAt base) mu rho)

    sixTermRicciIdentityCancellationLaw :
      (base : FiniteRBaseCarrier) →
      (lambda mu nu : CoordinateIndex) →
      sixTermRicciIdentityCancellation base lambda mu nu

    requestBoundary :
      List String

record GRCarrierConnectionLeviCivitaDependency : Set₁ where
  field
    metricCompatibleCarrier :
      GRMetricCompatibleLeviCivitaCarrierObligation

    standardLeviCivitaAlgebraLaw :
      GRStandardLeviCivitaAlgebraLawObligation

    christoffelFromMetricSixTermRicciIdentityRequest :
      GRChristoffelFromMetricSixTermRicciIdentityRequest
        standardLeviCivitaAlgebraLaw

    selectedMetricConnectionMatch :
      List String

    dependencyBoundary :
      List String

------------------------------------------------------------------------
-- Flat constant finite-r prerequisite surface.
--
-- This is the highest currently inhabited rung.  It ties the GR sidecar to
-- the exact flat Minkowski quadratic receipt, with a constant metric marker
-- and a trivial flat connection.  It is only a prerequisite surface: the
-- scalar algebra, finite contraction, and non-flat/prime-resonant carrier
-- connection needed by the GR Bianchi/Ricci route remain requested below.

data GRFlatConstantMetricFiniteRPrerequisiteStatus : Set where
  flatConstantMetricPrerequisiteOnlyNoCurvedGRPromotion :
    GRFlatConstantMetricFiniteRPrerequisiteStatus

FlatMetricCarrier : Set
FlatMetricCarrier = ML.MinkowskiCarrier → ℤ

FlatConnectionCarrier : Set
FlatConnectionCarrier = ⊤

FlatCoordinateIndex : Set
FlatCoordinateIndex = ⊤

FlatAlgebraScalar : Set
FlatAlgebraScalar = ⊤

flatConstantMetricAt :
  ML.MinkowskiCarrier →
  FlatMetricCarrier
flatConstantMetricAt _ = ML.minkowskiQuadratic

flatConstantConnectionAt :
  ML.MinkowskiCarrier →
  FlatConnectionCarrier
flatConstantConnectionAt _ = tt

flatMetricCompatibility :
  FlatMetricCarrier →
  FlatConnectionCarrier →
  Set
flatMetricCompatibility _ _ = ⊤

canonicalGRFlatConstantMetricCompatibleCarrier :
  GRMetricCompatibleLeviCivitaCarrierObligation
canonicalGRFlatConstantMetricCompatibleCarrier =
  record
    { FiniteRBaseCarrier =
        ML.MinkowskiCarrier
    ; MetricCarrier =
        FlatMetricCarrier
    ; ConnectionCarrier =
        FlatConnectionCarrier
    ; metricAt =
        flatConstantMetricAt
    ; carrierConnection =
        flatConstantConnectionAt
    ; metricCompatibility =
        flatMetricCompatibility
    ; carrierMetricCompatibility =
        λ _ → tt
    ; carrierConnectionIsLeviCivita =
        λ _ → ⊤
    ; leviCivitaCompatibilityBoundary =
        "Flat constant metric marker is tied to MinkowskiLimitReceipt.minkowskiQuadratic"
        ∷ "The selected connection on this prerequisite surface is the trivial flat connection"
        ∷ "Metric compatibility is inhabited only for this flat constant prerequisite"
        ∷ "This does not provide a non-flat carrier-internal connection or a GR promotion"
        ∷ []
    }

canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw :
  GRStandardLeviCivitaAlgebraLawObligation
canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw =
  record
    { FiniteRBaseCarrier =
        ML.MinkowskiCarrier
    ; MetricCarrier =
        FlatMetricCarrier
    ; ConnectionCarrier =
        FlatConnectionCarrier
    ; CoordinateIndex =
        FlatCoordinateIndex
    ; AlgebraScalar =
        FlatAlgebraScalar
    ; metricAt =
        flatConstantMetricAt
    ; connectionAt =
        flatConstantConnectionAt
    ; christoffelSymbol =
        λ _ _ _ _ → tt
    ; covariantDerivativeOfMetric =
        λ _ _ _ _ _ → tt
    ; metricSymmetryLaw =
        λ _ _ _ → ⊤
    ; christoffelSymmetryLaw =
        λ _ _ _ _ → refl
    ; metricCompatibilityLaw =
        λ _ _ _ _ → ⊤
    ; sixTermRicciIdentityCancellation =
        λ _ _ _ _ → ⊤
    ; traceEqualsFourLaw =
        λ _ → ⊤
    ; lawBoundary =
        "Christoffel symbols are trivial on the flat constant prerequisite surface"
        ∷ "The covariant derivative of the constant metric reduces to the unit scalar marker here"
        ∷ "The six-term Ricci cancellation is inhabited only at this flat prerequisite rung"
        ∷ "A finite non-degenerate scalar algebra and finite contraction remain missing for the selected GR carrier"
        ∷ []
    }

canonicalGRFlatConstantChristoffelRequest :
  GRChristoffelFromMetricSixTermRicciIdentityRequest
    canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
canonicalGRFlatConstantChristoffelRequest =
  record
    { _+_ =
        λ _ _ → tt
    ; _-_ =
        λ _ _ → tt
    ; _*_ =
        λ _ _ → tt
    ; twoScalar =
        tt
    ; metricComponent =
        λ _ _ _ → tt
    ; inverseMetricComponent =
        λ _ _ _ → tt
    ; partialDerivativeOfMetric =
        λ _ _ _ _ → tt
    ; contractCoordinateIndex =
        λ _ → tt
    ; christoffelFromMetricLaw =
        λ _ _ _ _ → refl
    ; sixTermMetricCompatibilityExpansion =
        λ _ _ _ _ → refl
    ; sixTermRicciIdentityCancellationLaw =
        λ _ _ _ _ → tt
    ; requestBoundary =
        "All Christoffel-from-metric equations reduce definitionally on the flat constant prerequisite surface"
        ∷ "This request does not instantiate a non-trivial finite scalar algebra, inverse metric table, coordinate derivative, or finite contraction"
        ∷ "Those non-trivial finite-r algebraic ingredients remain the first missing selected-GR metric surface"
        ∷ []
    }

canonicalGRFlatConstantLeviCivitaDependency :
  GRCarrierConnectionLeviCivitaDependency
canonicalGRFlatConstantLeviCivitaDependency =
  record
    { metricCompatibleCarrier =
        canonicalGRFlatConstantMetricCompatibleCarrier
    ; standardLeviCivitaAlgebraLaw =
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
    ; christoffelFromMetricSixTermRicciIdentityRequest =
        canonicalGRFlatConstantChristoffelRequest
    ; selectedMetricConnectionMatch =
        "flat constant metric: MinkowskiLimitReceipt.minkowskiQuadratic"
        ∷ "flat connection: unit/trivial connection marker"
        ∷ []
    ; dependencyBoundary =
        "This dependency is valid only for the flat constant prerequisite"
        ∷ "It must not be used as a non-flat prime-resonant finite-r GR metric receipt"
        ∷ []
    }

data GRFlatMinkowskiFiniteRLeviCivitaStatus : Set where
  flatMinkowskiFiniteRLeviCivitaClosedNoSelectedGRPromotion :
    GRFlatMinkowskiFiniteRLeviCivitaStatus

record GRFlatMinkowskiFiniteRLeviCivitaClosure : Setω where
  field
    status :
      GRFlatMinkowskiFiniteRLeviCivitaStatus

    minkowskiFlatMetricReceipt :
      ML.CarrierQuadraticIsMinkowski

    finiteRBaseIsMinkowski :
      GRMetricCompatibleLeviCivitaCarrierObligation.FiniteRBaseCarrier
        canonicalGRFlatConstantMetricCompatibleCarrier
      ≡
      ML.MinkowskiCarrier

    metricCarrierIsMinkowskiQuadraticFamily :
      GRMetricCompatibleLeviCivitaCarrierObligation.MetricCarrier
        canonicalGRFlatConstantMetricCompatibleCarrier
      ≡
      FlatMetricCarrier

    flatConnectionCarrierIsUnit :
      GRMetricCompatibleLeviCivitaCarrierObligation.ConnectionCarrier
        canonicalGRFlatConstantMetricCompatibleCarrier
      ≡
      FlatConnectionCarrier

    metricAtIsMinkowskiQuadratic :
      (base : ML.MinkowskiCarrier) →
      flatConstantMetricAt base
      ≡
      ML.minkowskiQuadratic

    connectionAtIsTrivial :
      (base : ML.MinkowskiCarrier) →
      flatConstantConnectionAt base
      ≡
      tt

    carrierMetricCompatibilityWitness :
      (base : ML.MinkowskiCarrier) →
      GRMetricCompatibleLeviCivitaCarrierObligation.metricCompatibility
        canonicalGRFlatConstantMetricCompatibleCarrier
        (flatConstantMetricAt base)
        (flatConstantConnectionAt base)

    carrierConnectionIsLeviCivitaWitness :
      (base : ML.MinkowskiCarrier) →
      GRMetricCompatibleLeviCivitaCarrierObligation.carrierConnectionIsLeviCivita
        canonicalGRFlatConstantMetricCompatibleCarrier
        base

    christoffelTorsionFreeWitness :
      (base : ML.MinkowskiCarrier) →
      (lambda mu nu : FlatCoordinateIndex) →
      GRStandardLeviCivitaAlgebraLawObligation.christoffelSymbol
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        (GRStandardLeviCivitaAlgebraLawObligation.connectionAt
          canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
          base)
        lambda
        mu
        nu
      ≡
      GRStandardLeviCivitaAlgebraLawObligation.christoffelSymbol
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        (GRStandardLeviCivitaAlgebraLawObligation.connectionAt
          canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
          base)
        lambda
        nu
        mu

    flatChristoffelFromMetricRequest :
      GRChristoffelFromMetricSixTermRicciIdentityRequest
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw

    flatLeviCivitaDependency :
      GRCarrierConnectionLeviCivitaDependency

    flatLeviCivitaDependencyIsCanonical :
      flatLeviCivitaDependency
      ≡
      canonicalGRFlatConstantLeviCivitaDependency

    standardLawIsCanonical :
      GRCarrierConnectionLeviCivitaDependency.standardLeviCivitaAlgebraLaw
        flatLeviCivitaDependency
      ≡
      canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw

    christoffelRequestIsCanonical :
      flatChristoffelFromMetricRequest
      ≡
      canonicalGRFlatConstantChristoffelRequest

    metricCompatibleCarrierIsCanonical :
      GRCarrierConnectionLeviCivitaDependency.metricCompatibleCarrier
        flatLeviCivitaDependency
      ≡
      canonicalGRFlatConstantMetricCompatibleCarrier

    metricCompatibilityLawWitness :
      (base : ML.MinkowskiCarrier) →
      (lambda mu nu : FlatCoordinateIndex) →
      GRStandardLeviCivitaAlgebraLawObligation.metricCompatibilityLaw
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        base
        lambda
        mu
        nu

    sixTermRicciIdentityCancellationWitness :
      (base : ML.MinkowskiCarrier) →
      (lambda mu nu : FlatCoordinateIndex) →
      GRStandardLeviCivitaAlgebraLawObligation.sixTermRicciIdentityCancellation
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        base
        lambda
        mu
        nu

    traceEqualsFourWitness :
      (metric : FlatMetricCarrier) →
      GRStandardLeviCivitaAlgebraLawObligation.traceEqualsFourLaw
        canonicalGRFlatConstantStandardLeviCivitaAlgebraLaw
        metric

    noCurvedGRPromotionWitness :
      ML.CarrierQuadraticIsMinkowski.noCurvedGRPromotion
        ML.minkowskiLimitReceipt

    remainingSelectedGRFirstMissing :
      GRDiscreteBianchiFiniteRMissingIngredient

    remainingSelectedGRFirstMissingIsFiniteRScalarAlgebra :
      remainingSelectedGRFirstMissing
      ≡
      missingFiniteRScalarAlgebra

    remainingSelectedGRMissing :
      List GRDiscreteBianchiFiniteRMissingIngredient

    unsupportedSelectedGRClaims :
      List GRDiscreteBianchiFiniteRUnsupportedClaim

    closureBoundary :
      List String

canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure :
  GRFlatMinkowskiFiniteRLeviCivitaClosure
canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure =
  record
    { status =
        flatMinkowskiFiniteRLeviCivitaClosedNoSelectedGRPromotion
    ; minkowskiFlatMetricReceipt =
        ML.minkowskiLimitReceipt
    ; finiteRBaseIsMinkowski =
        refl
    ; metricCarrierIsMinkowskiQuadraticFamily =
        refl
    ; flatConnectionCarrierIsUnit =
        refl
    ; metricAtIsMinkowskiQuadratic =
        λ _ → refl
    ; connectionAtIsTrivial =
        λ _ → refl
    ; carrierMetricCompatibilityWitness =
        λ _ → tt
    ; carrierConnectionIsLeviCivitaWitness =
        λ _ → tt
    ; christoffelTorsionFreeWitness =
        λ _ _ _ _ → refl
    ; flatChristoffelFromMetricRequest =
        canonicalGRFlatConstantChristoffelRequest
    ; flatLeviCivitaDependency =
        canonicalGRFlatConstantLeviCivitaDependency
    ; flatLeviCivitaDependencyIsCanonical =
        refl
    ; standardLawIsCanonical =
        refl
    ; christoffelRequestIsCanonical =
        refl
    ; metricCompatibleCarrierIsCanonical =
        refl
    ; metricCompatibilityLawWitness =
        λ _ _ _ _ → tt
    ; sixTermRicciIdentityCancellationWitness =
        λ _ _ _ _ → tt
    ; traceEqualsFourWitness =
        λ _ → tt
    ; noCurvedGRPromotionWitness =
        ML.minkowskiLimitNoCurvedGRPromotion
    ; remainingSelectedGRFirstMissing =
        missingFiniteRScalarAlgebra
    ; remainingSelectedGRFirstMissingIsFiniteRScalarAlgebra =
        refl
    ; remainingSelectedGRMissing =
        canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; unsupportedSelectedGRClaims =
        canonicalGRDiscreteBianchiFiniteRUnsupportedClaims
    ; closureBoundary =
        "Flat finite-r base is exactly MinkowskiLimitReceipt.MinkowskiCarrier"
        ∷ "Flat metric family is exactly the constant Minkowski quadratic family"
        ∷ "Flat connection carrier is the unit/trivial connection"
        ∷ "Metric compatibility, torsion-free Christoffel symmetry, Christoffel-from-metric, and six-term cancellation are inhabited definitionally on this flat constant surface"
        ∷ "This is the closed flat Levi-Civita carrier only; it does not supply the selected non-flat finite-r GR carrier"
        ∷ []
    }

record GRFlatConstantMetricFiniteRPrerequisiteReceipt : Setω where
  field
    status :
      GRFlatConstantMetricFiniteRPrerequisiteStatus

    minkowskiFlatMetricReceipt :
      ML.CarrierQuadraticIsMinkowski

    flatLeviCivitaDependency :
      GRCarrierConnectionLeviCivitaDependency

    flatLeviCivitaClosure :
      GRFlatMinkowskiFiniteRLeviCivitaClosure

    firstRemainingSelectedGRMissing :
      GRDiscreteBianchiFiniteRMissingIngredient

    firstRemainingIsFiniteRScalarAlgebra :
      firstRemainingSelectedGRMissing
      ≡
      missingFiniteRScalarAlgebra

    remainingSelectedGRRequest :
      List GRDiscreteBianchiFiniteRMissingIngredient

    prerequisiteBoundary :
      List String

canonicalGRFlatConstantMetricFiniteRPrerequisiteReceipt :
  GRFlatConstantMetricFiniteRPrerequisiteReceipt
canonicalGRFlatConstantMetricFiniteRPrerequisiteReceipt =
  record
    { status =
        flatConstantMetricPrerequisiteOnlyNoCurvedGRPromotion
    ; minkowskiFlatMetricReceipt =
        ML.minkowskiLimitReceipt
    ; flatLeviCivitaDependency =
        canonicalGRFlatConstantLeviCivitaDependency
    ; flatLeviCivitaClosure =
        canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure
    ; firstRemainingSelectedGRMissing =
        missingFiniteRScalarAlgebra
    ; firstRemainingIsFiniteRScalarAlgebra =
        refl
    ; remainingSelectedGRRequest =
        canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; prerequisiteBoundary =
        "Flat constant metric finite-r base is now typed as a prerequisite surface"
        ∷ "Flat constant Minkowski finite-r Levi-Civita closure is inhabited definitionally on its own flat carrier"
        ∷ "The selected GR finite-r carrier still requires scalar algebra, inverse metric, coordinate derivative, finite contraction, Christoffel-from-metric law, and six-term Ricci cancellation"
        ∷ "The existing flat Minkowski receipt remains flat-space-only and does not close the non-flat Levi-Civita/Bianchi/Ricci chain"
        ∷ []
    }

data GRSelectedNonFlatFiniteRScalarAlgebraRequestStatus : Set where
  selectedNonFlatFiniteRScalarAlgebraRequestedNoClosure :
    GRSelectedNonFlatFiniteRScalarAlgebraRequestStatus

record GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest : Setω where
  field
    status :
      GRSelectedNonFlatFiniteRScalarAlgebraRequestStatus

    scalarOperationsSurface :
      NFScalar.GRCarrierScalarOperations

    scalarOperationsSurfaceIsCanonicalFiniteR :
      scalarOperationsSurface
      ≡
      NFScalar.canonicalGRFiniteRCarrierScalarOperations

    scalarAlgebra :
      String

    metric :
      String

    inverseMetric :
      String

    inverseLaw :
      String

    coordinateDerivative :
      String

    finiteContraction :
      String

    christoffelLaw :
      String

    trace :
      String

    sixTermCancellation :
      String

    traceEqualsFourLaw :
      String

    scalarAlgebraMissingMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    scalarAlgebraMissingMarkerIsFiniteRScalarAlgebra :
      scalarAlgebraMissingMarker
      ≡
      missingFiniteRScalarAlgebra

    finiteContractionMissingMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    finiteContractionMissingMarkerIsMetricContractionForRicci :
      finiteContractionMissingMarker
      ≡
      missingMetricContractionForRicci

    sixTermCancellationMissingMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    sixTermCancellationMissingMarkerIsSixTermRicciIdentityCancellation :
      sixTermCancellationMissingMarker
      ≡
      missingSixTermRicciIdentityCancellation

    traceEqualsFourMissingMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    traceEqualsFourMissingMarkerIsTraceEqualsFourVacuumReduction :
      traceEqualsFourMissingMarker
      ≡
      missingTraceEqualsFourVacuumReduction

    flatPrerequisite :
      GRFlatConstantMetricFiniteRPrerequisiteReceipt

    typedNonFlatScalarAlgebraSurface :
      NFScalar.GRSelectedNonFlatScalarAlgebraObligationReceipt

    typedNonFlatConditionalDependencySurface :
      NFScalar.GRSelectedNonFlatConditionalDependencySurface

    typedNonFlatScalarAlgebraFirstMissing :
      NFScalar.GRSelectedNonFlatScalarAlgebraObligationReceipt.firstMissingInterface
        typedNonFlatScalarAlgebraSurface
      ≡
      "GRSelectedNonFlatMetricDependency for canonicalGRFiniteRCarrierScalarOperations"

    flatPrerequisiteLeavesScalarAlgebraFirst :
      GRFlatConstantMetricFiniteRPrerequisiteReceipt.firstRemainingSelectedGRMissing
        flatPrerequisite
      ≡
      missingFiniteRScalarAlgebra

    unsupportedClosureClaims :
      List GRDiscreteBianchiFiniteRUnsupportedClaim

    requestBoundary :
      List String

selectedNonFlatFiniteRScalarAlgebraRequestNames :
  GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest →
  List String
selectedNonFlatFiniteRScalarAlgebraRequestNames request =
  GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.scalarAlgebra request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.metric request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.inverseMetric request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.inverseLaw request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.coordinateDerivative request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.finiteContraction request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.christoffelLaw request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.trace request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.sixTermCancellation request
  ∷ GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.traceEqualsFourLaw request
  ∷ []

canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest :
  GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest =
  record
    { status =
        selectedNonFlatFiniteRScalarAlgebraRequestedNoClosure
    ; scalarOperationsSurface =
        NFScalar.canonicalGRFiniteRCarrierScalarOperations
    ; scalarOperationsSurfaceIsCanonicalFiniteR =
        refl
    ; scalarAlgebra =
        "selected non-flat finite-r scalar algebra"
    ; metric =
        "selected non-flat finite-r metric"
    ; inverseMetric =
        "selected non-flat finite-r inverse metric"
    ; inverseLaw =
        "selected non-flat finite-r inverse metric contraction law"
    ; coordinateDerivative =
        "selected non-flat finite-r coordinate derivative"
    ; finiteContraction =
        "selected non-flat finite-r finite contraction"
    ; christoffelLaw =
        "selected non-flat finite-r Christoffel-from-metric law"
    ; trace =
        "selected non-flat finite-r metric trace"
    ; sixTermCancellation =
        "selected non-flat finite-r six-term Ricci identity cancellation"
    ; traceEqualsFourLaw =
        "selected non-flat finite-r trace=4 law"
    ; scalarAlgebraMissingMarker =
        missingFiniteRScalarAlgebra
    ; scalarAlgebraMissingMarkerIsFiniteRScalarAlgebra =
        refl
    ; finiteContractionMissingMarker =
        missingMetricContractionForRicci
    ; finiteContractionMissingMarkerIsMetricContractionForRicci =
        refl
    ; sixTermCancellationMissingMarker =
        missingSixTermRicciIdentityCancellation
    ; sixTermCancellationMissingMarkerIsSixTermRicciIdentityCancellation =
        refl
    ; traceEqualsFourMissingMarker =
        missingTraceEqualsFourVacuumReduction
    ; traceEqualsFourMissingMarkerIsTraceEqualsFourVacuumReduction =
        refl
    ; flatPrerequisite =
        canonicalGRFlatConstantMetricFiniteRPrerequisiteReceipt
    ; typedNonFlatScalarAlgebraSurface =
        NFScalar.canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
    ; typedNonFlatConditionalDependencySurface =
        NFScalar.canonicalGRSelectedNonFlatConditionalDependencySurface
    ; typedNonFlatScalarAlgebraFirstMissing =
        refl
    ; flatPrerequisiteLeavesScalarAlgebraFirst =
        refl
    ; unsupportedClosureClaims =
        canonicalGRDiscreteBianchiFiniteRUnsupportedClaims
    ; requestBoundary =
        "This records the selected non-flat finite-r scalar-algebra dependency request after the flat Minkowski prerequisite"
        ∷ "The request names scalar algebra, metric, inverse metric, inverse law, coordinate derivative, finite contraction, Christoffel law, trace, six-term cancellation, and trace=4 law as separate fields"
        ∷ "The typed non-flat scalar algebra surface is GRNonFlatScalarAlgebraSurface.GRCarrierScalarOperations plus GRSelectedNonFlatMetricDependency, GRSelectedNonFlatMetricAlgebraLaws, and GRSelectedNonFlatConditionalDependencySurface"
        ∷ "The first typed missing interface is the CarrierScalar inhabitant for the selected non-flat finite-r carrier"
        ∷ "It does not instantiate the non-flat Levi-Civita carrier, Ricci contraction, Bianchi bridge, Einstein tensor law, or sourced Einstein equation"
        ∷ []
    }

canonicalGRSelectedNonFlatFiniteRScalarAlgebraRequestNames :
  selectedNonFlatFiniteRScalarAlgebraRequestNames
    canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
  ≡
  "selected non-flat finite-r scalar algebra"
  ∷ "selected non-flat finite-r metric"
  ∷ "selected non-flat finite-r inverse metric"
  ∷ "selected non-flat finite-r inverse metric contraction law"
  ∷ "selected non-flat finite-r coordinate derivative"
  ∷ "selected non-flat finite-r finite contraction"
  ∷ "selected non-flat finite-r Christoffel-from-metric law"
  ∷ "selected non-flat finite-r metric trace"
  ∷ "selected non-flat finite-r six-term Ricci identity cancellation"
  ∷ "selected non-flat finite-r trace=4 law"
  ∷ []
canonicalGRSelectedNonFlatFiniteRScalarAlgebraRequestNames = refl

record GRFiniteRScalarAlgebraHandoffReceipt : Setω where
  field
    priorDependencyRequest :
      GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest

    priorFirstMissingIsFiniteRScalarAlgebra :
      GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.scalarAlgebraMissingMarker
        priorDependencyRequest
      ≡
      missingFiniteRScalarAlgebra

    scalarOperationsSurface :
      NFScalar.GRCarrierScalarOperations

    scalarOperationsSurfaceIsCanonicalFiniteR :
      scalarOperationsSurface
      ≡
      NFScalar.canonicalGRFiniteRCarrierScalarOperations

    concreteFiniteRScalarAlgebraAndCarrierWitness :
      NFScalar.GRConcreteFiniteRScalarAlgebraAndCarrierWitness

    concreteFiniteRScalarAlgebraAndCarrierWitnessIsCanonical :
      concreteFiniteRScalarAlgebraAndCarrierWitness
      ≡
      NFScalar.canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness

    concreteFiniteRFourChartCarrierStaged :
      Bool

    concreteFiniteRFourChartCarrierStagedIsTrue :
      concreteFiniteRFourChartCarrierStaged ≡ true

    concreteFiniteRNeighbourCellStaged :
      Bool

    concreteFiniteRNeighbourCellStagedIsTrue :
      concreteFiniteRNeighbourCellStaged ≡ true

    concreteFiniteRDerivationBracketJacobiStaged :
      Bool

    concreteFiniteRDerivationBracketJacobiStagedIsTrue :
      concreteFiniteRDerivationBracketJacobiStaged ≡ true

    concreteFiniteRConnectionShiftStaged :
      Bool

    concreteFiniteRConnectionShiftStagedIsTrue :
      concreteFiniteRConnectionShiftStaged ≡ true

    concreteFiniteRRealContractionStaged :
      Bool

    concreteFiniteRRealContractionStagedIsTrue :
      concreteFiniteRRealContractionStaged ≡ true

    carrierScalarOperationsAvailable :
      Bool

    carrierScalarOperationsAvailableIsTrue :
      carrierScalarOperationsAvailable ≡ true

    selectedFiniteRScalarAlgebraDischarged :
      Bool

    selectedFiniteRScalarAlgebraDischargedIsFalse :
      selectedFiniteRScalarAlgebraDischarged ≡ false

    selectedFiniteRScalarAlgebraDischargeBlocker :
      String

    exactAbsentSelectedGRFields :
      List String

    firstUnresolvedFiniteRIngredient :
      GRDiscreteBianchiFiniteRMissingIngredient

    firstUnresolvedFiniteRIngredientIsFiniteRScalarAlgebra :
      firstUnresolvedFiniteRIngredient
      ≡
      missingFiniteRScalarAlgebra

    baseHandoffMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    baseHandoffMarkerIsBaseCarrier :
      baseHandoffMarker
      ≡
      missingFiniteRBaseCarrier

    neighbourhoodHandoffBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    neighbourhoodHandoffBlockerIsNeighbourhoodOrCellComplex :
      neighbourhoodHandoffBlocker
      ≡
      missingFiniteRNeighbourhoodOrCellComplex

    derivationHandoffBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    derivationHandoffBlockerIsDerivationCarrier :
      derivationHandoffBlocker
      ≡
      missingFiniteRDerivationCarrier

    bracketHandoffBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    bracketHandoffBlockerIsCarrierLieBracket :
      bracketHandoffBlocker
      ≡
      missingFiniteRCarrierLieBracket

    jacobiHandoffBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    jacobiHandoffBlockerIsJacobiWitness :
      jacobiHandoffBlocker
      ≡
      missingFiniteRJacobiWitness

    connectionHandoffBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    connectionHandoffBlockerIsConnectionOrShiftLaw :
      connectionHandoffBlocker
      ≡
      missingFiniteRConnectionOrShiftLaw

    nonFlatMetricDependencySupplied :
      Bool

    nonFlatMetricDependencySuppliedIsFalse :
      nonFlatMetricDependencySupplied ≡ false

    carrierConnectionIsLeviCivitaSupplied :
      Bool

    carrierConnectionIsLeviCivitaSuppliedIsFalse :
      carrierConnectionIsLeviCivitaSupplied ≡ false

    handoffBoundary :
      List String

open GRFiniteRScalarAlgebraHandoffReceipt public

canonicalGRFiniteRScalarAlgebraHandoffReceipt :
  GRFiniteRScalarAlgebraHandoffReceipt
canonicalGRFiniteRScalarAlgebraHandoffReceipt =
  record
    { priorDependencyRequest =
        canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; priorFirstMissingIsFiniteRScalarAlgebra =
        refl
    ; scalarOperationsSurface =
        NFScalar.canonicalGRFiniteRCarrierScalarOperations
    ; scalarOperationsSurfaceIsCanonicalFiniteR =
        refl
    ; concreteFiniteRScalarAlgebraAndCarrierWitness =
        NFScalar.canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
    ; concreteFiniteRScalarAlgebraAndCarrierWitnessIsCanonical =
        refl
    ; concreteFiniteRFourChartCarrierStaged =
        true
    ; concreteFiniteRFourChartCarrierStagedIsTrue =
        refl
    ; concreteFiniteRNeighbourCellStaged =
        true
    ; concreteFiniteRNeighbourCellStagedIsTrue =
        refl
    ; concreteFiniteRDerivationBracketJacobiStaged =
        true
    ; concreteFiniteRDerivationBracketJacobiStagedIsTrue =
        refl
    ; concreteFiniteRConnectionShiftStaged =
        true
    ; concreteFiniteRConnectionShiftStagedIsTrue =
        refl
    ; concreteFiniteRRealContractionStaged =
        true
    ; concreteFiniteRRealContractionStagedIsTrue =
        refl
    ; carrierScalarOperationsAvailable =
        true
    ; carrierScalarOperationsAvailableIsTrue =
        refl
    ; selectedFiniteRScalarAlgebraDischarged =
        false
    ; selectedFiniteRScalarAlgebraDischargedIsFalse =
        refl
    ; selectedFiniteRScalarAlgebraDischargeBlocker =
        "The local four-chart carrier does not inhabit GRSelectedNonFlatMetricDependency and does not provide the total scalar operations needed by the selected non-flat Christoffel/finite-contraction laws"
    ; exactAbsentSelectedGRFields =
        "GRSelectedNonFlatMetricDependency.metricAt"
        ∷ "GRSelectedNonFlatMetricDependency.metricComponent"
        ∷ "GRSelectedNonFlatMetricDependency.inverseMetricComponent"
        ∷ "GRSelectedNonFlatMetricDependency.coordinateDerivativeOfMetric"
        ∷ "GRSelectedNonFlatMetricDependency.finiteContract"
        ∷ "GRSelectedNonFlatMetricDependency.christoffelSymbol"
        ∷ "GRSelectedNonFlatMetricDependency.covariantDerivativeOfMetric"
        ∷ "GRSelectedNonFlatMetricDependency.metricContractionForRicci"
        ∷ "GRSelectedNonFlatMetricDependency.traceOfMetric"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.inverseMetricLeftLaw"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.inverseMetricRightLaw"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.christoffelFromMetricLaw"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.metricCompatibilityExpansion"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.sixTermRicciCancellationLaw"
        ∷ "GRSelectedNonFlatMetricAlgebraLaws.traceEqualsFourLaw"
        ∷ "DASHI.Combinatorics.String.LieAlgebra inhabitant compatible with the staged finite derivation bracket"
        ∷ []
    ; firstUnresolvedFiniteRIngredient =
        missingFiniteRScalarAlgebra
    ; firstUnresolvedFiniteRIngredientIsFiniteRScalarAlgebra =
        refl
    ; baseHandoffMarker =
        missingFiniteRBaseCarrier
    ; baseHandoffMarkerIsBaseCarrier =
        refl
    ; neighbourhoodHandoffBlocker =
        missingFiniteRNeighbourhoodOrCellComplex
    ; neighbourhoodHandoffBlockerIsNeighbourhoodOrCellComplex =
        refl
    ; derivationHandoffBlocker =
        missingFiniteRDerivationCarrier
    ; derivationHandoffBlockerIsDerivationCarrier =
        refl
    ; bracketHandoffBlocker =
        missingFiniteRCarrierLieBracket
    ; bracketHandoffBlockerIsCarrierLieBracket =
        refl
    ; jacobiHandoffBlocker =
        missingFiniteRJacobiWitness
    ; jacobiHandoffBlockerIsJacobiWitness =
        refl
    ; connectionHandoffBlocker =
        missingFiniteRConnectionOrShiftLaw
    ; connectionHandoffBlockerIsConnectionOrShiftLaw =
        refl
    ; nonFlatMetricDependencySupplied =
        false
    ; nonFlatMetricDependencySuppliedIsFalse =
        refl
    ; carrierConnectionIsLeviCivitaSupplied =
        false
    ; carrierConnectionIsLeviCivitaSuppliedIsFalse =
        refl
    ; handoffBoundary =
        "The finite four-residue carrier scalar operations surface is available as the bounded m3 scalar handoff"
        ∷ "A concrete four-chart carrier, cyclic neighbourhood/cell layer, derivation carrier, bracket/Jacobi equality, connection shift, and finite real-contraction operation are now staged in GRNonFlatScalarAlgebraSurface"
        ∷ "The selected non-flat finite-r scalar algebra is not discharged: the first true blocker remains missingFiniteRScalarAlgebra"
        ∷ "The staged local bracket is not accepted as DASHI.Combinatorics.String.LieAlgebra because that interface's antisym field blocks ordinary finite brackets at x = y"
        ∷ "The staged handoff queue still names base, neighbourhood/cell, derivation, bracket, Jacobi, and connection as selected-GR blockers until they are bound through the non-flat metric dependency and Bianchi bridge interfaces"
        ∷ "No selected non-flat metric dependency, derivation carrier, connection, Levi-Civita witness, Bianchi bridge, Ricci contraction, or sourced Einstein law is supplied here"
        ∷ []
    }

grFiniteRScalarAlgebraHandoffFirstBlocker :
  firstUnresolvedFiniteRIngredient canonicalGRFiniteRScalarAlgebraHandoffReceipt
  ≡
  missingFiniteRScalarAlgebra
grFiniteRScalarAlgebraHandoffFirstBlocker =
  refl

grFiniteRScalarAlgebraHandoffDerivationBlocker :
  derivationHandoffBlocker canonicalGRFiniteRScalarAlgebraHandoffReceipt
  ≡
  missingFiniteRDerivationCarrier
grFiniteRScalarAlgebraHandoffDerivationBlocker =
  refl

grFiniteRScalarAlgebraHandoffConnectionBlocker :
  connectionHandoffBlocker canonicalGRFiniteRScalarAlgebraHandoffReceipt
  ≡
  missingFiniteRConnectionOrShiftLaw
grFiniteRScalarAlgebraHandoffConnectionBlocker =
  refl

grFiniteRScalarAlgebraHandoffLocalStagingExists :
  concreteFiniteRDerivationBracketJacobiStaged
    canonicalGRFiniteRScalarAlgebraHandoffReceipt
  ≡
  true
grFiniteRScalarAlgebraHandoffLocalStagingExists =
  refl

data GRFiniteRFirstSevenIngredientProgressStatus : Set where
  firstSevenFiniteRIngredientsInhabitedNoGRPromotion :
    GRFiniteRFirstSevenIngredientProgressStatus

record GRFiniteRFirstSevenIngredientProgressReceipt : Setω where
  field
    status :
      GRFiniteRFirstSevenIngredientProgressStatus

    concreteCarrierWitness :
      NFScalar.GRConcreteFiniteRScalarAlgebraAndCarrierWitness

    concreteCarrierWitnessIsCanonical :
      concreteCarrierWitness
      ≡
      NFScalar.canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness

    finiteRScalarAlgebra :
      NFScalar.GRCarrierScalarOperations

    finiteRScalarAlgebraIsCanonical :
      finiteRScalarAlgebra
      ≡
      NFScalar.canonicalGRFiniteRCarrierScalarOperations

    finiteRRealContractionOperation :
      NFScalar.GRFiniteRScalar →
      NFScalar.GRFiniteRScalar

    finiteRRealContractionOperationIsCanonical :
      finiteRRealContractionOperation
      ≡
      NFScalar.grFiniteRScalarRealContraction

    finiteRRealContractionFixedZero :
      finiteRRealContractionOperation NFScalar.r0
      ≡
      NFScalar.r0

    finiteRBaseCarrier :
      Set

    finiteRBaseCarrierIsFourChart :
      finiteRBaseCarrier
      ≡
      NFScalar.GRFiniteRChartPoint

    finiteRBaseFourChartCycle :
      List NFScalar.GRFiniteRChartPoint

    finiteRBaseFourChartCycleIsCanonical :
      finiteRBaseFourChartCycle
      ≡
      NFScalar.chart0 ∷ NFScalar.chart1 ∷ NFScalar.chart2 ∷ NFScalar.chart3 ∷ []

    finiteRNeighbourhood :
      NFScalar.GRFiniteRChartPoint →
      NFScalar.GRFiniteRChartPoint →
      Set

    finiteRNeighbourhoodIsCyclic :
      finiteRNeighbourhood
      ≡
      NFScalar.GRFiniteRNeighbour

    finiteRCellComplex :
      Set

    finiteRCellComplexIsCyclicFourChartCell :
      finiteRCellComplex
      ≡
      NFScalar.GRFiniteRCellComplex

    finiteRDerivationCarrier :
      Set

    finiteRDerivationCarrierIsConcrete :
      finiteRDerivationCarrier
      ≡
      NFScalar.GRFiniteRDerivationCarrier

    finiteRCarrierLieBracket :
      NFScalar.GRFiniteRDerivationCarrier →
      NFScalar.GRFiniteRDerivationCarrier →
      NFScalar.GRFiniteRDerivationCarrier

    finiteRCarrierLieBracketIsConcrete :
      finiteRCarrierLieBracket
      ≡
      NFScalar.grFiniteRDerivationBracket

    finiteRJacobiWitness :
      (x y z : NFScalar.GRFiniteRDerivationCarrier) →
      finiteRCarrierLieBracket x (finiteRCarrierLieBracket y z)
      ≡
      finiteRCarrierLieBracket (finiteRCarrierLieBracket x y) z

    finiteRConnectionCarrier :
      Set

    finiteRConnectionCarrierIsConcrete :
      finiteRConnectionCarrier
      ≡
      NFScalar.GRFiniteRConnectionCarrier

    finiteRConnectionOrShiftLaw :
      NFScalar.GRFiniteRConnectionCarrier →
      NFScalar.GRFiniteRDerivationCarrier →
      NFScalar.GRFiniteRChartPoint →
      NFScalar.GRFiniteRChartPoint

    finiteRConnectionOrShiftLawIsConcrete :
      finiteRConnectionOrShiftLaw
      ≡
      NFScalar.grFiniteRConnectionShift

    finiteRConnectionForwardShiftNontrivial :
      finiteRConnectionOrShiftLaw
        NFScalar.finiteRCyclicShiftConnection
        NFScalar.derivationForward
        NFScalar.chart0
      ≡
      NFScalar.chart1

    scalarAlgebraMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    scalarAlgebraMarkerIsFiniteRScalarAlgebra :
      scalarAlgebraMarker
      ≡
      missingFiniteRScalarAlgebra

    baseCarrierMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    baseCarrierMarkerIsFiniteRBaseCarrier :
      baseCarrierMarker
      ≡
      missingFiniteRBaseCarrier

    neighbourhoodMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    neighbourhoodMarkerIsFiniteRNeighbourhoodOrCellComplex :
      neighbourhoodMarker
      ≡
      missingFiniteRNeighbourhoodOrCellComplex

    derivationCarrierMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    derivationCarrierMarkerIsFiniteRDerivationCarrier :
      derivationCarrierMarker
      ≡
      missingFiniteRDerivationCarrier

    carrierLieBracketMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    carrierLieBracketMarkerIsFiniteRCarrierLieBracket :
      carrierLieBracketMarker
      ≡
      missingFiniteRCarrierLieBracket

    jacobiWitnessMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    jacobiWitnessMarkerIsFiniteRJacobiWitness :
      jacobiWitnessMarker
      ≡
      missingFiniteRJacobiWitness

    connectionOrShiftLawMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    connectionOrShiftLawMarkerIsFiniteRConnectionOrShiftLaw :
      connectionOrShiftLawMarker
      ≡
      missingFiniteRConnectionOrShiftLaw

    firstSevenIngredientsAdvanced :
      Bool

    firstSevenIngredientsAdvancedIsTrue :
      firstSevenIngredientsAdvanced ≡ true

    postFirstSevenResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    postFirstSevenResidualBlockerIsMetricCompatibility :
      postFirstSevenResidualBlocker
      ≡
      missingMetricCompatibility

    noLeviCivitaOrEinsteinPromotion :
      Bool

    noLeviCivitaOrEinsteinPromotionIsTrue :
      noLeviCivitaOrEinsteinPromotion ≡ true

    progressBoundary :
      List String

canonicalGRFiniteRFirstSevenIngredientProgressReceipt :
  GRFiniteRFirstSevenIngredientProgressReceipt
canonicalGRFiniteRFirstSevenIngredientProgressReceipt =
  record
    { status =
        firstSevenFiniteRIngredientsInhabitedNoGRPromotion
    ; concreteCarrierWitness =
        NFScalar.canonicalGRConcreteFiniteRScalarAlgebraAndCarrierWitness
    ; concreteCarrierWitnessIsCanonical =
        refl
    ; finiteRScalarAlgebra =
        NFScalar.canonicalGRFiniteRCarrierScalarOperations
    ; finiteRScalarAlgebraIsCanonical =
        refl
    ; finiteRRealContractionOperation =
        NFScalar.grFiniteRScalarRealContraction
    ; finiteRRealContractionOperationIsCanonical =
        refl
    ; finiteRRealContractionFixedZero =
        refl
    ; finiteRBaseCarrier =
        NFScalar.GRFiniteRChartPoint
    ; finiteRBaseCarrierIsFourChart =
        refl
    ; finiteRBaseFourChartCycle =
        NFScalar.grFiniteRAllCharts
    ; finiteRBaseFourChartCycleIsCanonical =
        refl
    ; finiteRNeighbourhood =
        NFScalar.GRFiniteRNeighbour
    ; finiteRNeighbourhoodIsCyclic =
        refl
    ; finiteRCellComplex =
        NFScalar.GRFiniteRCellComplex
    ; finiteRCellComplexIsCyclicFourChartCell =
        refl
    ; finiteRDerivationCarrier =
        NFScalar.GRFiniteRDerivationCarrier
    ; finiteRDerivationCarrierIsConcrete =
        refl
    ; finiteRCarrierLieBracket =
        NFScalar.grFiniteRDerivationBracket
    ; finiteRCarrierLieBracketIsConcrete =
        refl
    ; finiteRJacobiWitness =
        NFScalar.grFiniteRDerivationJacobiWitness
    ; finiteRConnectionCarrier =
        NFScalar.GRFiniteRConnectionCarrier
    ; finiteRConnectionCarrierIsConcrete =
        refl
    ; finiteRConnectionOrShiftLaw =
        NFScalar.grFiniteRConnectionShift
    ; finiteRConnectionOrShiftLawIsConcrete =
        refl
    ; finiteRConnectionForwardShiftNontrivial =
        refl
    ; scalarAlgebraMarker =
        missingFiniteRScalarAlgebra
    ; scalarAlgebraMarkerIsFiniteRScalarAlgebra =
        refl
    ; baseCarrierMarker =
        missingFiniteRBaseCarrier
    ; baseCarrierMarkerIsFiniteRBaseCarrier =
        refl
    ; neighbourhoodMarker =
        missingFiniteRNeighbourhoodOrCellComplex
    ; neighbourhoodMarkerIsFiniteRNeighbourhoodOrCellComplex =
        refl
    ; derivationCarrierMarker =
        missingFiniteRDerivationCarrier
    ; derivationCarrierMarkerIsFiniteRDerivationCarrier =
        refl
    ; carrierLieBracketMarker =
        missingFiniteRCarrierLieBracket
    ; carrierLieBracketMarkerIsFiniteRCarrierLieBracket =
        refl
    ; jacobiWitnessMarker =
        missingFiniteRJacobiWitness
    ; jacobiWitnessMarkerIsFiniteRJacobiWitness =
        refl
    ; connectionOrShiftLawMarker =
        missingFiniteRConnectionOrShiftLaw
    ; connectionOrShiftLawMarkerIsFiniteRConnectionOrShiftLaw =
        refl
    ; firstSevenIngredientsAdvanced =
        true
    ; firstSevenIngredientsAdvancedIsTrue =
        refl
    ; postFirstSevenResidualBlocker =
        missingMetricCompatibility
    ; postFirstSevenResidualBlockerIsMetricCompatibility =
        refl
    ; noLeviCivitaOrEinsteinPromotion =
        true
    ; noLeviCivitaOrEinsteinPromotionIsTrue =
        refl
    ; progressBoundary =
        "The first seven finite-r ingredients are inhabited by the four-chart scalar/carrier witness from GRNonFlatScalarAlgebraSurface"
        ∷ "missingFiniteRScalarAlgebra is advanced by canonicalGRFiniteRCarrierScalarOperations over r0,r1,r2,r3"
        ∷ "The same local scalar carrier stages grFiniteRScalarRealContraction with fixed r0, without asserting an ordered real Lipschitz theorem"
        ∷ "missingFiniteRBaseCarrier is advanced by GRFiniteRChartPoint with chart0, chart1, chart2, chart3"
        ∷ "missingFiniteRNeighbourhoodOrCellComplex is advanced by the bidirectional cyclic edge relation plus cyclicFourChartCell"
        ∷ "missingFiniteRDerivationCarrier is advanced by stay/forward/backward/opposite finite-difference directions"
        ∷ "missingFiniteRCarrierLieBracket and missingFiniteRJacobiWitness are advanced by the selected finite derivation bracket and definitional Jacobi witness"
        ∷ "missingFiniteRConnectionOrShiftLaw is advanced by finiteRCyclicShiftConnection and the concrete shift law"
        ∷ "The next residual blocker after this local algebra layer is metricCompatibility, not a Levi-Civita/Bianchi/Ricci/Einstein promotion"
        ∷ []
    }

grFiniteRFirstSevenProgressNextResidual :
  GRFiniteRFirstSevenIngredientProgressReceipt.postFirstSevenResidualBlocker
    canonicalGRFiniteRFirstSevenIngredientProgressReceipt
  ≡
  missingMetricCompatibility
grFiniteRFirstSevenProgressNextResidual = refl

data GRFiniteRMetricCompatibilityProgressStatus : Set where
  finiteRMetricCompatibilityInhabitedNoLeviCivitaPromotion :
    GRFiniteRMetricCompatibilityProgressStatus

record GRFiniteRMetricCompatibilityProgressReceipt : Setω where
  field
    status :
      GRFiniteRMetricCompatibilityProgressStatus

    firstSevenIngredientProgress :
      GRFiniteRFirstSevenIngredientProgressReceipt

    firstSevenNextResidualWasMetricCompatibility :
      GRFiniteRFirstSevenIngredientProgressReceipt.postFirstSevenResidualBlocker
        firstSevenIngredientProgress
      ≡
      missingMetricCompatibility

    unitMetricAlgebraStaging :
      NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt

    selectedMetricDependency :
      NFScalar.GRSelectedNonFlatMetricDependency
        NFScalar.canonicalGRFiniteRCarrierScalarOperations

    selectedMetricAlgebraLaws :
      NFScalar.GRSelectedNonFlatMetricAlgebraLaws
        NFScalar.canonicalGRFiniteRCarrierScalarOperations
        selectedMetricDependency

    metricCompatibilityExpansionStaged :
      Bool

    metricCompatibilityExpansionStagedIsTrue :
      metricCompatibilityExpansionStaged
      ≡
      true

    sixTermRicciCancellationStaged :
      Bool

    sixTermRicciCancellationStagedIsTrue :
      sixTermRicciCancellationStaged
      ≡
      true

    metricCompatibilityMarkerDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    metricCompatibilityMarkerDischargedIsMetricCompatibility :
      metricCompatibilityMarkerDischarged
      ≡
      missingMetricCompatibility

    postMetricCompatibilityResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    postMetricCompatibilityResidualBlockerIsCarrierConnectionIsLeviCivita :
      postMetricCompatibilityResidualBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    noSelectedNonFlatLeviCivitaPromotion :
      NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesNonFlatLeviCivita
        unitMetricAlgebraStaging
      ≡
      false

    noGRPromotion :
      NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesGR
        unitMetricAlgebraStaging
      ≡
      false

    progressBoundary :
      List String

canonicalGRFiniteRMetricCompatibilityProgressReceipt :
  GRFiniteRMetricCompatibilityProgressReceipt
canonicalGRFiniteRMetricCompatibilityProgressReceipt =
  record
    { status =
        finiteRMetricCompatibilityInhabitedNoLeviCivitaPromotion
    ; firstSevenIngredientProgress =
        canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; firstSevenNextResidualWasMetricCompatibility =
        refl
    ; unitMetricAlgebraStaging =
        NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; selectedMetricDependency =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.metricDependency
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; selectedMetricAlgebraLaws =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.metricAlgebraLaws
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; metricCompatibilityExpansionStaged =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.metricCompatibilityExpansionStaged
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; metricCompatibilityExpansionStagedIsTrue =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.metricCompatibilityExpansionStagedIsTrue
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; sixTermRicciCancellationStaged =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.sixTermCancellationStaged
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; sixTermRicciCancellationStagedIsTrue =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.sixTermCancellationStagedIsTrue
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; metricCompatibilityMarkerDischarged =
        missingMetricCompatibility
    ; metricCompatibilityMarkerDischargedIsMetricCompatibility =
        refl
    ; postMetricCompatibilityResidualBlocker =
        missingCarrierConnectionIsLeviCivita
    ; postMetricCompatibilityResidualBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; noSelectedNonFlatLeviCivitaPromotion =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesNonFlatLeviCivitaIsFalse
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; noGRPromotion =
        NFScalar.GRConcreteFiniteRUnitMetricAlgebraStagingReceipt.promotesGRIsFalse
          NFScalar.canonicalGRConcreteFiniteRUnitMetricAlgebraStagingReceipt
    ; progressBoundary =
        "The first seven finite-r ingredients are consumed from canonicalGRFiniteRFirstSevenIngredientProgressReceipt"
        ∷ "The selected four-chart unit metric staging from GRNonFlatScalarAlgebraSurface supplies GRSelectedNonFlatMetricDependency and GRSelectedNonFlatMetricAlgebraLaws"
        ∷ "metricCompatibilityExpansionStaged and sixTermCancellationStaged are true for the bounded identity metric and zero Christoffel table"
        ∷ "This discharges the local missingMetricCompatibility marker and advances the local residual blocker to missingCarrierConnectionIsLeviCivita"
        ∷ "No selected non-flat Levi-Civita, curvature-as-bracket-defect, Bianchi bridge, Ricci contraction, Einstein tensor, or sourced Einstein law is promoted"
        ∷ []
    }

grFiniteRMetricCompatibilityProgressNextResidual :
  GRFiniteRMetricCompatibilityProgressReceipt.postMetricCompatibilityResidualBlocker
    canonicalGRFiniteRMetricCompatibilityProgressReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grFiniteRMetricCompatibilityProgressNextResidual = refl

data GRFiniteRLeviCivitaBianchiEinsteinProgressStatus : Set where
  finiteRLeviCivitaBianchiEinsteinStagedNoSourcedPromotion :
    GRFiniteRLeviCivitaBianchiEinsteinProgressStatus

record GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt : Setω where
  field
    status :
      GRFiniteRLeviCivitaBianchiEinsteinProgressStatus

    metricCompatibilityProgress :
      GRFiniteRMetricCompatibilityProgressReceipt

    postMetricCompatibilityWasCarrierConnectionIsLeviCivita :
      GRFiniteRMetricCompatibilityProgressReceipt.postMetricCompatibilityResidualBlocker
        metricCompatibilityProgress
      ≡
      missingCarrierConnectionIsLeviCivita

    selectedFourChartGeometryStaging :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    carrierConnectionIsLeviCivitaMarkerDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    carrierConnectionIsLeviCivitaMarkerDischargedIsCanonical :
      carrierConnectionIsLeviCivitaMarkerDischarged
      ≡
      missingCarrierConnectionIsLeviCivita

    curvatureAsBracketDefectMarkerDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    curvatureAsBracketDefectMarkerDischargedIsCanonical :
      curvatureAsBracketDefectMarkerDischarged
      ≡
      missingCurvatureAsBracketDefect

    jacobiToBianchiBridgeMarkerDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    jacobiToBianchiBridgeMarkerDischargedIsCanonical :
      jacobiToBianchiBridgeMarkerDischarged
      ≡
      missingJacobiToBianchiBridge

    finiteRBianchiLawMarkerDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    finiteRBianchiLawMarkerDischargedIsCanonical :
      finiteRBianchiLawMarkerDischarged
      ≡
      missingFiniteRBianchiLaw

    ricciScalarEinsteinTensorStaged :
      Bool

    ricciScalarEinsteinTensorStagedIsTrue :
      ricciScalarEinsteinTensorStaged
      ≡
      true

    postGeometryPromotionResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    postGeometryPromotionResidualBlockerIsCurvatureToRicciEinsteinBoundary :
      postGeometryPromotionResidualBlocker
      ≡
      missingCurvatureToRicciEinsteinContractionBoundary

    sourcedEinsteinResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    sourcedEinsteinResidualBlockerIsStressEnergyCompatibility :
      sourcedEinsteinResidualBlocker
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    noSourcedEinsteinPromotion :
      Bool

    noSourcedEinsteinPromotionIsTrue :
      noSourcedEinsteinPromotion
      ≡
      true

    progressBoundary :
      List String

canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt :
  GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt =
  record
    { status =
        finiteRLeviCivitaBianchiEinsteinStagedNoSourcedPromotion
    ; metricCompatibilityProgress =
        canonicalGRFiniteRMetricCompatibilityProgressReceipt
    ; postMetricCompatibilityWasCarrierConnectionIsLeviCivita =
        refl
    ; selectedFourChartGeometryStaging =
        NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; carrierConnectionIsLeviCivitaMarkerDischarged =
        missingCarrierConnectionIsLeviCivita
    ; carrierConnectionIsLeviCivitaMarkerDischargedIsCanonical =
        refl
    ; curvatureAsBracketDefectMarkerDischarged =
        missingCurvatureAsBracketDefect
    ; curvatureAsBracketDefectMarkerDischargedIsCanonical =
        refl
    ; jacobiToBianchiBridgeMarkerDischarged =
        missingJacobiToBianchiBridge
    ; jacobiToBianchiBridgeMarkerDischargedIsCanonical =
        refl
    ; finiteRBianchiLawMarkerDischarged =
        missingFiniteRBianchiLaw
    ; finiteRBianchiLawMarkerDischargedIsCanonical =
        refl
    ; ricciScalarEinsteinTensorStaged =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciScalarEinsteinTensorStaged
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; ricciScalarEinsteinTensorStagedIsTrue =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciScalarEinsteinTensorStagedIsTrue
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; postGeometryPromotionResidualBlocker =
        missingCurvatureToRicciEinsteinContractionBoundary
    ; postGeometryPromotionResidualBlockerIsCurvatureToRicciEinsteinBoundary =
        refl
    ; sourcedEinsteinResidualBlocker =
        missingStressEnergyCompatibilityForContractedBianchi
    ; sourcedEinsteinResidualBlockerIsStressEnergyCompatibility =
        refl
    ; noSourcedEinsteinPromotion =
        true
    ; noSourcedEinsteinPromotionIsTrue =
        refl
    ; progressBoundary =
        "The post-metric local residual missingCarrierConnectionIsLeviCivita is advanced by the selected four-chart Levi-Civita equality from GRNonFlatScalarAlgebraSurface"
        ∷ "Curvature-as-bracket-defect, Jacobi-to-Bianchi, and finite-r Bianchi are staged by zero-table cyclic-sum witnesses on the selected four-chart carrier"
        ∷ "Ricci, scalar curvature, and Einstein tensor components are staged as selected zero tables only"
        ∷ "The remaining promotion blocker is the curvature-to-Ricci/Einstein contraction boundary; sourced Einstein additionally waits on stress-energy compatibility and W4"
        ∷ []
    }

grFiniteRLeviCivitaBianchiEinsteinPostGeometryResidual :
  GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.postGeometryPromotionResidualBlocker
    canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
  ≡
  missingCurvatureToRicciEinsteinContractionBoundary
grFiniteRLeviCivitaBianchiEinsteinPostGeometryResidual =
  refl

grFiniteRLeviCivitaBianchiEinsteinNoSourcedPromotion :
  GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.noSourcedEinsteinPromotion
    canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
  ≡
  true
grFiniteRLeviCivitaBianchiEinsteinNoSourcedPromotion =
  refl

data GRFiniteRCurvatureRicciEinsteinContractionBoundaryStatus : Set where
  finiteRCurvatureRicciEinsteinContractionBoundaryAdvancedNoSourcePromotion :
    GRFiniteRCurvatureRicciEinsteinContractionBoundaryStatus

record GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt : Setω where
  field
    status :
      GRFiniteRCurvatureRicciEinsteinContractionBoundaryStatus

    leviCivitaBianchiProgress :
      GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt

    previousPostGeometryResidualWasContractionBoundary :
      GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt.postGeometryPromotionResidualBlocker
        leviCivitaBianchiProgress
      ≡
      missingCurvatureToRicciEinsteinContractionBoundary

    selectedFourChartGeometryStaging :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    ricciFromCurvatureContraction :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRRicciComponent mu nu
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grSelectedFiniteRCurvatureAction rho mu rho nu)

    scalarCurvatureFromRicciTrace :
      NFScalar.grSelectedFiniteRScalarCurvatureComponent
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              rho
              rho)
            (NFScalar.grSelectedFiniteRRicciComponent rho rho))

    einsteinTensorFromRicciScalar :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteREinsteinTensorComponent mu nu
      ≡
      NFScalar.grFiniteRScalarSub
        (NFScalar.grSelectedFiniteRRicciComponent mu nu)
        (NFScalar.grFiniteRScalarMul
          NFScalar.r2
          (NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              mu
              nu)
            NFScalar.grSelectedFiniteRScalarCurvatureComponent))

    contractedBianchiDivergenceZero :
      (nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRContract
        (λ mu → NFScalar.grSelectedFiniteREinsteinTensorComponent mu nu)
      ≡
      NFScalar.r0

    curvatureToRicciEinsteinBoundaryDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    curvatureToRicciEinsteinBoundaryDischargedIsCanonical :
      curvatureToRicciEinsteinBoundaryDischarged
      ≡
      missingCurvatureToRicciEinsteinContractionBoundary

    metricContractionForRicciDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    metricContractionForRicciDischargedIsCanonical :
      metricContractionForRicciDischarged
      ≡
      missingMetricContractionForRicci

    traceEqualsFourReductionDischarged :
      GRDiscreteBianchiFiniteRMissingIngredient

    traceEqualsFourReductionDischargedIsCanonical :
      traceEqualsFourReductionDischarged
      ≡
      missingTraceEqualsFourVacuumReduction

    stressEnergyConservationSourceStaging :
      FVMetric.FactorVecGate4StressEnergyConservationSourceReceipt

    localStressEnergyBridgeRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localStressEnergyBridgeRemainingBlockerIsMatterInterface :
      localStressEnergyBridgeRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    w4ExternalHalt :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt

    postContractionResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    postContractionResidualBlockerIsStressEnergyCompatibility :
      postContractionResidualBlocker
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        w4ExternalHalt
      ≡
      false

    wave3Boundary :
      List String

canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt :
  GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt =
  record
    { status =
        finiteRCurvatureRicciEinsteinContractionBoundaryAdvancedNoSourcePromotion
    ; leviCivitaBianchiProgress =
        canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; previousPostGeometryResidualWasContractionBoundary =
        refl
    ; selectedFourChartGeometryStaging =
        NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; ricciFromCurvatureContraction =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciFromCurvatureContraction
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; scalarCurvatureFromRicciTrace =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.scalarCurvatureFromRicciTrace
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; einsteinTensorFromRicciScalar =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.einsteinTensorFromRicciScalar
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; contractedBianchiDivergenceZero =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.contractedBianchiDivergenceZero
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; curvatureToRicciEinsteinBoundaryDischarged =
        missingCurvatureToRicciEinsteinContractionBoundary
    ; curvatureToRicciEinsteinBoundaryDischargedIsCanonical =
        refl
    ; metricContractionForRicciDischarged =
        missingMetricContractionForRicci
    ; metricContractionForRicciDischargedIsCanonical =
        refl
    ; traceEqualsFourReductionDischarged =
        missingTraceEqualsFourVacuumReduction
    ; traceEqualsFourReductionDischargedIsCanonical =
        refl
    ; stressEnergyConservationSourceStaging =
        FVMetric.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; localStressEnergyBridgeRemainingBlocker =
        FVMetric.FactorVecGate4StressEnergyConservationSourceReceipt.exactRemainingBlocker
          FVMetric.canonicalFactorVecGate4StressEnergyConservationSourceReceipt
    ; localStressEnergyBridgeRemainingBlockerIsMatterInterface =
        refl
    ; w4ExternalHalt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; postContractionResidualBlocker =
        missingStressEnergyCompatibilityForContractedBianchi
    ; postContractionResidualBlockerIsStressEnergyCompatibility =
        refl
    ; noSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; wave3Boundary =
        "Continuation wave 3 advances the selected zero-table curvature-to-Ricci/Einstein contraction boundary"
        ∷ "Ricci is obtained as the finite contraction of the selected zero curvature table"
        ∷ "Scalar curvature is the inverse-metric trace of the zero Ricci table, and the Einstein tensor obeys the local Ricci-scalar formula"
        ∷ "The selected contracted-Bianchi divergence is zero; source compatibility is staged only through the local FactorVec stress-energy conservation/source receipt"
        ∷ "No W4MatterStressEnergyInterfaceReceipt is consumed and no sourced Einstein equation is promoted"
        ∷ []
    }

grFiniteRCurvatureRicciEinsteinContractionBoundaryWave3Residual :
  GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt.postContractionResidualBlocker
    canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
  ≡
  missingStressEnergyCompatibilityForContractedBianchi
grFiniteRCurvatureRicciEinsteinContractionBoundaryWave3Residual =
  refl

grFiniteRCurvatureRicciEinsteinContractionBoundaryWave3LocalMatterBlocker :
  GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt.localStressEnergyBridgeRemainingBlocker
    canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grFiniteRCurvatureRicciEinsteinContractionBoundaryWave3LocalMatterBlocker =
  refl

data GRFiniteRGate4ConservativeStagingStatus : Set where
  finiteRGate4FourChartStagedBlockersRemainExplicit :
    GRFiniteRGate4ConservativeStagingStatus

canonicalGRFiniteRGate4RemainingBlockers :
  List GRDiscreteBianchiFiniteRMissingIngredient
canonicalGRFiniteRGate4RemainingBlockers =
  missingCarrierConnectionIsLeviCivita
  ∷ missingCurvatureAsBracketDefect
  ∷ missingJacobiToBianchiBridge
  ∷ missingFiniteRBianchiLaw
  ∷ missingCurvatureToRicciEinsteinContractionBoundary
  ∷ missingMetricContractionForRicci
  ∷ missingStressEnergyCompatibilityForContractedBianchi
  ∷ []

record GRFiniteRGate4ConservativeStagingReceipt : Setω where
  field
    status :
      GRFiniteRGate4ConservativeStagingStatus

    firstSevenIngredientProgress :
      GRFiniteRFirstSevenIngredientProgressReceipt

    metricCompatibilityProgress :
      GRFiniteRMetricCompatibilityProgressReceipt

    selectedFourChartMetricCompatibilityReceipt :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt

    selectedFourChartGeometryStaging :
      NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt

    scalarBaseCellDerivationBracketJacobiConnectionStaged :
      Bool

    scalarBaseCellDerivationBracketJacobiConnectionStagedIsTrue :
      scalarBaseCellDerivationBracketJacobiConnectionStaged
      ≡
      true

    localMetricCompatibilityStaged :
      Bool

    localMetricCompatibilityStagedIsTrue :
      localMetricCompatibilityStaged
      ≡
      true

    localZeroTableGeometryStaged :
      Bool

    localZeroTableGeometryStagedIsTrue :
      localZeroTableGeometryStaged
      ≡
      true

    remainingGate4Blockers :
      List GRDiscreteBianchiFiniteRMissingIngredient

    remainingGate4BlockersAreCanonical :
      remainingGate4Blockers
      ≡
      canonicalGRFiniteRGate4RemainingBlockers

    carrierConnectionLeviCivitaBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    carrierConnectionLeviCivitaBlockerIsCanonical :
      carrierConnectionLeviCivitaBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    curvatureAsBracketDefectBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    curvatureAsBracketDefectBlockerIsCanonical :
      curvatureAsBracketDefectBlocker
      ≡
      missingCurvatureAsBracketDefect

    jacobiToBianchiBridgeBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    jacobiToBianchiBridgeBlockerIsCanonical :
      jacobiToBianchiBridgeBlocker
      ≡
      missingJacobiToBianchiBridge

    finiteRBianchiLawBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    finiteRBianchiLawBlockerIsCanonical :
      finiteRBianchiLawBlocker
      ≡
      missingFiniteRBianchiLaw

    ricciContractionBoundaryBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    ricciContractionBoundaryBlockerIsCanonical :
      ricciContractionBoundaryBlocker
      ≡
      missingCurvatureToRicciEinsteinContractionBoundary

    metricContractionForRicciBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    metricContractionForRicciBlockerIsCanonical :
      metricContractionForRicciBlocker
      ≡
      missingMetricContractionForRicci

    stressEnergyCompatibilityBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    stressEnergyCompatibilityBlockerIsCanonical :
      stressEnergyCompatibilityBlocker
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    w4ExternalHalt :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt

    exactW4MatterStressEnergyInterfaceBlocker :
      String

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        w4ExternalHalt
      ≡
      false

    receiptBoundary :
      List String

canonicalGRFiniteRGate4ConservativeStagingReceipt :
  GRFiniteRGate4ConservativeStagingReceipt
canonicalGRFiniteRGate4ConservativeStagingReceipt =
  record
    { status =
        finiteRGate4FourChartStagedBlockersRemainExplicit
    ; firstSevenIngredientProgress =
        canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; metricCompatibilityProgress =
        canonicalGRFiniteRMetricCompatibilityProgressReceipt
    ; selectedFourChartMetricCompatibilityReceipt =
        NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; selectedFourChartGeometryStaging =
        NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; scalarBaseCellDerivationBracketJacobiConnectionStaged =
        true
    ; scalarBaseCellDerivationBracketJacobiConnectionStagedIsTrue =
        refl
    ; localMetricCompatibilityStaged =
        true
    ; localMetricCompatibilityStagedIsTrue =
        refl
    ; localZeroTableGeometryStaged =
        true
    ; localZeroTableGeometryStagedIsTrue =
        refl
    ; remainingGate4Blockers =
        canonicalGRFiniteRGate4RemainingBlockers
    ; remainingGate4BlockersAreCanonical =
        refl
    ; carrierConnectionLeviCivitaBlocker =
        missingCarrierConnectionIsLeviCivita
    ; carrierConnectionLeviCivitaBlockerIsCanonical =
        refl
    ; curvatureAsBracketDefectBlocker =
        missingCurvatureAsBracketDefect
    ; curvatureAsBracketDefectBlockerIsCanonical =
        refl
    ; jacobiToBianchiBridgeBlocker =
        missingJacobiToBianchiBridge
    ; jacobiToBianchiBridgeBlockerIsCanonical =
        refl
    ; finiteRBianchiLawBlocker =
        missingFiniteRBianchiLaw
    ; finiteRBianchiLawBlockerIsCanonical =
        refl
    ; ricciContractionBoundaryBlocker =
        missingCurvatureToRicciEinsteinContractionBoundary
    ; ricciContractionBoundaryBlockerIsCanonical =
        refl
    ; metricContractionForRicciBlocker =
        missingMetricContractionForRicci
    ; metricContractionForRicciBlockerIsCanonical =
        refl
    ; stressEnergyCompatibilityBlocker =
        missingStressEnergyCompatibilityForContractedBianchi
    ; stressEnergyCompatibilityBlockerIsCanonical =
        refl
    ; w4ExternalHalt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; exactW4MatterStressEnergyInterfaceBlocker =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; noSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; receiptBoundary =
        "Gate 4 now has a typed conservative ledger for the selected four-chart finite-r staging already present"
        ∷ "Scalar/base/cell/derivation/bracket/Jacobi/connection and local metric-compatibility staging are recorded as local staging only"
        ∷ "The local zero-table Levi-Civita/Bianchi/Ricci/Einstein equations are not promoted to global non-flat GR closure"
        ∷ "The remaining blockers are kept explicit: carrierConnectionIsLeviCivita, curvature-as-bracket-defect, Jacobi-to-Bianchi, finite-r Bianchi, Ricci contraction, and W4 matter/stress-energy"
        ∷ "No W4MatterStressEnergyInterfaceReceipt, stress-energy source closure, sourced Einstein law, or GR/QFT promotion is constructed"
        ∷ []
    }

grFiniteRGate4ConservativeRemainingBlockersExplicit :
  GRFiniteRGate4ConservativeStagingReceipt.remainingGate4Blockers
    canonicalGRFiniteRGate4ConservativeStagingReceipt
  ≡
  canonicalGRFiniteRGate4RemainingBlockers
grFiniteRGate4ConservativeRemainingBlockersExplicit =
  refl

grFiniteRGate4ConservativeNoSourcedEinsteinPromotion :
  GRFiniteRGate4ConservativeStagingReceipt.noSourcedEinsteinPromotion
    canonicalGRFiniteRGate4ConservativeStagingReceipt
  ≡
  W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
grFiniteRGate4ConservativeNoSourcedEinsteinPromotion =
  refl

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

record GRSelectedFiniteRMetricCompatibilityInspection : Setω where
  field
    selectedMetricSurface :
      SelectedMetric.GRSelectedNonFlatMetricInstanceSurface

    selectedMetricDependency :
      NFScalar.GRSelectedNonFlatMetricDependency
        NFScalar.canonicalGRFiniteRCarrierScalarOperations

    selectedMetricSymmetry :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedMetricComponent
        (SelectedMetric.selectedMetricAt base)
        mu
        nu
      ≡
      SelectedMetric.selectedMetricComponent
        (SelectedMetric.selectedMetricAt base)
        nu
        mu

    selectedInverseMetricLeft :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedFiniteContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (SelectedMetric.selectedInverseMetricComponent
              (SelectedMetric.selectedMetricAt base)
              mu
              rho)
            (SelectedMetric.selectedMetricComponent
              (SelectedMetric.selectedMetricAt base)
              rho
              nu))
      ≡
      SelectedMetric.selectedKroneckerDelta mu nu

    selectedInverseMetricRight :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedFiniteContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (SelectedMetric.selectedMetricComponent
              (SelectedMetric.selectedMetricAt base)
              mu
              rho)
            (SelectedMetric.selectedInverseMetricComponent
              (SelectedMetric.selectedMetricAt base)
              rho
              nu))
      ≡
      SelectedMetric.selectedKroneckerDelta mu nu

    selectedTraceLaw :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      SelectedMetric.selectedTraceOfMetric
        (SelectedMetric.selectedMetricAt base)
      ≡
      NFScalar.r2

    inspectedCompatibilityBase :
      SelectedMetric.GRSelectedFiniteRBase

    inspectedCompatibilityLambda :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCompatibilityMu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCompatibilityNu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCovariantDerivativeIsR0 :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection inspectedCompatibilityBase)
        (SelectedMetric.selectedMetricAt inspectedCompatibilityBase)
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu
      ≡
      NFScalar.r0

    inspectedMetricCompatibilityShape :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedCompatibilityBase
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    inspectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedCompatibilityBase
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu

    selectedMetricCompatibilityWitnessSupplied :
      Bool

    selectedMetricCompatibilityWitnessSuppliedIsTrue :
      selectedMetricCompatibilityWitnessSupplied
      ≡
      true

    inspectionBoundary :
      List String

canonicalGRSelectedFiniteRMetricCompatibilityInspection :
  GRSelectedFiniteRMetricCompatibilityInspection
canonicalGRSelectedFiniteRMetricCompatibilityInspection =
  record
    { selectedMetricSurface =
        SelectedMetric.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; selectedMetricDependency =
        SelectedMetric.selectedGRNonFlatMetricDependency
    ; selectedMetricSymmetry =
        SelectedMetric.selectedMetricSymmetryLaw
    ; selectedInverseMetricLeft =
        SelectedMetric.selectedInverseMetricLeftLaw
    ; selectedInverseMetricRight =
        SelectedMetric.selectedInverseMetricRightLaw
    ; selectedTraceLaw =
        SelectedMetric.selectedTraceLaw
    ; inspectedCompatibilityBase =
        SelectedMetric.selectedBase0
    ; inspectedCompatibilityLambda =
        SelectedMetric.selectedRadial
    ; inspectedCompatibilityMu =
        SelectedMetric.selectedRadial
    ; inspectedCompatibilityNu =
        SelectedMetric.selectedRadial
    ; inspectedCovariantDerivativeIsR0 =
        refl
    ; inspectedMetricCompatibilityShape =
        refl
    ; inspectedMetricCompatibilityWitness =
        SelectedMetric.selectedMetricCompatibilityWitness
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; selectedMetricCompatibilityWitnessSupplied =
        true
    ; selectedMetricCompatibilityWitnessSuppliedIsTrue =
        refl
    ; inspectionBoundary =
        "The selected non-flat metric dependency is threaded into the finite-r Bianchi sidecar"
        ∷ "Metric symmetry, inverse left/right contraction, and selected trace=r2 are available from GRSelectedNonFlatMetricInstance"
        ∷ "The inspected selected slot is base0/radial/radial/radial"
        ∷ "At that slot, selectedCovariantDerivativeOfMetric now reduces to r0 and the selected metric-compatibility witness is consumed"
        ∷ "No selected Levi-Civita, Bianchi, Ricci, or Einstein promotion is claimed"
        ∷ []
    }

grSelectedFiniteRMetricCompatibilityWitnessConsumed :
  GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
    canonicalGRSelectedFiniteRMetricCompatibilityInspection
  ≡
  SelectedMetric.selectedMetricCompatibilityWitness
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
grSelectedFiniteRMetricCompatibilityWitnessConsumed =
  refl

grSelectedFiniteRMetricCompatibilityWitnessSupplied :
  GRSelectedFiniteRMetricCompatibilityInspection.selectedMetricCompatibilityWitnessSupplied
    canonicalGRSelectedFiniteRMetricCompatibilityInspection
  ≡
  true
grSelectedFiniteRMetricCompatibilityWitnessSupplied =
  refl

data GRGate4FlatVsSelectedNonFlatMetricCompatibilityStatus : Set where
  flatSelectedFiniteChartCompatibilityProvedSelectedWitnessConsumed :
    GRGate4FlatVsSelectedNonFlatMetricCompatibilityStatus

record GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt : Setω where
  field
    status :
      GRGate4FlatVsSelectedNonFlatMetricCompatibilityStatus

    flatSelectedFiniteChartMetricCompatibilityReceipt :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt

    flatSelectedFiniteChartCompatibilityTheorem :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRCovariantDerivativeOfMetric
        (NFScalar.grSelectedFiniteRConnectionAt base)
        (NFScalar.grSelectedFiniteRMetricAt base)
        lambda
        mu
        nu
      ≡
      NFScalar.r0

    flatCompatibilityProved :
      Bool

    flatCompatibilityProvedIsTrue :
      flatCompatibilityProved
      ≡
      true

    flatReceiptCompatibilityDischarged :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt.metricCompatibilityDischarged
        flatSelectedFiniteChartMetricCompatibilityReceipt
      ≡
      true

    flatReceiptNoLeviCivitaPromotion :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt.carrierConnectionIsLeviCivitaPromoted
        flatSelectedFiniteChartMetricCompatibilityReceipt
      ≡
      false

    selectedNonFlatMetricInspection :
      GRSelectedFiniteRMetricCompatibilityInspection

    selectedNonFlatMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityBase
          selectedNonFlatMetricInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityLambda
          selectedNonFlatMetricInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityMu
          selectedNonFlatMetricInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityNu
          selectedNonFlatMetricInspection)

    nonFlatCompatibilityPromoted :
      Bool

    nonFlatCompatibilityPromotedIsTrue :
      nonFlatCompatibilityPromoted
      ≡
      true

    exactNonFlatPostCompatibilityBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactNonFlatPostCompatibilityBlockerIsCarrierConnectionIsLeviCivita :
      exactNonFlatPostCompatibilityBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactLeviCivitaChainBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita :
      exactLeviCivitaChainBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    blockerExplanation :
      String

    receiptBoundary :
      List String

canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt :
  GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt =
  record
    { status =
        flatSelectedFiniteChartCompatibilityProvedSelectedWitnessConsumed
    ; flatSelectedFiniteChartMetricCompatibilityReceipt =
        NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; flatSelectedFiniteChartCompatibilityTheorem =
        NFScalar.grFlatSelectedFiniteChartMetricCompatibilityTheorem
    ; flatCompatibilityProved =
        true
    ; flatCompatibilityProvedIsTrue =
        refl
    ; flatReceiptCompatibilityDischarged =
        NFScalar.grSelectedFourChartMetricCompatibilityDischarged
    ; flatReceiptNoLeviCivitaPromotion =
        NFScalar.grSelectedFourChartMetricCompatibilityNoLeviCivitaPromotion
    ; selectedNonFlatMetricInspection =
        canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; selectedNonFlatMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; nonFlatCompatibilityPromoted =
        true
    ; nonFlatCompatibilityPromotedIsTrue =
        refl
    ; exactNonFlatPostCompatibilityBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactNonFlatPostCompatibilityBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactLeviCivitaChainBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; blockerExplanation =
        "The flat four-chart identity metric has covariantDerivativeOfMetric = r0, and the selected non-flat metric instance now exposes selectedMetricCompatibilityWitness over its r0 covariant-derivative table."
    ; receiptBoundary =
        "This receipt splits the flat selected finite-chart compatibility lane from the selected non-flat metric instance"
        ∷ "flatCompatibilityProved=true is backed by grFlatSelectedFiniteChartMetricCompatibilityTheorem over the four-chart identity metric"
        ∷ "The selected non-flat metric compatibility witness is consumed from canonicalGRSelectedFiniteRMetricCompatibilityInspection"
        ∷ "nonFlatCompatibilityPromoted=true for the selected metric-compatibility obligation"
        ∷ "The remaining Levi-Civita-chain blocker is missingCarrierConnectionIsLeviCivita"
        ∷ []
    }

grGate4FlatSelectedFiniteChartCompatibilityProved :
  GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.flatCompatibilityProved
    canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
  ≡
  true
grGate4FlatSelectedFiniteChartCompatibilityProved =
  refl

grGate4SelectedNonFlatCompatibilityPromoted :
  GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.nonFlatCompatibilityPromoted
    canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
  ≡
  true
grGate4SelectedNonFlatCompatibilityPromoted =
  refl

grGate4SelectedNonFlatMetricCompatibilityNextBlocker :
  GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.exactNonFlatPostCompatibilityBlocker
    canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grGate4SelectedNonFlatMetricCompatibilityNextBlocker =
  refl

------------------------------------------------------------------------
-- Gate 4 upper6 selected Christoffel/Levi-Civita attempt.
--
-- This supplements the placeholder selected non-flat connection inspection
-- with the actual Christoffel-from-metric numerator at the failing slot.
-- The selected finite-r carrier cannot divide the odd numerator by two, so
-- the attempt records the exact missing algebraic API and remains fail-closed.

selectedLeviCivitaChristoffelNumerator :
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedLeviCivitaChristoffelNumerator base lambda mu nu =
  SelectedMetric.selectedFiniteContract
    (λ rho →
      NFScalar.grFiniteRScalarMul
        (SelectedMetric.selectedInverseMetricComponent
          (SelectedMetric.selectedMetricAt base)
          lambda
          rho)
        (NFScalar.grFiniteRScalarSub
          (NFScalar.grFiniteRScalarAdd
            (SelectedMetric.selectedCoordinateDerivativeOfMetric
              (SelectedMetric.selectedMetricAt base)
              mu
              nu
              rho)
            (SelectedMetric.selectedCoordinateDerivativeOfMetric
              (SelectedMetric.selectedMetricAt base)
              nu
              mu
              rho))
          (SelectedMetric.selectedCoordinateDerivativeOfMetric
            (SelectedMetric.selectedMetricAt base)
            rho
            mu
            nu)))

selectedInspectedLeviCivitaChristoffelNumeratorIsOdd :
  selectedLeviCivitaChristoffelNumerator
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  NFScalar.r1
selectedInspectedLeviCivitaChristoffelNumeratorIsOdd =
  refl

selectedInspectedPlaceholderChristoffelDoubleIsZero :
  NFScalar.grFiniteRScalarMul
    NFScalar.r2
    (SelectedMetric.selectedChristoffelSymbol
      (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  NFScalar.r0
selectedInspectedPlaceholderChristoffelDoubleIsZero =
  refl

selectedInspectedLeviCivitaHalfUnavailable :
  NFScalar.grFiniteRScalarHalf
    (selectedLeviCivitaChristoffelNumerator
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  NFScalar.unavailable
    ("No half witness in the four-residue carrier for r1"
      ∷ "2 * x = r1 has no solution in GRFiniteRScalar"
      ∷ [])
selectedInspectedLeviCivitaHalfUnavailable =
  refl

selectedInspectedChristoffelFromMetricObligation :
  Set
selectedInspectedChristoffelFromMetricObligation =
  NFScalar.grFiniteRScalarMul
    NFScalar.r2
    (SelectedMetric.selectedChristoffelSymbol
      (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  selectedLeviCivitaChristoffelNumerator
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial

selectedInspectedChristoffelFromMetricShape :
  selectedInspectedChristoffelFromMetricObligation
  ≡
  (NFScalar.r0 ≡ NFScalar.r1)
selectedInspectedChristoffelFromMetricShape =
  refl

selectedInspectedChristoffelFromMetricCounterexample :
  selectedInspectedChristoffelFromMetricObligation →
  ⊥
selectedInspectedChristoffelFromMetricCounterexample =
  λ ()

data GRGate4Upper6SelectedChristoffelAttemptStatus : Set where
  upper6SelectedChristoffelAttemptBlockedByOddHalfAndMetricCancellation :
    GRGate4Upper6SelectedChristoffelAttemptStatus

record GRGate4Upper6SelectedChristoffelAttemptReceipt : Setω where
  field
    status :
      GRGate4Upper6SelectedChristoffelAttemptStatus

    priorFlatVsSelectedSplit :
      GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt

    selectedMetricInspection :
      GRSelectedFiniteRMetricCompatibilityInspection

    inspectedBase :
      SelectedMetric.GRSelectedFiniteRBase

    inspectedLambda :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedMu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedNu :
      SelectedMetric.GRSelectedCoordinateIndex

    christoffelNumeratorAtInspectedSlot :
      NFScalar.GRFiniteRScalar

    christoffelNumeratorAtInspectedSlotIsOdd :
      christoffelNumeratorAtInspectedSlot
      ≡
      NFScalar.r1

    placeholderChristoffelDoubleAtInspectedSlot :
      NFScalar.GRFiniteRScalar

    placeholderChristoffelDoubleAtInspectedSlotIsZero :
      placeholderChristoffelDoubleAtInspectedSlot
      ≡
      NFScalar.r0

    doubledChristoffelResidualHalfAtInspectedSlot :
      NFScalar.GRDiscretePartial NFScalar.GRFiniteRScalar

    doubledChristoffelResidualHalfAtInspectedSlotIsAvailable :
      doubledChristoffelResidualHalfAtInspectedSlot
      ≡
      NFScalar.available NFScalar.r0

    christoffelFromMetricObligationShape :
      selectedInspectedChristoffelFromMetricObligation
      ≡
      (NFScalar.r0 ≡ NFScalar.r1)

    christoffelFromMetricCounterexample :
      selectedInspectedChristoffelFromMetricObligation →
      ⊥

    preservedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    exactFirstNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactLeviCivitaBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactLeviCivitaBlockerIsCarrierConnectionIsLeviCivita :
      exactLeviCivitaBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactStandardLawBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactStandardLawBlockerIsStandardLeviCivitaAlgebraLaw :
      exactStandardLawBlocker
      ≡
      missingStandardLeviCivitaAlgebraLaw

    selectedLeviCivitaAttemptStaged :
      Bool

    selectedLeviCivitaAttemptStagedIsTrue :
      selectedLeviCivitaAttemptStaged
      ≡
      true

    selectedLeviCivitaPromoted :
      Bool

    selectedLeviCivitaPromotedIsFalse :
      selectedLeviCivitaPromoted
      ≡
      false

    nonFlatCompatibilityPromoted :
      Bool

    nonFlatCompatibilityPromotedIsTrue :
      nonFlatCompatibilityPromoted
      ≡
      true

    christoffelRequirements :
      List String

    missingAlgebraicCancellationAPI :
      List String

    receiptBoundary :
      List String

canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt :
  GRGate4Upper6SelectedChristoffelAttemptReceipt
canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt =
  record
    { status =
        upper6SelectedChristoffelAttemptBlockedByOddHalfAndMetricCancellation
    ; priorFlatVsSelectedSplit =
        canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; selectedMetricInspection =
        canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedBase =
        SelectedMetric.selectedBase0
    ; inspectedLambda =
        SelectedMetric.selectedRadial
    ; inspectedMu =
        SelectedMetric.selectedRadial
    ; inspectedNu =
        SelectedMetric.selectedRadial
    ; christoffelNumeratorAtInspectedSlot =
        selectedLeviCivitaChristoffelNumerator
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; christoffelNumeratorAtInspectedSlotIsOdd =
        selectedInspectedLeviCivitaChristoffelNumeratorIsOdd
    ; placeholderChristoffelDoubleAtInspectedSlot =
        NFScalar.grFiniteRScalarMul
          NFScalar.r2
          (SelectedMetric.selectedChristoffelSymbol
            (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
            SelectedMetric.selectedRadial
            SelectedMetric.selectedRadial
            SelectedMetric.selectedRadial)
    ; placeholderChristoffelDoubleAtInspectedSlotIsZero =
        selectedInspectedPlaceholderChristoffelDoubleIsZero
    ; doubledChristoffelResidualHalfAtInspectedSlot =
        NFScalar.grFiniteRScalarHalf
          (NFScalar.grFiniteRScalarMul
            NFScalar.r2
            (SelectedMetric.selectedChristoffelSymbol
              (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
              SelectedMetric.selectedRadial
              SelectedMetric.selectedRadial
              SelectedMetric.selectedRadial))
    ; doubledChristoffelResidualHalfAtInspectedSlotIsAvailable =
        refl
    ; christoffelFromMetricObligationShape =
        selectedInspectedChristoffelFromMetricShape
    ; christoffelFromMetricCounterexample =
        selectedInspectedChristoffelFromMetricCounterexample
    ; preservedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; exactFirstNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactLeviCivitaBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactLeviCivitaBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactStandardLawBlocker =
        missingStandardLeviCivitaAlgebraLaw
    ; exactStandardLawBlockerIsStandardLeviCivitaAlgebraLaw =
        refl
    ; selectedLeviCivitaAttemptStaged =
        true
    ; selectedLeviCivitaAttemptStagedIsTrue =
        refl
    ; selectedLeviCivitaPromoted =
        false
    ; selectedLeviCivitaPromotedIsFalse =
        refl
    ; nonFlatCompatibilityPromoted =
        true
    ; nonFlatCompatibilityPromotedIsTrue =
        refl
    ; christoffelRequirements =
        "For every selected base/lambda/mu/nu, provide Gamma satisfying 2 * Gamma = g^-1 contracted against the three metric derivative terms"
        ∷ "Use the same Gamma table in the covariant metric derivative expansion"
        ∷ "Prove torsion-free lower-index symmetry for the selected Christoffel table"
        ∷ "Prove covariantDerivativeOfMetric = r0 for every selected slot"
        ∷ "Then package carrierConnectionIsLeviCivita for selectedGRNonFlatMetricDependency"
        ∷ []
    ; missingAlgebraicCancellationAPI =
        "A total or proof-relevant half/division-by-two API for doubled Christoffel residuals, with the selected route staged on the doubled carrier rather than the raw r1 branch"
        ∷ "A finite-r equation solver or cancellation lemma for 2 * Gamma = numerator over GRFiniteRScalar"
        ∷ "A substitution bridge from the solved Christoffel coefficients into selectedCovariantDerivativeOfMetric"
        ∷ "A finite-contraction distributivity/cancellation API for the two-index selected contraction"
        ∷ "A proof that the resulting six-term metric-compatibility expansion cancels to r0 at every selected slot"
        ∷ []
    ; receiptBoundary =
        "upper6 tries the selected Christoffel-from-metric equation at selectedBase0/radial/radial/radial after selected metric compatibility has been witnessed"
        ∷ "The numerator reduces to r1, while the placeholder Christoffel table gives 2 * Gamma = r0"
        ∷ "The selected route is tracked through the doubled Christoffel residual; the raw r1 half blocker is no longer the staged surface"
        ∷ "The selected metric-compatibility witness is preserved; nonFlatCompatibilityPromoted is true"
        ∷ "No selected carrierConnectionIsLeviCivita, Bianchi, Ricci, or Einstein promotion is fabricated"
        ∷ []
    }

grGate4Upper6SelectedChristoffelOddNumerator :
  GRGate4Upper6SelectedChristoffelAttemptReceipt.christoffelNumeratorAtInspectedSlot
    canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
  ≡
  NFScalar.r1
grGate4Upper6SelectedChristoffelOddNumerator =
  refl

grGate4Upper6SelectedChristoffelDoubledResidualHalfAvailable :
  GRGate4Upper6SelectedChristoffelAttemptReceipt.doubledChristoffelResidualHalfAtInspectedSlot
    canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
  ≡
  NFScalar.available NFScalar.r0
grGate4Upper6SelectedChristoffelDoubledResidualHalfAvailable =
  refl

grGate4Upper6SelectedChristoffelNoNonFlatPromotion :
  GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaPromoted
    canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
  ≡
  false
grGate4Upper6SelectedChristoffelNoNonFlatPromotion =
  refl

data GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityStatus : Set where
  u4Upper6DoubledChristoffelIntegralRouteBlockedBySelectedSlot :
    GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityStatus

record GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt : Setω where
  field
    status :
      GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityStatus

    selectedChristoffelObstruction :
      GRGate4Upper6SelectedChristoffelAttemptReceipt

    doubledChristoffelRouteStaged :
      Bool

    doubledChristoffelRouteStagedIsTrue :
      doubledChristoffelRouteStaged
      ≡
      true

    inspectedDoubledChristoffelEquation :
      Set

    inspectedDoubledChristoffelEquationIsSelectedObligation :
      inspectedDoubledChristoffelEquation
      ≡
      selectedInspectedChristoffelFromMetricObligation

    inspectedDoubledChristoffelEquationShape :
      inspectedDoubledChristoffelEquation
      ≡
      (NFScalar.r0 ≡ NFScalar.r1)

    inspectedDoubledChristoffelCounterexample :
      inspectedDoubledChristoffelEquation →
      ⊥

    integralRouteAvoidsHalfSelection :
      Bool

    integralRouteAvoidsHalfSelectionIsTrue :
      integralRouteAvoidsHalfSelection
      ≡
      true

    integralRouteClosesSelectedChristoffel :
      Bool

    integralRouteClosesSelectedChristoffelIsFalse :
      integralRouteClosesSelectedChristoffel
      ≡
      false

    inspectedMetricCompatibilityShape :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    inspectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedNonFlatLeviCivitaPromoted :
      Bool

    selectedNonFlatLeviCivitaPromotedIsFalse :
      selectedNonFlatLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactLeviCivitaPromotionBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactLeviCivitaPromotionBlockerIsCarrierConnectionIsLeviCivita :
      exactLeviCivitaPromotionBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    honestStatusBoundary :
      List String

canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt :
  GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt =
  record
    { status =
        u4Upper6DoubledChristoffelIntegralRouteBlockedBySelectedSlot
    ; selectedChristoffelObstruction =
        canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; doubledChristoffelRouteStaged =
        true
    ; doubledChristoffelRouteStagedIsTrue =
        refl
    ; inspectedDoubledChristoffelEquation =
        selectedInspectedChristoffelFromMetricObligation
    ; inspectedDoubledChristoffelEquationIsSelectedObligation =
        refl
    ; inspectedDoubledChristoffelEquationShape =
        selectedInspectedChristoffelFromMetricShape
    ; inspectedDoubledChristoffelCounterexample =
        selectedInspectedChristoffelFromMetricCounterexample
    ; integralRouteAvoidsHalfSelection =
        true
    ; integralRouteAvoidsHalfSelectionIsTrue =
        refl
    ; integralRouteClosesSelectedChristoffel =
        false
    ; integralRouteClosesSelectedChristoffelIsFalse =
        refl
    ; inspectedMetricCompatibilityShape =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityShape
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedNonFlatLeviCivitaPromoted =
        false
    ; selectedNonFlatLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactLeviCivitaPromotionBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactLeviCivitaPromotionBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; honestStatusBoundary =
        "u4 upper6 doubled-Christoffel route records the integral equation 2 * Gamma = numerator without selecting a half"
        ∷ "At selectedBase0/radial/radial/radial the doubled-Christoffel equation still reduces to r0 = r1 for the current selected placeholder table"
        ∷ "The route therefore does not close a selected Christoffel-from-metric theorem from the current ingredients"
        ∷ "The same inspected metric-compatibility slot now reduces to r0 = r0 and the selected witness is preserved"
        ∷ "Fail closed: no selected non-flat Levi-Civita, Bianchi, Ricci, or Einstein promotion is produced"
        ∷ []
    }

grU4Upper6DoubledChristoffelIntegralRouteDoesNotClose :
  GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt.integralRouteClosesSelectedChristoffel
    canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
  ≡
  false
grU4Upper6DoubledChristoffelIntegralRouteDoesNotClose =
  refl

grU4Upper6DoubledChristoffelIntegralRouteNoLeviCivitaPromotion :
  GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt.selectedNonFlatLeviCivitaPromoted
    canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
  ≡
  false
grU4Upper6DoubledChristoffelIntegralRouteNoLeviCivitaPromotion =
  refl

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

    selectedFiniteRMetricCompatibilityInspection :
      GRSelectedFiniteRMetricCompatibilityInspection

    selectedFiniteRMetricCompatibilityNextBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    selectedFiniteRMetricCompatibilityNextBlockerIsCarrierConnectionIsLeviCivita :
      selectedFiniteRMetricCompatibilityNextBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    flatVsSelectedNonFlatMetricCompatibilityReceipt :
      GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt

    flatSelectedFiniteChartCompatibilityProved :
      Bool

    flatSelectedFiniteChartCompatibilityProvedIsTrue :
      flatSelectedFiniteChartCompatibilityProved
      ≡
      true

    selectedNonFlatCompatibilityPromoted :
      Bool

    selectedNonFlatCompatibilityPromotedIsTrue :
      selectedNonFlatCompatibilityPromoted
      ≡
      true

    selectedNonFlatPostCompatibilityBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    selectedNonFlatPostCompatibilityBlockerIsCarrierConnectionIsLeviCivita :
      selectedNonFlatPostCompatibilityBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    flatConstantMetricFiniteRPrerequisite :
      GRFlatConstantMetricFiniteRPrerequisiteReceipt

    finiteRFirstSevenIngredientProgress :
      GRFiniteRFirstSevenIngredientProgressReceipt

    finiteRFirstSevenNextResidualBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    finiteRFirstSevenNextResidualBlockerIsMetricCompatibility :
      finiteRFirstSevenNextResidualBlocker
      ≡
      missingMetricCompatibility

    finiteRSelectedFourChartMetricCompatibilityReceipt :
      NFScalar.GRSelectedFourChartMetricCompatibilityReceipt

    finiteRSelectedFourChartMetricCompatibilityDischarged :
      Bool

    finiteRSelectedFourChartMetricCompatibilityDischargedIsTrue :
      finiteRSelectedFourChartMetricCompatibilityDischarged
      ≡
      true

    finiteRSelectedFourChartMetricNoLeviCivitaPromotion :
      Bool

    finiteRSelectedFourChartMetricNoLeviCivitaPromotionIsFalse :
      finiteRSelectedFourChartMetricNoLeviCivitaPromotion
      ≡
      false

    finiteRMetricCompatibilityNextBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    finiteRMetricCompatibilityNextBlockerIsCarrierConnectionIsLeviCivita :
      finiteRMetricCompatibilityNextBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    finiteRGate4ConservativeStaging :
      GRFiniteRGate4ConservativeStagingReceipt

    finiteRGate4ConservativeRemainingBlockers :
      List GRDiscreteBianchiFiniteRMissingIngredient

    finiteRGate4ConservativeRemainingBlockersAreCanonical :
      finiteRGate4ConservativeRemainingBlockers
      ≡
      canonicalGRFiniteRGate4RemainingBlockers

    factorVecDiscreteMetricTensorSurface :
      FVMetric.FactorVecDiscreteMetricTensorSurface

    factorVecMetricContractedBianchiRoute :
      FVMetric.FactorVecContractedBianchiRoute

    factorVecMetricFirstContractedBianchiGate :
      FVMetric.FactorVecContractedBianchiRouteMissingGate

    factorVecMetricFirstContractedBianchiGateIsSignature :
      factorVecMetricFirstContractedBianchiGate
      ≡
      FVMetric.missingNonDegenerateFactorVecMetricSignature

    factorVecMetricSupportedUnitContractedBianchiWitness :
      FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness

    factorVecMetricSupportedUnitContractedBianchiNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecMetricSupportedUnitContractedBianchiNextIsStressEnergy :
      factorVecMetricSupportedUnitContractedBianchiNextPrimitive
      ≡
      FVMetric.missingValuationStressEnergyCompatibilityComputation

    factorVecMetricSignatureInverseHandoffProgress :
      FVMetric.FactorVecValuationP2LorentzSignatureInverseHandoffProgress

    factorVecMetricSignatureNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecMetricSignatureNextIsInverseMetric :
      factorVecMetricSignatureNextPrimitive
      ≡
      FVMetric.missingValuationInverseMetricComputation

    factorVecMetricSupportedUnitInverseChristoffelProgress :
      FVMetric.FactorVecValuationP2LorentzUnitInverseChristoffelProgress

    factorVecMetricSupportedUnitInverseNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecMetricSupportedUnitInverseNextIsChristoffel :
      factorVecMetricSupportedUnitInverseNextPrimitive
      ≡
      FVMetric.missingValuationLeviCivitaChristoffelComputation

    factorVecMetricSupportedUnitChristoffelNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecMetricSupportedUnitChristoffelNextIsRiemann :
      factorVecMetricSupportedUnitChristoffelNextPrimitive
      ≡
      FVMetric.missingValuationRiemannCurvatureComputation

    factorVecMetricSupportedUnitRiemannWitness :
      FVMetric.FactorVecValuationP2LorentzUnitRiemannWitness

    factorVecMetricSupportedUnitRiemannNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecMetricSupportedUnitRiemannNextIsRicci :
      factorVecMetricSupportedUnitRiemannNextPrimitive
      ≡
      FVMetric.missingValuationRicciContractionComputation

    factorVecMetricSupportedUnitStressEnergyCompatibilityRequest :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest

    factorVecMetricSupportedUnitStressEnergyFirstMissingPrimitive :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyFirstMissingIsTensorCandidate :
      factorVecMetricSupportedUnitStressEnergyFirstMissingPrimitive
      ≡
      FVMetric.missingValuationStressEnergyTensorCandidate

    factorVecMetricSupportedUnitStressEnergyTensorCandidateRequest :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorCandidateRequest

    factorVecMetricSupportedUnitStressEnergyTensorFirstMissingPrimitive :
      FVMetric.FactorVecStressEnergyTensorCandidateMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyTensorFirstMissingIsComponentFamily :
      factorVecMetricSupportedUnitStressEnergyTensorFirstMissingPrimitive
      ≡
      FVMetric.missingValuationStressEnergyTensorComponentFamily

    factorVecMetricSupportedUnitStressEnergyTensorComponentFamilyProgress :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingPrimitive :
      FVMetric.FactorVecStressEnergyTensorCandidateMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingIsSymmetryLaw :
      factorVecMetricSupportedUnitStressEnergyTensorNextMissingPrimitive
      ≡
      FVMetric.missingValuationStressEnergyTensorSymmetryLaw

    factorVecMetricSupportedUnitStressEnergyTensorSymmetryProgress :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterSymmetry :
      FVMetric.FactorVecStressEnergyTensorCandidateMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterSymmetryIsFiniteSupportLaw :
      factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterSymmetry
      ≡
      FVMetric.missingValuationStressEnergyTensorFiniteSupportLaw

    factorVecMetricSupportedUnitStressEnergyTensorFiniteSupportProgress :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterFiniteSupport :
      FVMetric.FactorVecStressEnergyTensorCandidateMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterFiniteSupportIsCarrierEmbedding :
      factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterFiniteSupport
      ≡
      FVMetric.missingValuationStressEnergyTensorCarrierEmbedding

    factorVecMetricSupportedUnitStressEnergyTensorCarrierEmbeddingProgress :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress

    factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterCarrierEmbedding :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterCarrierEmbeddingIsEinsteinSourceCouplingLaw :
      factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterCarrierEmbedding
      ≡
      FVMetric.missingValuationEinsteinSourceCouplingLaw

    factorVecMetricSupportedUnitEinsteinSourceCouplingProgress :
      FVMetric.FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress

    factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterEinsteinSourceCoupling :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterEinsteinSourceCouplingIsCovariantDivergenceLaw :
      factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterEinsteinSourceCoupling
      ≡
      FVMetric.missingValuationStressEnergyCovariantDivergenceLaw

    factorVecMetricSupportedUnitYMGRStressEnergyCompatibilityReceipt :
      FVMetric.FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt

    factorVecMetricSupportedUnitYMGRStressEnergyFirstMissing :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    factorVecMetricSupportedUnitYMGRStressEnergyFirstMissingIsTensorCandidate :
      factorVecMetricSupportedUnitYMGRStressEnergyFirstMissing
      ≡
      FVMetric.missingValuationStressEnergyTensorCandidate

    factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlockerIsMatterReceiptInterface :
      factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    factorVecMetricSupportedUnitExactMissingMatterInterfaceSymbol :
      String

    factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceDiagnostic :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceFirstMissing :
      EEC.W4MatterStressEnergyInterfaceMissingField

    factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceFirstMissingIsW4AnchorArtifactReceipt :
      factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceFirstMissing
      ≡
      EEC.missingW4AnchorArtifactReceiptForMatterStress

    factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityInterfaceObstruction :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceObstruction

    factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityFirstBlockerIsCandidate256 :
      factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    factorVecMetricSupportedUnitW4MatterStressEnergyNoSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceObstruction.promotesSourcedEinstein
        factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityInterfaceObstruction
      ≡
      false

    selectedNonFlatFiniteRScalarAlgebraRequest :
      GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest

    typedNonFlatScalarAlgebraSurface :
      NFScalar.GRSelectedNonFlatScalarAlgebraObligationReceipt

    typedNonFlatConditionalDependencySurface :
      NFScalar.GRSelectedNonFlatConditionalDependencySurface

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

    firstMissingIsFiniteRScalarAlgebra :
      firstMissing
      ≡
      missingFiniteRScalarAlgebra

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
    ; selectedFiniteRMetricCompatibilityInspection =
        canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; selectedFiniteRMetricCompatibilityNextBlocker =
        missingCarrierConnectionIsLeviCivita
    ; selectedFiniteRMetricCompatibilityNextBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; flatVsSelectedNonFlatMetricCompatibilityReceipt =
        canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; flatSelectedFiniteChartCompatibilityProved =
        GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.flatCompatibilityProved
          canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; flatSelectedFiniteChartCompatibilityProvedIsTrue =
        refl
    ; selectedNonFlatCompatibilityPromoted =
        GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.nonFlatCompatibilityPromoted
          canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; selectedNonFlatCompatibilityPromotedIsTrue =
        refl
    ; selectedNonFlatPostCompatibilityBlocker =
        GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.exactNonFlatPostCompatibilityBlocker
          canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; selectedNonFlatPostCompatibilityBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; flatConstantMetricFiniteRPrerequisite =
        canonicalGRFlatConstantMetricFiniteRPrerequisiteReceipt
    ; finiteRFirstSevenIngredientProgress =
        canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; finiteRFirstSevenNextResidualBlocker =
        GRFiniteRFirstSevenIngredientProgressReceipt.postFirstSevenResidualBlocker
          canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; finiteRFirstSevenNextResidualBlockerIsMetricCompatibility =
        refl
    ; finiteRSelectedFourChartMetricCompatibilityReceipt =
        NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; finiteRSelectedFourChartMetricCompatibilityDischarged =
        NFScalar.GRSelectedFourChartMetricCompatibilityReceipt.metricCompatibilityDischarged
          NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; finiteRSelectedFourChartMetricCompatibilityDischargedIsTrue =
        refl
    ; finiteRSelectedFourChartMetricNoLeviCivitaPromotion =
        NFScalar.GRSelectedFourChartMetricCompatibilityReceipt.carrierConnectionIsLeviCivitaPromoted
          NFScalar.canonicalGRSelectedFourChartMetricCompatibilityReceipt
    ; finiteRSelectedFourChartMetricNoLeviCivitaPromotionIsFalse =
        refl
    ; finiteRMetricCompatibilityNextBlocker =
        missingCarrierConnectionIsLeviCivita
    ; finiteRMetricCompatibilityNextBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; finiteRGate4ConservativeStaging =
        canonicalGRFiniteRGate4ConservativeStagingReceipt
    ; finiteRGate4ConservativeRemainingBlockers =
        GRFiniteRGate4ConservativeStagingReceipt.remainingGate4Blockers
          canonicalGRFiniteRGate4ConservativeStagingReceipt
    ; finiteRGate4ConservativeRemainingBlockersAreCanonical =
        refl
    ; factorVecDiscreteMetricTensorSurface =
        FVMetric.canonicalFactorVecDiscreteMetricTensorSurface
    ; factorVecMetricContractedBianchiRoute =
        FVMetric.canonicalFactorVecContractedBianchiRoute
    ; factorVecMetricFirstContractedBianchiGate =
        FVMetric.FactorVecContractedBianchiRoute.firstRemainingGate
          FVMetric.canonicalFactorVecContractedBianchiRoute
    ; factorVecMetricFirstContractedBianchiGateIsSignature =
        refl
    ; factorVecMetricSupportedUnitContractedBianchiWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; factorVecMetricSupportedUnitContractedBianchiNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness.firstRemainingMetricPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; factorVecMetricSupportedUnitContractedBianchiNextIsStressEnergy =
        refl
    ; factorVecMetricSignatureInverseHandoffProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzSignatureInverseHandoffProgress
    ; factorVecMetricSignatureNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzSignatureInverseHandoffProgress.firstMetricPrimitiveAfterInertia
          FVMetric.canonicalFactorVecValuationP2LorentzSignatureInverseHandoffProgress
    ; factorVecMetricSignatureNextIsInverseMetric =
        refl
    ; factorVecMetricSupportedUnitInverseChristoffelProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; factorVecMetricSupportedUnitInverseNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitInverse
          FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; factorVecMetricSupportedUnitInverseNextIsChristoffel =
        refl
    ; factorVecMetricSupportedUnitChristoffelNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitChristoffel
          FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; factorVecMetricSupportedUnitChristoffelNextIsRiemann =
        refl
    ; factorVecMetricSupportedUnitRiemannWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; factorVecMetricSupportedUnitRiemannNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitRiemannWitness.firstRemainingMetricPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; factorVecMetricSupportedUnitRiemannNextIsRicci =
        refl
    ; factorVecMetricSupportedUnitStressEnergyCompatibilityRequest =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; factorVecMetricSupportedUnitStressEnergyFirstMissingPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; factorVecMetricSupportedUnitStressEnergyFirstMissingIsTensorCandidate =
        refl
    ; factorVecMetricSupportedUnitStressEnergyTensorCandidateRequest =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.tensorCandidateRequest
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; factorVecMetricSupportedUnitStressEnergyTensorFirstMissingPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingTensorCandidatePrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; factorVecMetricSupportedUnitStressEnergyTensorFirstMissingIsComponentFamily =
        refl
    ; factorVecMetricSupportedUnitStressEnergyTensorComponentFamilyProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress.firstRemainingTensorCandidatePrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorComponentFamilyProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingIsSymmetryLaw =
        refl
    ; factorVecMetricSupportedUnitStressEnergyTensorSymmetryProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterSymmetry =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress.firstRemainingTensorCandidatePrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorSymmetryProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterSymmetryIsFiniteSupportLaw =
        refl
    ; factorVecMetricSupportedUnitStressEnergyTensorFiniteSupportProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterFiniteSupport =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress.firstRemainingTensorCandidatePrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorFiniteSupportProgress
    ; factorVecMetricSupportedUnitStressEnergyTensorNextMissingAfterFiniteSupportIsCarrierEmbedding =
        refl
    ; factorVecMetricSupportedUnitStressEnergyTensorCarrierEmbeddingProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
    ; factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterCarrierEmbedding =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress.firstRemainingStressEnergyCompatibilityPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyTensorCarrierEmbeddingProgress
    ; factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterCarrierEmbeddingIsEinsteinSourceCouplingLaw =
        refl
    ; factorVecMetricSupportedUnitEinsteinSourceCouplingProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterEinsteinSourceCoupling =
        FVMetric.FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress.firstRemainingStressEnergyCompatibilityPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; factorVecMetricSupportedUnitStressEnergyCompatibilityNextMissingAfterEinsteinSourceCouplingIsCovariantDivergenceLaw =
        refl
    ; factorVecMetricSupportedUnitYMGRStressEnergyCompatibilityReceipt =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
    ; factorVecMetricSupportedUnitYMGRStressEnergyFirstMissing =
        FVMetric.FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.stressEnergyCompatibilityRequestFirstMissing
          FVMetric.canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
    ; factorVecMetricSupportedUnitYMGRStressEnergyFirstMissingIsTensorCandidate =
        refl
    ; factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlocker =
        FVMetric.FactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt.firstRemainingStressEnergyCompatibilityPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitYMGRStressEnergyCompatibilityReceipt
    ; factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlockerIsMatterReceiptInterface =
        refl
    ; factorVecMetricSupportedUnitExactMissingMatterInterfaceSymbol =
        FVMetric.FactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress.exactMissingMatterInterfaceSymbol
          FVMetric.canonicalFactorVecValuationP2LorentzUnitEinsteinSourceCouplingProgress
    ; factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceDiagnostic =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceFirstMissing =
        EEC.W4MatterStressEnergyInterfaceDiagnostic.firstMissing
          EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; factorVecMetricSupportedUnitW4MatterStressEnergyInterfaceFirstMissingIsW4AnchorArtifactReceipt =
        refl
    ; factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityInterfaceObstruction =
        W4Stress.canonicalW4MatterStressEnergyAuthorityInterfaceObstruction
    ; factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityFirstBlocker =
        W4Stress.W4MatterStressEnergyAuthorityInterfaceObstruction.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyAuthorityInterfaceObstruction
    ; factorVecMetricSupportedUnitW4MatterStressEnergyAuthorityFirstBlockerIsCandidate256 =
        refl
    ; factorVecMetricSupportedUnitW4MatterStressEnergyNoSourcedEinsteinPromotion =
        refl
    ; selectedNonFlatFiniteRScalarAlgebraRequest =
        canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; typedNonFlatScalarAlgebraSurface =
        NFScalar.canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
    ; typedNonFlatConditionalDependencySurface =
        NFScalar.canonicalGRSelectedNonFlatConditionalDependencySurface
    ; inspectedJacobiSurfaces =
        "DASHI.Combinatorics.String.LieAlgebra exposes Carrier, bracket, antisym, and a Jacobi equality over a carrier"
        ∷ "DASHI.Physics.Constraints.Bracket.LieLike exposes a constraint bracket plus abstract antisym and jacobi fields"
        ∷ "DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate exposes only flat-vacuum curvature diagnostics and missing non-flat connection/Ricci/Einstein fields"
        ∷ "DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT records no CRT-derived non-flat connection or Bianchi witness"
        ∷ "DASHI.Physics.Closure.GRFirstOrderGravityScope records finite-r Bianchi as an obligation, not as an inhabited law"
        ∷ "DASHI.Physics.Closure.MinkowskiLimitReceipt now feeds a typed flat constant metric prerequisite, but not the selected non-flat GR carrier"
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
        missingFiniteRScalarAlgebra
    ; firstMissingIsFiniteRScalarAlgebra =
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
        "A flat constant finite-r prerequisite is typed from MinkowskiLimitReceipt, and a separate four-chart finite-r carrier witness now supplies the local scalar/base/neighbourhood/derivation/bracket/Jacobi/shift layer"
        ∷ "A FactorVec tangent metric tensor surface now supplies symmetric rational g and a flat finite Koszul/Christoffel witness over SSP directions"
        ∷ "A typed handoff witness now threads local MetricNondegenerateSignature completion to the exact inverse-metric queue head"
        ∷ "The FactorVec supported unit p2-time route now supplies an explicit inverse→Christoffel progress package with next blockers typed as Christoffel then Riemann"
        ∷ "The same supported unit p2-time route now threads an explicit local Riemann witness and types the next local metric primitive as Ricci contraction"
        ∷ "The FactorVec supported unit p2-time route now supplies zero-table Ricci contraction and contracted-Bianchi divergence witnesses"
        ∷ "The supported unit p2-time stress-energy tensor candidate now supplies component-family, symmetry, finite-support, and carrier-embedding progress on the zero-table witness"
        ∷ "After that carrier-embedding progress, the next typed stress-energy compatibility primitive is Einstein-source coupling"
        ∷ "The same supported unit p2-time route now discharges Einstein-source coupling locally on the zero-table Einstein/stress-energy component family and advances to covariant-divergence compatibility"
        ∷ "A typed YM/GR stress-energy compatibility receipt now connects that supported component family to the formal YM tensor shape and contracted-Bianchi conservation target without promoting global GR"
        ∷ "Exact downstream matter interface symbol remains authority-boundary blocked: DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
        ∷ "The W4 matter/stress-energy interface diagnostic is explicitly threaded here and still first-missing at the W4 anchor artifact receipt"
        ∷ "The W4 matter/stress-energy authority-interface obstruction is now threaded here with Candidate256 calibration as the local first blocker and sourced-Einstein promotion set false"
        ∷ "A selected non-flat finite-r scalar-algebra dependency request now names the scalar algebra, metric, inverse metric, inverse law, coordinate derivative, finite contraction, Christoffel law, trace, six-term cancellation, and trace=4 law"
        ∷ "GRNonFlatScalarAlgebraSurface now types the selected CarrierScalar operations, four-chart base carrier, cyclic neighbourhood/cell, finite derivations, carrier bracket, Jacobi witness, connection shift law, non-flat metric dependency interface, inverse-metric contraction laws, derivative expansion, Christoffel-from-metric law, finite contraction, trace, and six-term cancellation law"
        ∷ "The first seven finite-r ingredients are advanced locally by canonicalGRFiniteRFirstSevenIngredientProgressReceipt"
        ∷ "The selected non-flat metric dependency is threaded here through canonicalGRSelectedFiniteRMetricCompatibilityInspection"
        ∷ "The flat selected finite-chart compatibility lane is split out with flatCompatibilityProved=true while selectedNonFlatCompatibilityPromoted=true"
        ∷ "Metric symmetry, inverse contraction, and trace=r2 are typed for the selected finite-r metric instance"
        ∷ "At selectedBase0/radial/radial/radial the selected placeholder connection has covariantDerivativeOfMetric = r0, so metricCompatibility is witnessed"
        ∷ "The selected GR metric-compatibility witness is bound to the four-chart carrier connection"
        ∷ "A metricCompatibility witness is available for the selected finite-r metric and carrier connection"
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
        ∷ "This sidecar does not turn the FactorVec flat metric tensor seed into a non-degenerate Lorentzian metric"
        ∷ "This sidecar does not inhabit carrierConnectionIsLeviCivita for any selected non-flat carrier"
        ∷ "This sidecar does not convert the flat-vacuum diagnostic into finite-r GR"
        ∷ "This sidecar does not promote the supported unit p2-time Ricci/Bianchi zero tables to a global non-flat connection, ricciFromBianchi theorem, vacuum Ricci-zero theorem, Einstein tensor law, or sourced Einstein law"
        ∷ "This sidecar does not construct W4MatterStressEnergyInterfaceReceipt"
        ∷ "This sidecar does not promote GR, G4, G6, W4, W5, or GR/QFT closure"
        ∷ []
    }

data GRGlobalNonFlatLeviCivitaChristoffelPromotionStatus : Set where
  globalNonFlatLeviCivitaChristoffelPromotionBlocked :
    GRGlobalNonFlatLeviCivitaChristoffelPromotionStatus

record GRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt : Setω where
  field
    status :
      GRGlobalNonFlatLeviCivitaChristoffelPromotionStatus

    factorVecMetricTensorSurface :
      FVMetric.FactorVecDiscreteMetricTensorSurface

    factorVecSupportedUnitInverseChristoffelProgress :
      FVMetric.FactorVecValuationP2LorentzUnitInverseChristoffelProgress

    factorVecSupportedUnitInverseNextPrimitive :
      FVMetric.FactorVecMetricGRPrimitive

    factorVecSupportedUnitInverseNextPrimitiveIsChristoffel :
      factorVecSupportedUnitInverseNextPrimitive
      ≡
      FVMetric.missingValuationLeviCivitaChristoffelComputation

    selectedNonFlatScalarAlgebraRequest :
      GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest

    selectedNonFlatScalarOperationsSurface :
      NFScalar.GRCarrierScalarOperations

    selectedNonFlatScalarOperationsSurfaceIsCanonicalFiniteR :
      selectedNonFlatScalarOperationsSurface
      ≡
      NFScalar.canonicalGRFiniteRCarrierScalarOperations

    selectedNonFlatScalarAlgebraSurface :
      NFScalar.GRSelectedNonFlatScalarAlgebraObligationReceipt

    selectedNonFlatConditionalDependencySurface :
      NFScalar.GRSelectedNonFlatConditionalDependencySurface

    finiteRBianchiSurface :
      GRDiscreteBianchiFiniteRObligationSurface

    firstMissing :
      GRDiscreteBianchiFiniteRMissingIngredient

    firstMissingIsFiniteRScalarAlgebra :
      firstMissing
      ≡
      missingFiniteRScalarAlgebra

    missingMetricCompatibilityMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingMetricCompatibilityMarkerIsMetricCompatibility :
      missingMetricCompatibilityMarker
      ≡
      missingMetricCompatibility

    missingCarrierConnectionIsLeviCivitaMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingCarrierConnectionIsLeviCivitaMarkerIsCanonical :
      missingCarrierConnectionIsLeviCivitaMarker
      ≡
      missingCarrierConnectionIsLeviCivita

    missingStandardLeviCivitaAlgebraLawMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    missingStandardLeviCivitaAlgebraLawMarkerIsCanonical :
      missingStandardLeviCivitaAlgebraLawMarker
      ≡
      missingStandardLeviCivitaAlgebraLaw

    promotionBoundary :
      List String

canonicalGRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt :
  GRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt
canonicalGRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt =
  record
    { status =
        globalNonFlatLeviCivitaChristoffelPromotionBlocked
    ; factorVecMetricTensorSurface =
        FVMetric.canonicalFactorVecDiscreteMetricTensorSurface
    ; factorVecSupportedUnitInverseChristoffelProgress =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; factorVecSupportedUnitInverseNextPrimitive =
        FVMetric.FactorVecValuationP2LorentzUnitInverseChristoffelProgress.firstMetricPrimitiveAfterUnitInverse
          FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseChristoffelProgress
    ; factorVecSupportedUnitInverseNextPrimitiveIsChristoffel =
        refl
    ; selectedNonFlatScalarAlgebraRequest =
        canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; selectedNonFlatScalarOperationsSurface =
        GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.scalarOperationsSurface
          canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; selectedNonFlatScalarOperationsSurfaceIsCanonicalFiniteR =
        GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest.scalarOperationsSurfaceIsCanonicalFiniteR
          canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; selectedNonFlatScalarAlgebraSurface =
        NFScalar.canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
    ; selectedNonFlatConditionalDependencySurface =
        NFScalar.canonicalGRSelectedNonFlatConditionalDependencySurface
    ; finiteRBianchiSurface =
        canonicalGRDiscreteBianchiFiniteRObligationSurface
    ; firstMissing =
        missingFiniteRScalarAlgebra
    ; firstMissingIsFiniteRScalarAlgebra =
        refl
    ; missingMetricCompatibilityMarker =
        missingMetricCompatibility
    ; missingMetricCompatibilityMarkerIsMetricCompatibility =
        refl
    ; missingCarrierConnectionIsLeviCivitaMarker =
        missingCarrierConnectionIsLeviCivita
    ; missingCarrierConnectionIsLeviCivitaMarkerIsCanonical =
        refl
    ; missingStandardLeviCivitaAlgebraLawMarker =
        missingStandardLeviCivitaAlgebraLaw
    ; missingStandardLeviCivitaAlgebraLawMarkerIsCanonical =
        refl
    ; promotionBoundary =
        "This receipt composes the selected non-flat scalar-algebra dependency request, the FactorVec metric tensor surface, and the finite-r Bianchi obligation surface"
        ∷ "The supported unit inverse-metric progress still points first to Christoffel-from-metric as the next local metric primitive"
        ∷ "The global finite-r queue remains blocked before scalar-algebra/metric-compatibility/Levi-Civita inhabitants are provided on a selected non-flat carrier"
        ∷ "No non-flat Levi-Civita connection, global Christoffel-from-metric theorem, Ricci-from-Bianchi theorem, or Einstein promotion is claimed here"
        ∷ []
    }

grGlobalNonFlatLeviCivitaChristoffelPromotionFirstMissing :
  GRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt.firstMissing
    canonicalGRGlobalNonFlatLeviCivitaChristoffelPromotionReceipt
  ≡
  missingFiniteRScalarAlgebra
grGlobalNonFlatLeviCivitaChristoffelPromotionFirstMissing = refl

data GRNonFlatMetricTowerFailClosedStatus : Set where
  nonFlatMetricTowerStagedAwaitingStressEnergySource :
    GRNonFlatMetricTowerFailClosedStatus

record GRNonFlatMetricTowerFailClosedReceipt : Setω where
  field
    status :
      GRNonFlatMetricTowerFailClosedStatus

    selectedNonFlatScalarAlgebraRequest :
      GRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest

    selectedNonFlatScalarAlgebraSurface :
      NFScalar.GRSelectedNonFlatScalarAlgebraObligationReceipt

    finiteRBianchiSurface :
      GRDiscreteBianchiFiniteRObligationSurface

    finiteRContractionBoundaryWave3 :
      GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt

    supportedUnitInverseMetricWitness :
      FVMetric.FactorVecValuationP2LorentzUnitInverseMetricWitness

    supportedUnitChristoffelWitness :
      FVMetric.FactorVecValuationP2LorentzUnitChristoffelWitness

    supportedUnitRiemannWitness :
      FVMetric.FactorVecValuationP2LorentzUnitRiemannWitness

    supportedUnitRicciWitness :
      FVMetric.FactorVecValuationP2LorentzUnitRicciWitness

    supportedUnitScalarCurvatureWitness :
      FVMetric.FactorVecValuationP2LorentzUnitScalarCurvatureWitness

    supportedUnitEinsteinTensorWitness :
      FVMetric.FactorVecValuationP2LorentzUnitEinsteinTensorWitness

    supportedUnitContractedBianchiWitness :
      FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness

    inverseMetricPrimitiveDischarged :
      FVMetric.FactorVecMetricGRPrimitive

    inverseMetricPrimitiveDischargedIsValuationInverse :
      inverseMetricPrimitiveDischarged
      ≡
      FVMetric.missingValuationInverseMetricComputation

    christoffelPrimitiveDischarged :
      FVMetric.FactorVecMetricGRPrimitive

    christoffelPrimitiveDischargedIsValuationChristoffel :
      christoffelPrimitiveDischarged
      ≡
      FVMetric.missingValuationLeviCivitaChristoffelComputation

    riemannPrimitiveDischarged :
      FVMetric.FactorVecMetricGRPrimitive

    riemannPrimitiveDischargedIsValuationRiemann :
      riemannPrimitiveDischarged
      ≡
      FVMetric.missingValuationRiemannCurvatureComputation

    ricciPrimitiveDischarged :
      FVMetric.FactorVecMetricGRPrimitive

    ricciPrimitiveDischargedIsValuationRicci :
      ricciPrimitiveDischarged
      ≡
      FVMetric.missingValuationRicciContractionComputation

    contractedBianchiPrimitiveDischarged :
      FVMetric.FactorVecMetricGRPrimitive

    contractedBianchiPrimitiveDischargedIsValuationContractedBianchi :
      contractedBianchiPrimitiveDischarged
      ≡
      FVMetric.missingValuationContractedBianchiComputation

    firstMetricPrimitiveAfterGeometry :
      FVMetric.FactorVecMetricGRPrimitive

    firstMetricPrimitiveAfterGeometryIsStressEnergy :
      firstMetricPrimitiveAfterGeometry
      ≡
      FVMetric.missingValuationStressEnergyCompatibilityComputation

    upstreamSourceBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    upstreamSourceBlockerIsStressEnergyTensorCandidate :
      upstreamSourceBlocker
      ≡
      FVMetric.missingValuationStressEnergyTensorCandidate

    upstreamContractedBianchiSourceIngredient :
      GRDiscreteBianchiFiniteRMissingIngredient

    upstreamContractedBianchiSourceIngredientIsStressEnergyCompatibility :
      upstreamContractedBianchiSourceIngredient
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceObstruction.promotesSourcedEinstein
        W4Stress.canonicalW4MatterStressEnergyAuthorityInterfaceObstruction
      ≡
      false

    towerBoundary :
      List String

canonicalGRNonFlatMetricTowerFailClosedReceipt :
  GRNonFlatMetricTowerFailClosedReceipt
canonicalGRNonFlatMetricTowerFailClosedReceipt =
  record
    { status =
        nonFlatMetricTowerStagedAwaitingStressEnergySource
    ; selectedNonFlatScalarAlgebraRequest =
        canonicalGRSelectedNonFlatFiniteRScalarAlgebraDependencyRequest
    ; selectedNonFlatScalarAlgebraSurface =
        NFScalar.canonicalGRSelectedNonFlatScalarAlgebraObligationReceipt
    ; finiteRBianchiSurface =
        canonicalGRDiscreteBianchiFiniteRObligationSurface
    ; finiteRContractionBoundaryWave3 =
        canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
    ; supportedUnitInverseMetricWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; supportedUnitChristoffelWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; supportedUnitRiemannWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; supportedUnitRicciWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitRicciWitness
    ; supportedUnitScalarCurvatureWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitScalarCurvatureWitness
    ; supportedUnitEinsteinTensorWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitEinsteinTensorWitness
    ; supportedUnitContractedBianchiWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; inverseMetricPrimitiveDischarged =
        FVMetric.FactorVecValuationP2LorentzUnitInverseMetricWitness.inverseMetricPrimitiveDischarged
          FVMetric.canonicalFactorVecValuationP2LorentzUnitInverseMetricWitness
    ; inverseMetricPrimitiveDischargedIsValuationInverse =
        refl
    ; christoffelPrimitiveDischarged =
        FVMetric.FactorVecValuationP2LorentzUnitChristoffelWitness.christoffelPrimitiveDischarged
          FVMetric.canonicalFactorVecValuationP2LorentzUnitChristoffelWitness
    ; christoffelPrimitiveDischargedIsValuationChristoffel =
        refl
    ; riemannPrimitiveDischarged =
        FVMetric.FactorVecValuationP2LorentzUnitRiemannWitness.riemannPrimitiveDischarged
          FVMetric.canonicalFactorVecValuationP2LorentzUnitRiemannWitness
    ; riemannPrimitiveDischargedIsValuationRiemann =
        refl
    ; ricciPrimitiveDischarged =
        FVMetric.FactorVecValuationP2LorentzUnitRicciWitness.ricciPrimitiveDischarged
          FVMetric.canonicalFactorVecValuationP2LorentzUnitRicciWitness
    ; ricciPrimitiveDischargedIsValuationRicci =
        refl
    ; contractedBianchiPrimitiveDischarged =
        FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness.contractedBianchiPrimitiveDischarged
          FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; contractedBianchiPrimitiveDischargedIsValuationContractedBianchi =
        refl
    ; firstMetricPrimitiveAfterGeometry =
        FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness.firstRemainingMetricPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; firstMetricPrimitiveAfterGeometryIsStressEnergy =
        refl
    ; upstreamSourceBlocker =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest.firstMissingStressEnergyCompatibilityPrimitive
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyCompatibilityRequest
    ; upstreamSourceBlockerIsStressEnergyTensorCandidate =
        refl
    ; upstreamContractedBianchiSourceIngredient =
        missingStressEnergyCompatibilityForContractedBianchi
    ; upstreamContractedBianchiSourceIngredientIsStressEnergyCompatibility =
        refl
    ; noSourcedEinsteinPromotion =
        W4Stress.W4MatterStressEnergyAuthorityInterfaceObstruction.promotesSourcedEinsteinIsFalse
          W4Stress.canonicalW4MatterStressEnergyAuthorityInterfaceObstruction
    ; towerBoundary =
        "This receipt stages the u4 geometric tower only: inverse metric, Levi-Civita/Christoffel, Riemann, Ricci, scalar curvature, Einstein tensor, and contracted Bianchi"
        ∷ "The inhabited geometric fields are the supported unit p2-time zero-table witnesses from FactorVecDiscreteMetricTensorSurface"
        ∷ "Continuation wave 3 advances the local finite-r curvature-to-Ricci/Einstein contraction boundary to the stress-energy compatibility frontier"
        ∷ "Those witnesses are not promoted to a selected global non-flat finite-r connection or non-flat Einstein tensor law"
        ∷ "After the contracted-Bianchi witness, the exact next metric primitive is stress-energy compatibility"
        ∷ "The exact upstream source blocker is FactorVecDiscreteMetricTensorSurface.missingValuationStressEnergyTensorCandidate"
        ∷ "This receipt constructs no stress-energy tensor, no W4MatterStressEnergyInterfaceReceipt, and no sourced Einstein equation"
        ∷ []
    }

grNonFlatMetricTowerFailClosedFirstMetricPrimitiveAfterGeometry :
  GRNonFlatMetricTowerFailClosedReceipt.firstMetricPrimitiveAfterGeometry
    canonicalGRNonFlatMetricTowerFailClosedReceipt
  ≡
  FVMetric.missingValuationStressEnergyCompatibilityComputation
grNonFlatMetricTowerFailClosedFirstMetricPrimitiveAfterGeometry = refl

grNonFlatMetricTowerFailClosedSourceBlocker :
  GRNonFlatMetricTowerFailClosedReceipt.upstreamSourceBlocker
    canonicalGRNonFlatMetricTowerFailClosedReceipt
  ≡
  FVMetric.missingValuationStressEnergyTensorCandidate
grNonFlatMetricTowerFailClosedSourceBlocker = refl

grNonFlatMetricTowerFailClosedContractedBianchiSourceIngredient :
  GRNonFlatMetricTowerFailClosedReceipt.upstreamContractedBianchiSourceIngredient
    canonicalGRNonFlatMetricTowerFailClosedReceipt
  ≡
  missingStressEnergyCompatibilityForContractedBianchi
grNonFlatMetricTowerFailClosedContractedBianchiSourceIngredient = refl

data GRFiniteRStressEnergyT00BridgeStagingStatus : Set where
  finiteRStressEnergyT00StagedNoMatterInterfacePromotion :
    GRFiniteRStressEnergyT00BridgeStagingStatus

record GRFiniteRStressEnergyT00BridgeStagingReceipt : Setω where
  field
    status :
      GRFiniteRStressEnergyT00BridgeStagingStatus

    finiteRBianchiSurface :
      GRDiscreteBianchiFiniteRObligationSurface

    concreteFiniteRScalarCarrierStaging :
      NFScalar.GRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt

    factorVecT00FullTensorStaging :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt

    factorVecT00CandidateIsCanonical :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.t00Candidate
        factorVecT00FullTensorStaging
      ≡
      FVMetric.factorVecUnitP2LorentzStressEnergyT00Candidate

    localStressEnergyOriginalFirstMissing :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localStressEnergyOriginalFirstMissingIsTensorCandidate :
      localStressEnergyOriginalFirstMissing
      ≡
      FVMetric.missingValuationStressEnergyTensorCandidate

    localStressEnergyRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localStressEnergyRemainingBlockerIsMatterReceiptInterface :
      localStressEnergyRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    globalFiniteRFirstBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    globalFiniteRFirstBlockerIsFiniteRScalarAlgebra :
      globalFiniteRFirstBlocker
      ≡
      missingFiniteRScalarAlgebra

    exactMissingMatterInterfaceSymbol :
      String

    bridgeBoundary :
      List String

canonicalGRFiniteRStressEnergyT00BridgeStagingReceipt :
  GRFiniteRStressEnergyT00BridgeStagingReceipt
canonicalGRFiniteRStressEnergyT00BridgeStagingReceipt =
  record
    { status =
        finiteRStressEnergyT00StagedNoMatterInterfacePromotion
    ; finiteRBianchiSurface =
        canonicalGRDiscreteBianchiFiniteRObligationSurface
    ; concreteFiniteRScalarCarrierStaging =
        NFScalar.canonicalGRConcreteFiniteRBaseDerivationBracketConnectionStagingReceipt
    ; factorVecT00FullTensorStaging =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
    ; factorVecT00CandidateIsCanonical =
        refl
    ; localStressEnergyOriginalFirstMissing =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.originalCompatibilityFirstMissing
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
    ; localStressEnergyOriginalFirstMissingIsTensorCandidate =
        refl
    ; localStressEnergyRemainingBlocker =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt.localProgressRemainingBlocker
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyT00FullTensorStagingReceipt
    ; localStressEnergyRemainingBlockerIsMatterReceiptInterface =
        refl
    ; globalFiniteRFirstBlocker =
        missingFiniteRScalarAlgebra
    ; globalFiniteRFirstBlockerIsFiniteRScalarAlgebra =
        refl
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; bridgeBoundary =
        "This receipt bridges the bounded m3 finite-r base/derivation/bracket/connection staging to the local u3 FactorVec T00/full stress-energy tensor staging"
        ∷ "The FactorVec tensor is the supported unit p2-time zero-table candidate only; the original local compatibility request remains first-missing at the tensor-candidate primitive"
        ∷ "The bounded local stress-energy lane advances only to missingValuationMatterReceiptInterface"
        ∷ "The global finite-r sidecar still records missingFiniteRScalarAlgebra as the first true blocker"
        ∷ "No W4MatterStressEnergyInterfaceReceipt, sourced Einstein law, Ricci-from-Bianchi theorem, or GR promotion is constructed"
        ∷ []
    }

grFiniteRStressEnergyT00BridgeGlobalFirstBlocker :
  GRFiniteRStressEnergyT00BridgeStagingReceipt.globalFiniteRFirstBlocker
    canonicalGRFiniteRStressEnergyT00BridgeStagingReceipt
  ≡
  missingFiniteRScalarAlgebra
grFiniteRStressEnergyT00BridgeGlobalFirstBlocker =
  refl

grFiniteRStressEnergyT00BridgeLocalRemainingBlocker :
  GRFiniteRStressEnergyT00BridgeStagingReceipt.localStressEnergyRemainingBlocker
    canonicalGRFiniteRStressEnergyT00BridgeStagingReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grFiniteRStressEnergyT00BridgeLocalRemainingBlocker =
  refl

data GRFiniteRStressEnergyFullComponentFlatMinkowskiStatus : Set where
  finiteRStressEnergyFullComponentFamilyStagedFlatMinkowskiNoW4Promotion :
    GRFiniteRStressEnergyFullComponentFlatMinkowskiStatus

record GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt : Setω where
  field
    status :
      GRFiniteRStressEnergyFullComponentFlatMinkowskiStatus

    flatMinkowskiLeviCivitaClosure :
      GRFlatMinkowskiFiniteRLeviCivitaClosure

    flatMinkowskiLeviCivitaClosureStatus :
      GRFlatMinkowskiFiniteRLeviCivitaStatus

    flatMinkowskiLeviCivitaClosureStatusIsClosedNoSelectedGRPromotion :
      flatMinkowskiLeviCivitaClosureStatus
      ≡
      flatMinkowskiFiniteRLeviCivitaClosedNoSelectedGRPromotion

    valuationMatterInterfaceReceipt :
      FVMetric.FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt

    fullComponentFamilyReceipt :
      FVMetric.FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt

    contractedBianchiWitness :
      FVMetric.FactorVecValuationP2LorentzUnitContractedBianchiWitness

    contractedBianchiConservationTarget :
      FVMetric.FactorVecTangentDirection →
      ℚ

    contractedBianchiConservationTargetIsSupportedZeroTable :
      contractedBianchiConservationTarget
      ≡
      FVMetric.factorVecUnitP2LorentzContractedBianchiDivergence

    stressEnergyCovariantDivergenceLaw :
      FVMetric.FactorVecStressEnergyCovariantDivergenceLaw
        (FVMetric.FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt.fullTensorCandidate
          fullComponentFamilyReceipt)

    localProgressRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localProgressRemainingBlockerIsMatterReceiptInterface :
      localProgressRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    w4ExternalHalt :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt

    w4ExternalHaltFirstBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4ExternalHaltFirstBlockerIsCandidate256 :
      w4ExternalHaltFirstBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        w4ExternalHalt
      ≡
      false

    exactMissingMatterInterfaceSymbol :
      String

    receiptBoundary :
      List String

canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt :
  GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt =
  record
    { status =
        finiteRStressEnergyFullComponentFamilyStagedFlatMinkowskiNoW4Promotion
    ; flatMinkowskiLeviCivitaClosure =
        canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure
    ; flatMinkowskiLeviCivitaClosureStatus =
        GRFlatMinkowskiFiniteRLeviCivitaClosure.status
          canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure
    ; flatMinkowskiLeviCivitaClosureStatusIsClosedNoSelectedGRPromotion =
        refl
    ; valuationMatterInterfaceReceipt =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; fullComponentFamilyReceipt =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; contractedBianchiWitness =
        FVMetric.canonicalFactorVecValuationP2LorentzUnitContractedBianchiWitness
    ; contractedBianchiConservationTarget =
        FVMetric.factorVecUnitP2LorentzContractedBianchiDivergence
    ; contractedBianchiConservationTargetIsSupportedZeroTable =
        refl
    ; stressEnergyCovariantDivergenceLaw =
        FVMetric.FactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt.covariantDivergenceLaw
          FVMetric.canonicalFactorVecValuationP2LorentzUnitStressEnergyFullComponentFamilyReceipt
    ; localProgressRemainingBlocker =
        FVMetric.FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.localProgressRemainingBlocker
          FVMetric.canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; localProgressRemainingBlockerIsMatterReceiptInterface =
        refl
    ; w4ExternalHalt =
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; w4ExternalHaltFirstBlocker =
        W4Stress.W4MatterStressEnergyInterfaceExternalHalt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; w4ExternalHaltFirstBlockerIsCandidate256 =
        refl
    ; noSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; exactMissingMatterInterfaceSymbol =
        "DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt"
    ; receiptBoundary =
        "This receipt advances the u3 stress-energy bridge beyond T00 by threading the full FactorVec component family through local source coupling and conservation"
        ∷ "The conservation check uses the supported zero-table contracted-Bianchi target together with the already inhabited flat Minkowski finite-r Levi-Civita closure"
        ∷ "This is a flat local compatibility closure only; it does not promote a selected non-flat GR carrier or sourced Einstein equation"
        ∷ "The exact remaining halt is the external W4MatterStressEnergyInterfaceReceipt, with Candidate256 calibration as the local W4 authority blocker"
        ∷ []
    }

grFiniteRStressEnergyFullComponentFlatMinkowskiLocalRemaining :
  GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt.localProgressRemainingBlocker
    canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grFiniteRStressEnergyFullComponentFlatMinkowskiLocalRemaining =
  refl

grFiniteRStressEnergyFullComponentFlatMinkowskiNoSourcedEinsteinPromotion :
  GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt.noSourcedEinsteinPromotion
    canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
  ≡
  W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
grFiniteRStressEnergyFullComponentFlatMinkowskiNoSourcedEinsteinPromotion =
  refl

grDiscreteBianchiFiniteRSupportedUnitYMGRStressEnergyFirstMissingHonest :
  GRDiscreteBianchiFiniteRObligationSurface.factorVecMetricSupportedUnitYMGRStressEnergyFirstMissing
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  FVMetric.missingValuationStressEnergyTensorCandidate
grDiscreteBianchiFiniteRSupportedUnitYMGRStressEnergyFirstMissingHonest = refl

grDiscreteBianchiFiniteRSupportedUnitYMGRStressEnergyRemainingBlocker :
  GRDiscreteBianchiFiniteRObligationSurface.factorVecMetricSupportedUnitYMGRStressEnergyRemainingBlocker
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grDiscreteBianchiFiniteRSupportedUnitYMGRStressEnergyRemainingBlocker = refl

grDiscreteBianchiFiniteRSelectedMetricCompatibilityNextBlocker :
  GRDiscreteBianchiFiniteRObligationSurface.selectedFiniteRMetricCompatibilityNextBlocker
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  missingCarrierConnectionIsLeviCivita
grDiscreteBianchiFiniteRSelectedMetricCompatibilityNextBlocker =
  refl

grDiscreteBianchiFiniteRGate4ConservativeRemainingBlockers :
  GRDiscreteBianchiFiniteRObligationSurface.finiteRGate4ConservativeRemainingBlockers
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  canonicalGRFiniteRGate4RemainingBlockers
grDiscreteBianchiFiniteRGate4ConservativeRemainingBlockers =
  refl

grDiscreteBianchiFiniteRFirstMissingIsFiniteRScalarAlgebra :
  GRDiscreteBianchiFiniteRObligationSurface.firstMissing
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  missingFiniteRScalarAlgebra
grDiscreteBianchiFiniteRFirstMissingIsFiniteRScalarAlgebra = refl

grDiscreteBianchiFiniteRReadinessIsBlocked :
  GRDiscreteBianchiFiniteRObligationSurface.readiness
    canonicalGRDiscreteBianchiFiniteRObligationSurface
  ≡
  blockedBeforeFiniteRConnectionAndJacobiBridge
grDiscreteBianchiFiniteRReadinessIsBlocked = refl

data GRGate4M3U3U4AttemptStatus : Set where
  gate4M3U3U4LocallyStagedHaltedAtSelectedMetricAndW4 :
    GRGate4M3U3U4AttemptStatus

record GRGate4M3U3U4AttemptReceipt : Setω where
  field
    status :
      GRGate4M3U3U4AttemptStatus

    finiteRBianchiSurface :
      GRDiscreteBianchiFiniteRObligationSurface

    m3FiniteRFirstSevenProgress :
      GRFiniteRFirstSevenIngredientProgressReceipt

    m3MetricCompatibilityProgress :
      GRFiniteRMetricCompatibilityProgressReceipt

    u4LeviCivitaBianchiEinsteinProgress :
      GRFiniteRLeviCivitaBianchiEinsteinProgressReceipt

    u4CurvatureRicciEinsteinBoundaryProgress :
      GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt

    u3StressEnergyFullComponentReceipt :
      GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt

    m3ScalarBaseDerivationConnectionAdvanced :
      Bool

    m3ScalarBaseDerivationConnectionAdvancedIsTrue :
      m3ScalarBaseDerivationConnectionAdvanced
      ≡
      true

    u3StressEnergyCandidateReceived :
      Bool

    u3StressEnergyCandidateReceivedIsTrue :
      u3StressEnergyCandidateReceived
      ≡
      true

    u4ZeroTableGeometryAdvanced :
      Bool

    u4ZeroTableGeometryAdvancedIsTrue :
      u4ZeroTableGeometryAdvanced
      ≡
      true

    exactFirstSelectedNonFlatMetricBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatMetricBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatMetricBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    flatVsSelectedNonFlatMetricCompatibilityReceipt :
      GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt

    flatCompatibilityProved :
      Bool

    flatCompatibilityProvedIsTrue :
      flatCompatibilityProved
      ≡
      true

    nonFlatCompatibilityPromoted :
      Bool

    nonFlatCompatibilityPromotedIsTrue :
      nonFlatCompatibilityPromoted
      ≡
      true

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityBase
          canonicalGRSelectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityLambda
          canonicalGRSelectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityMu
          canonicalGRSelectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityNu
          canonicalGRSelectedFiniteRMetricCompatibilityInspection)

    requiredMathForSelectedMetricCompatibility :
      String

    exactPostLocalGeometryBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactPostLocalGeometryBlockerIsStressEnergyCompatibility :
      exactPostLocalGeometryBlocker
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    exactLocalStressEnergyBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    exactLocalStressEnergyBlockerIsMatterReceiptInterface :
      exactLocalStressEnergyBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    exactW4AuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    exactW4AuthorityBlockerIsCandidate256 :
      exactW4AuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    requiredMathForSourceEquation :
      String

    noW4MatterStressEnergyInterfaceReceiptFabricated :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        W4Stress.canonicalW4MatterStressEnergyInterfaceExternalHalt
      ≡
      false

    attemptBoundary :
      List String

canonicalGRGate4M3U3U4AttemptReceipt :
  GRGate4M3U3U4AttemptReceipt
canonicalGRGate4M3U3U4AttemptReceipt =
  record
    { status =
        gate4M3U3U4LocallyStagedHaltedAtSelectedMetricAndW4
    ; finiteRBianchiSurface =
        canonicalGRDiscreteBianchiFiniteRObligationSurface
    ; m3FiniteRFirstSevenProgress =
        canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; m3MetricCompatibilityProgress =
        canonicalGRFiniteRMetricCompatibilityProgressReceipt
    ; u4LeviCivitaBianchiEinsteinProgress =
        canonicalGRFiniteRLeviCivitaBianchiEinsteinProgressReceipt
    ; u4CurvatureRicciEinsteinBoundaryProgress =
        canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
    ; u3StressEnergyFullComponentReceipt =
        canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
    ; m3ScalarBaseDerivationConnectionAdvanced =
        true
    ; m3ScalarBaseDerivationConnectionAdvancedIsTrue =
        refl
    ; u3StressEnergyCandidateReceived =
        true
    ; u3StressEnergyCandidateReceivedIsTrue =
        refl
    ; u4ZeroTableGeometryAdvanced =
        true
    ; u4ZeroTableGeometryAdvancedIsTrue =
        refl
    ; exactFirstSelectedNonFlatMetricBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatMetricBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; flatVsSelectedNonFlatMetricCompatibilityReceipt =
        canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; flatCompatibilityProved =
        GRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt.flatCompatibilityProved
          canonicalGRGate4FlatVsSelectedNonFlatMetricCompatibilityReceipt
    ; flatCompatibilityProvedIsTrue =
        refl
    ; nonFlatCompatibilityPromoted =
        true
    ; nonFlatCompatibilityPromotedIsTrue =
        refl
    ; selectedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; requiredMathForSelectedMetricCompatibility =
        "consume selectedMetricCompatibilityWitness for the selected r0 covariant-derivative table, then prove carrierConnectionIsLeviCivita and the standard Christoffel algebra law for that same metric"
    ; exactPostLocalGeometryBlocker =
        GRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt.postContractionResidualBlocker
          canonicalGRFiniteRCurvatureRicciEinsteinContractionBoundaryReceipt
    ; exactPostLocalGeometryBlockerIsStressEnergyCompatibility =
        refl
    ; exactLocalStressEnergyBlocker =
        GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt.localProgressRemainingBlocker
          canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
    ; exactLocalStressEnergyBlockerIsMatterReceiptInterface =
        refl
    ; exactW4AuthorityBlocker =
        GRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt.w4ExternalHaltFirstBlocker
          canonicalGRFiniteRStressEnergyFullComponentFlatMinkowskiReceipt
    ; exactW4AuthorityBlockerIsCandidate256 =
        refl
    ; requiredMathForSourceEquation =
        "provide W4MatterStressEnergyInterfaceReceipt with Candidate256 calibration authority, bind the local zero-table stress-energy component family to that accepted matter interface, and prove covariant conservation/source coupling for the selected non-flat finite-r connection rather than only the supported flat zero table"
    ; noW4MatterStressEnergyInterfaceReceiptFabricated =
        FVMetric.FactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt.noEinsteinInterfaceReceiptHere
          FVMetric.canonicalFactorVecValuationP2LorentzUnitValuationMatterInterfaceReceipt
    ; noSourcedEinsteinPromotion =
        W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
    ; attemptBoundary =
        "m3 advanced locally: scalar operations, four-chart base, neighbourhood/cell, derivation carrier, bracket/Jacobi witness, and cyclic-shift connection are typed"
        ∷ "m3 flat selected finite-chart compatibility is proved for the bounded identity metric, and the selected non-flat metric instance now consumes selectedMetricCompatibilityWitness"
        ∷ "u4 advanced locally: zero-table Levi-Civita equality, curvature-as-bracket-defect, Jacobi-to-Bianchi, finite-r Bianchi, Ricci contraction, scalar curvature, Einstein tensor, and contracted-Bianchi divergence are typed"
        ∷ "u3 advanced locally: the supported unit p2-time stress-energy component family, source coupling, and covariant-divergence law are threaded through the flat zero-table route"
        ∷ "The exact selected non-flat geometry blocker is missingCarrierConnectionIsLeviCivita after metric compatibility is witnessed"
        ∷ "The exact source-equation blocker is missingStressEnergyCompatibilityForContractedBianchi, locally refined to missingValuationMatterReceiptInterface and W4 Candidate256 calibration authority"
        ∷ "No W4MatterStressEnergyInterfaceReceipt or sourced Einstein equation is fabricated"
        ∷ []
    }

grGate4M3U3U4AttemptSelectedMetricNextBlocker :
  GRGate4M3U3U4AttemptReceipt.exactFirstSelectedNonFlatMetricBlocker
    canonicalGRGate4M3U3U4AttemptReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grGate4M3U3U4AttemptSelectedMetricNextBlocker =
  refl

grGate4M3U3U4AttemptLocalStressEnergyBlocker :
  GRGate4M3U3U4AttemptReceipt.exactLocalStressEnergyBlocker
    canonicalGRGate4M3U3U4AttemptReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grGate4M3U3U4AttemptLocalStressEnergyBlocker =
  refl

grGate4M3U3U4AttemptNoSourcedEinsteinPromotion :
  GRGate4M3U3U4AttemptReceipt.noSourcedEinsteinPromotion
    canonicalGRGate4M3U3U4AttemptReceipt
  ≡
  W4Stress.w4MatterStressEnergyInterfaceExternalHaltNoSourcedEinsteinPromotion
grGate4M3U3U4AttemptNoSourcedEinsteinPromotion =
  refl

data GRGate4SourcedEinsteinFailClosedHandoffStatus : Set where
  gate4SourcedEinsteinAttachmentBlockedByU3W4Handoff :
    GRGate4SourcedEinsteinFailClosedHandoffStatus

record GRGate4SourcedEinsteinFailClosedHandoffReceipt : Setω where
  field
    status :
      GRGate4SourcedEinsteinFailClosedHandoffStatus

    gate4Attempt :
      GRGate4M3U3U4AttemptReceipt

    factorVecDASHIMatterStressEnergyFinalReceipt :
      FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt

    w4MatterStressEnergyGate4HardHaltReceipt :
      W4Stress.W4MatterStressEnergyGate4HardHaltReceipt

    localMatterReceiptInterfaceBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localMatterReceiptInterfaceBlockerIsExact :
      localMatterReceiptInterfaceBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    w4AuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityBlockerIsCandidate256 :
      w4AuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    sourcedEinsteinAttachmentBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    sourcedEinsteinAttachmentBlockerIsStressEnergyCompatibility :
      sourcedEinsteinAttachmentBlocker
      ≡
      missingStressEnergyCompatibilityForContractedBianchi

    noAuthorityBackedStressEnergyTensor :
      Bool

    noAuthorityBackedStressEnergyTensorIsTrue :
      noAuthorityBackedStressEnergyTensor
      ≡
      true

    sourcedEinsteinAttachmentInhabited :
      Bool

    sourcedEinsteinAttachmentInhabitedIsFalse :
      sourcedEinsteinAttachmentInhabited
      ≡
      false

    noW4MatterStressEnergyInterfaceReceiptFabricated :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    noSourcedEinsteinPromotion :
      W4Stress.W4MatterStressEnergyGate4HardHaltReceipt.promotesSourcedEinstein
        w4MatterStressEnergyGate4HardHaltReceipt
      ≡
      false

    handoffBoundary :
      List String

canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt :
  GRGate4SourcedEinsteinFailClosedHandoffReceipt
canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt =
  record
    { status =
        gate4SourcedEinsteinAttachmentBlockedByU3W4Handoff
    ; gate4Attempt =
        canonicalGRGate4M3U3U4AttemptReceipt
    ; factorVecDASHIMatterStressEnergyFinalReceipt =
        FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; w4MatterStressEnergyGate4HardHaltReceipt =
        W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; localMatterReceiptInterfaceBlocker =
        FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.matterReceiptInterfaceRemainingBlocker
          FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; localMatterReceiptInterfaceBlockerIsExact =
        FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.matterReceiptInterfaceRemainingBlockerIsExact
          FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; w4AuthorityBlocker =
        FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.w4AuthorityFirstBlocker
          FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; w4AuthorityBlockerIsCandidate256 =
        FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.w4AuthorityFirstBlockerIsCandidate256
          FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; sourcedEinsteinAttachmentBlocker =
        missingStressEnergyCompatibilityForContractedBianchi
    ; sourcedEinsteinAttachmentBlockerIsStressEnergyCompatibility =
        refl
    ; noAuthorityBackedStressEnergyTensor =
        true
    ; noAuthorityBackedStressEnergyTensorIsTrue =
        refl
    ; sourcedEinsteinAttachmentInhabited =
        false
    ; sourcedEinsteinAttachmentInhabitedIsFalse =
        refl
    ; noW4MatterStressEnergyInterfaceReceiptFabricated =
        FVMetric.FactorVecGate4DASHIMatterStressEnergyFinalReceipt.noEinsteinInterfaceReceiptHere
          FVMetric.canonicalFactorVecGate4DASHIMatterStressEnergyFinalReceipt
    ; noSourcedEinsteinPromotion =
        W4Stress.W4MatterStressEnergyGate4HardHaltReceipt.promotesSourcedEinsteinIsFalse
          W4Stress.canonicalW4MatterStressEnergyGate4HardHaltReceipt
    ; handoffBoundary =
        "u4 consumes the u3 FactorVecGate4DASHIMatterStressEnergyFinalReceipt only as a fail-closed source handoff"
        ∷ "The local stress-energy candidate remains bounded flat staging and stops at missingValuationMatterReceiptInterface"
        ∷ "The W4 hard halt first authority blocker is missingCandidate256CalibrationReceiptForMatterInterface"
        ∷ "No authority-backed StressEnergyTensor, W4MatterStressEnergyInterfaceReceipt, sourced Einstein attachment, or GR promotion is inhabited"
        ∷ []
    }

grGate4SourcedEinsteinFailClosedLocalBlocker :
  GRGate4SourcedEinsteinFailClosedHandoffReceipt.localMatterReceiptInterfaceBlocker
    canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grGate4SourcedEinsteinFailClosedLocalBlocker =
  refl

grGate4SourcedEinsteinFailClosedW4AuthorityBlocker :
  GRGate4SourcedEinsteinFailClosedHandoffReceipt.w4AuthorityBlocker
    canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
  ≡
  W4Stress.missingCandidate256CalibrationReceiptForMatterInterface
grGate4SourcedEinsteinFailClosedW4AuthorityBlocker =
  refl

grGate4SourcedEinsteinAttachmentBlocked :
  GRGate4SourcedEinsteinFailClosedHandoffReceipt.sourcedEinsteinAttachmentInhabited
    canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
  ≡
  false
grGate4SourcedEinsteinAttachmentBlocked =
  refl

------------------------------------------------------------------------
-- Next-wave fail-closed GR surfaces.
--
-- These receipts bind the already-typed local surfaces into the u3/m3/u4
-- tranche names requested by the GR handoff.  They deliberately separate the
-- flat chart, where compatibility is inhabited, from the selected non-flat
-- carrier, where the inspected metric-compatibility slot is still blocked.

data GRNextWaveFailClosedStatus : Set where
  grNextWaveFailClosedSurfacesRecordedNoPromotion :
    GRNextWaveFailClosedStatus

record GRU3DASHIMatterLagrangianCouplingReceiptShape : Setω where
  field
    status :
      GRNextWaveFailClosedStatus

    designReceipt :
      W4Stress.DASHIMatterLagrangianCouplingReceipt

    factorVecLocalReceipt :
      FVMetric.FactorVecDASHIMatterLagrangianCouplingReceipt

    localInterfaceSurface :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface

    localInterfaceOnly :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.localInterfaceOnly
        localInterfaceSurface
      ≡
      true

    localInterfaceConstructsW4MatterField :
      W4Stress.DASHIMatterLagrangianLocalInterfaceSurface.constructsW4MatterField
        localInterfaceSurface
      ≡
      false

    localMatterReceiptInterfaceBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localMatterReceiptInterfaceBlockerIsExact :
      localMatterReceiptInterfaceBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    exactMissingMatterReceiptInterfaceName :
      String

    constructsMatterField :
      Bool

    constructsMatterFieldIsFalse :
      constructsMatterField
      ≡
      false

    constructsStressEnergyTensor :
      Bool

    constructsStressEnergyTensorIsFalse :
      constructsStressEnergyTensor
      ≡
      false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein
      ≡
      false

    noW4MatterStressEnergyInterfaceReceiptFabricated :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    u3Boundary :
      List String

canonicalGRU3DASHIMatterLagrangianCouplingReceiptShape :
  GRU3DASHIMatterLagrangianCouplingReceiptShape
canonicalGRU3DASHIMatterLagrangianCouplingReceiptShape =
  record
    { status =
        grNextWaveFailClosedSurfacesRecordedNoPromotion
    ; designReceipt =
        W4Stress.canonicalDASHIMatterLagrangianCouplingReceipt
    ; factorVecLocalReceipt =
        FVMetric.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceSurface =
        FVMetric.FactorVecDASHIMatterLagrangianCouplingReceipt.localInterfaceSurface
          FVMetric.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceOnly =
        FVMetric.FactorVecDASHIMatterLagrangianCouplingReceipt.localInterfaceOnly
          FVMetric.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; localInterfaceConstructsW4MatterField =
        FVMetric.FactorVecDASHIMatterLagrangianCouplingReceipt.localInterfaceConstructsW4MatterField
          FVMetric.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; localMatterReceiptInterfaceBlocker =
        FVMetric.FactorVecDASHIMatterLagrangianCouplingReceipt.localCompatibilityRemainingBlocker
          FVMetric.canonicalFactorVecDASHIMatterLagrangianCouplingReceipt
    ; localMatterReceiptInterfaceBlockerIsExact =
        refl
    ; exactMissingMatterReceiptInterfaceName =
        "FactorVecDiscreteMetricTensorSurface.missingValuationMatterReceiptInterface"
    ; constructsMatterField =
        false
    ; constructsMatterFieldIsFalse =
        refl
    ; constructsStressEnergyTensor =
        false
    ; constructsStressEnergyTensorIsFalse =
        refl
    ; promotesSourcedEinstein =
        false
    ; promotesSourcedEinsteinIsFalse =
        refl
    ; noW4MatterStressEnergyInterfaceReceiptFabricated =
        EEC.w4MatterStressEnergyInterfaceReceiptImpossibleHere
    ; u3Boundary =
        "u3 binds DASHIMatterLagrangianCouplingReceipt through a typed local interface surface"
        ∷ "The local FactorVec receipt still stops exactly at missingValuationMatterReceiptInterface"
        ∷ "The local interface surface is explicitly local-only and constructs no W4 MatterField"
        ∷ "No MatterField, authority-backed StressEnergyTensor, W4 matter receipt, or sourced Einstein law is constructed"
        ∷ []
    }

record GRM3SelectedFiniteRCarrierBindingReceipt : Setω where
  field
    status :
      GRNextWaveFailClosedStatus

    firstSevenIngredientProgress :
      GRFiniteRFirstSevenIngredientProgressReceipt

    selectedMetricSurface :
      SelectedMetric.GRSelectedNonFlatMetricInstanceSurface

    selectedFiniteRBaseCarrier :
      Set

    selectedFiniteRBaseCarrierIsSelectedMetricBase :
      selectedFiniteRBaseCarrier
      ≡
      SelectedMetric.GRSelectedFiniteRBase

    selectedMetricDependency :
      NFScalar.GRSelectedNonFlatMetricDependency
        NFScalar.canonicalGRFiniteRCarrierScalarOperations

    selectedMetricDependencyIsCanonical :
      Bool

    selectedMetricDependencyIsCanonicalTrue :
      selectedMetricDependencyIsCanonical
      ≡
      true

    selectedCarrierBindingStaged :
      Bool

    selectedCarrierBindingStagedIsTrue :
      selectedCarrierBindingStaged
      ≡
      true

    postBindingFirstSelectedMetricBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    postBindingFirstSelectedMetricBlockerIsMetricCompatibility :
      postBindingFirstSelectedMetricBlocker
      ≡
      missingMetricCompatibility

    selectedLeviCivitaPromoted :
      Bool

    selectedLeviCivitaPromotedIsFalse :
      selectedLeviCivitaPromoted
      ≡
      false

    m3Boundary :
      List String

canonicalGRM3SelectedFiniteRCarrierBindingReceipt :
  GRM3SelectedFiniteRCarrierBindingReceipt
canonicalGRM3SelectedFiniteRCarrierBindingReceipt =
  record
    { status =
        grNextWaveFailClosedSurfacesRecordedNoPromotion
    ; firstSevenIngredientProgress =
        canonicalGRFiniteRFirstSevenIngredientProgressReceipt
    ; selectedMetricSurface =
        SelectedMetric.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; selectedFiniteRBaseCarrier =
        SelectedMetric.GRSelectedFiniteRBase
    ; selectedFiniteRBaseCarrierIsSelectedMetricBase =
        refl
    ; selectedMetricDependency =
        SelectedMetric.selectedGRNonFlatMetricDependency
    ; selectedMetricDependencyIsCanonical =
        true
    ; selectedMetricDependencyIsCanonicalTrue =
        refl
    ; selectedCarrierBindingStaged =
        true
    ; selectedCarrierBindingStagedIsTrue =
        refl
    ; postBindingFirstSelectedMetricBlocker =
        missingMetricCompatibility
    ; postBindingFirstSelectedMetricBlockerIsMetricCompatibility =
        refl
    ; selectedLeviCivitaPromoted =
        false
    ; selectedLeviCivitaPromotedIsFalse =
        refl
    ; m3Boundary =
        "m3 binds the selected finite-r base carrier through GRSelectedNonFlatMetricInstance"
        ∷ "The selected metric dependency is canonical and typed over canonicalGRFiniteRCarrierScalarOperations"
        ∷ "The binding does not promote the selected connection to Levi-Civita; the first selected-metric blocker remains missingMetricCompatibility"
        ∷ []
    }

record GRU4FlatChartMetricCompatibilitySplitReceipt : Setω where
  field
    status :
      GRNextWaveFailClosedStatus

    flatLeviCivitaClosure :
      GRFlatMinkowskiFiniteRLeviCivitaClosure

    flatCompatibilityProved :
      Bool

    flatCompatibilityProvedIsTrue :
      flatCompatibilityProved
      ≡
      true

    flatMetricCompatibilityWitness :
      (base : ML.MinkowskiCarrier) →
      GRMetricCompatibleLeviCivitaCarrierObligation.metricCompatibility
        canonicalGRFlatConstantMetricCompatibleCarrier
        (flatConstantMetricAt base)
        (flatConstantConnectionAt base)

    selectedFiniteRMetricCompatibilityInspection :
      GRSelectedFiniteRMetricCompatibilityInspection

    upper6SelectedChristoffelAttempt :
      GRGate4Upper6SelectedChristoffelAttemptReceipt

    upper6SelectedChristoffelAttemptStaged :
      Bool

    upper6SelectedChristoffelAttemptStagedIsTrue :
      upper6SelectedChristoffelAttemptStaged
      ≡
      true

    upper6SelectedLeviCivitaPromoted :
      Bool

    upper6SelectedLeviCivitaPromotedIsFalse :
      upper6SelectedLeviCivitaPromoted
      ≡
      false

    nonFlatCompatibilityStaged :
      Bool

    nonFlatCompatibilityStagedIsTrue :
      nonFlatCompatibilityStaged
      ≡
      true

    nonFlatCompatibilityPromoted :
      Bool

    nonFlatCompatibilityPromotedIsTrue :
      nonFlatCompatibilityPromoted
      ≡
      true

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityBase
          selectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityLambda
          selectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityMu
          selectedFiniteRMetricCompatibilityInspection)
        (GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityNu
          selectedFiniteRMetricCompatibilityInspection)

    nonFlatFirstBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    nonFlatFirstBlockerIsCarrierConnectionIsLeviCivita :
      nonFlatFirstBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    nonFlatLeviCivitaChainBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    nonFlatLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita :
      nonFlatLeviCivitaChainBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    noNonFlatLeviCivitaClosureFabricated :
      Bool

    noNonFlatLeviCivitaClosureFabricatedIsTrue :
      noNonFlatLeviCivitaClosureFabricated
      ≡
      true

    u4Boundary :
      List String

canonicalGRU4FlatChartMetricCompatibilitySplitReceipt :
  GRU4FlatChartMetricCompatibilitySplitReceipt
canonicalGRU4FlatChartMetricCompatibilitySplitReceipt =
  record
    { status =
        grNextWaveFailClosedSurfacesRecordedNoPromotion
    ; flatLeviCivitaClosure =
        canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure
    ; flatCompatibilityProved =
        true
    ; flatCompatibilityProvedIsTrue =
        refl
    ; flatMetricCompatibilityWitness =
        GRFlatMinkowskiFiniteRLeviCivitaClosure.carrierMetricCompatibilityWitness
          canonicalGRFlatMinkowskiFiniteRLeviCivitaClosure
    ; selectedFiniteRMetricCompatibilityInspection =
        canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; upper6SelectedChristoffelAttempt =
        canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; upper6SelectedChristoffelAttemptStaged =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaAttemptStaged
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; upper6SelectedChristoffelAttemptStagedIsTrue =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaAttemptStagedIsTrue
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; upper6SelectedLeviCivitaPromoted =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaPromoted
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; upper6SelectedLeviCivitaPromotedIsFalse =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaPromotedIsFalse
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; nonFlatCompatibilityStaged =
        true
    ; nonFlatCompatibilityStagedIsTrue =
        refl
    ; nonFlatCompatibilityPromoted =
        true
    ; nonFlatCompatibilityPromotedIsTrue =
        refl
    ; selectedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; nonFlatFirstBlocker =
        missingCarrierConnectionIsLeviCivita
    ; nonFlatFirstBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; nonFlatLeviCivitaChainBlocker =
        missingCarrierConnectionIsLeviCivita
    ; nonFlatLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; noNonFlatLeviCivitaClosureFabricated =
        true
    ; noNonFlatLeviCivitaClosureFabricatedIsTrue =
        refl
    ; u4Boundary =
        "u4 split: flat chart metric compatibility is proved on the Minkowski/unit-connection carrier"
        ∷ "u4 upper6: selected Christoffel-from-metric is attempted at selectedBase0/radial/radial/radial and blocks on odd numerator r1 with no half witness"
        ∷ "u4 split: selected non-flat metric compatibility is staged and witnessed by SelectedMetric.selectedMetricCompatibilityWitness"
        ∷ "nonFlatCompatibilityPromoted=true; the next Levi-Civita-chain blocker is missingCarrierConnectionIsLeviCivita"
        ∷ "The split does not fabricate non-flat Levi-Civita closure, W4 authority, or sourced Einstein promotion"
        ∷ []
    }

record GRNextWaveFailClosedSurfaceReceipt : Setω where
  field
    status :
      GRNextWaveFailClosedStatus

    u3DASHIMatterLagrangianCouplingReceiptShape :
      GRU3DASHIMatterLagrangianCouplingReceiptShape

    m3SelectedFiniteRCarrierBinding :
      GRM3SelectedFiniteRCarrierBindingReceipt

    u4FlatChartMetricCompatibilitySplit :
      GRU4FlatChartMetricCompatibilitySplitReceipt

    u4Upper6SelectedChristoffelAttempt :
      GRGate4Upper6SelectedChristoffelAttemptReceipt

    gate4FailClosedHandoff :
      GRGate4SourcedEinsteinFailClosedHandoffReceipt

    u3LocalMatterBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    u3LocalMatterBlockerIsMissingValuationMatterReceiptInterface :
      u3LocalMatterBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    m3SelectedCarrierBound :
      Bool

    m3SelectedCarrierBoundIsTrue :
      m3SelectedCarrierBound
      ≡
      true

    u4FlatCompatibilityProved :
      Bool

    u4FlatCompatibilityProvedIsTrue :
      u4FlatCompatibilityProved
      ≡
      true

    u4NonFlatCompatibilityStaged :
      Bool

    u4NonFlatCompatibilityStagedIsTrue :
      u4NonFlatCompatibilityStaged
      ≡
      true

    u4Upper6SelectedLeviCivitaPromoted :
      Bool

    u4Upper6SelectedLeviCivitaPromotedIsFalse :
      u4Upper6SelectedLeviCivitaPromoted
      ≡
      false

    noSourcedEinsteinPromotion :
      GRGate4SourcedEinsteinFailClosedHandoffReceipt.sourcedEinsteinAttachmentInhabited
        gate4FailClosedHandoff
      ≡
      false

    nextWaveBoundary :
      List String

canonicalGRNextWaveFailClosedSurfaceReceipt :
  GRNextWaveFailClosedSurfaceReceipt
canonicalGRNextWaveFailClosedSurfaceReceipt =
  record
    { status =
        grNextWaveFailClosedSurfacesRecordedNoPromotion
    ; u3DASHIMatterLagrangianCouplingReceiptShape =
        canonicalGRU3DASHIMatterLagrangianCouplingReceiptShape
    ; m3SelectedFiniteRCarrierBinding =
        canonicalGRM3SelectedFiniteRCarrierBindingReceipt
    ; u4FlatChartMetricCompatibilitySplit =
        canonicalGRU4FlatChartMetricCompatibilitySplitReceipt
    ; u4Upper6SelectedChristoffelAttempt =
        canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; gate4FailClosedHandoff =
        canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
    ; u3LocalMatterBlocker =
        GRU3DASHIMatterLagrangianCouplingReceiptShape.localMatterReceiptInterfaceBlocker
          canonicalGRU3DASHIMatterLagrangianCouplingReceiptShape
    ; u3LocalMatterBlockerIsMissingValuationMatterReceiptInterface =
        refl
    ; m3SelectedCarrierBound =
        GRM3SelectedFiniteRCarrierBindingReceipt.selectedCarrierBindingStaged
          canonicalGRM3SelectedFiniteRCarrierBindingReceipt
    ; m3SelectedCarrierBoundIsTrue =
        refl
    ; u4FlatCompatibilityProved =
        GRU4FlatChartMetricCompatibilitySplitReceipt.flatCompatibilityProved
          canonicalGRU4FlatChartMetricCompatibilitySplitReceipt
    ; u4FlatCompatibilityProvedIsTrue =
        refl
    ; u4NonFlatCompatibilityStaged =
        GRU4FlatChartMetricCompatibilitySplitReceipt.nonFlatCompatibilityStaged
          canonicalGRU4FlatChartMetricCompatibilitySplitReceipt
    ; u4NonFlatCompatibilityStagedIsTrue =
        refl
    ; u4Upper6SelectedLeviCivitaPromoted =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaPromoted
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; u4Upper6SelectedLeviCivitaPromotedIsFalse =
        GRGate4Upper6SelectedChristoffelAttemptReceipt.selectedLeviCivitaPromotedIsFalse
          canonicalGRGate4Upper6SelectedChristoffelAttemptReceipt
    ; noSourcedEinsteinPromotion =
        refl
    ; nextWaveBoundary =
        "Next-wave GR fail-closed surface binds u3, m3, and u4 without changing the promotion boundary"
        ∷ "u3 records the DASHI matter-Lagrangian design receipt shape and exact missingValuationMatterReceiptInterface blocker"
        ∷ "m3 binds the selected finite-r carrier while selected metric compatibility is witnessed"
        ∷ "u4 records flatCompatibilityProved=true and nonFlatCompatibilityStaged=true as separate fields"
        ∷ "u4 upper6 records the selected Christoffel/Levi-Civita attempt and leaves selectedLeviCivitaPromoted=false"
        ∷ "No non-flat Levi-Civita closure, W4 authority, sourced Einstein law, or GR/QFT promotion is produced"
        ∷ []
    }

grNextWaveU3LocalMatterBlocker :
  GRNextWaveFailClosedSurfaceReceipt.u3LocalMatterBlocker
    canonicalGRNextWaveFailClosedSurfaceReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grNextWaveU3LocalMatterBlocker =
  refl

grNextWaveM3SelectedCarrierBound :
  GRNextWaveFailClosedSurfaceReceipt.m3SelectedCarrierBound
    canonicalGRNextWaveFailClosedSurfaceReceipt
  ≡
  true
grNextWaveM3SelectedCarrierBound =
  refl

grNextWaveU4FlatCompatibilityProved :
  GRNextWaveFailClosedSurfaceReceipt.u4FlatCompatibilityProved
    canonicalGRNextWaveFailClosedSurfaceReceipt
  ≡
  true
grNextWaveU4FlatCompatibilityProved =
  refl

grNextWaveU4NonFlatCompatibilityStaged :
  GRNextWaveFailClosedSurfaceReceipt.u4NonFlatCompatibilityStaged
    canonicalGRNextWaveFailClosedSurfaceReceipt
  ≡
  true
grNextWaveU4NonFlatCompatibilityStaged =
  refl

grNextWaveU4Upper6SelectedLeviCivitaNotPromoted :
  GRNextWaveFailClosedSurfaceReceipt.u4Upper6SelectedLeviCivitaPromoted
    canonicalGRNextWaveFailClosedSurfaceReceipt
  ≡
  false
grNextWaveU4Upper6SelectedLeviCivitaNotPromoted =
  refl

------------------------------------------------------------------------
-- Current-wave u3/u4/m3 GR constructor and Levi-Civita attempt surfaces.
--
-- These receipts add the explicit constructor and Levi-Civita/torsion-free
-- shapes requested by the current GR tranche.  They consume the local
-- zero-table/flat-chart witnesses already present, consume the selected
-- non-flat metric-compatibility witness, and keep the W4 source boundary
-- unchanged.

data GRCurrentWaveFailClosedStatus : Set where
  grCurrentWaveConstructorLeviCivitaAttemptsRecordedNoPromotion :
    GRCurrentWaveFailClosedStatus

selectedPlaceholderChristoffelLowerSymmetry :
  (connection : SelectedMetric.GRSelectedConnectionCarrier) →
  (lambda mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  SelectedMetric.selectedChristoffelSymbol connection lambda mu nu
  ≡
  SelectedMetric.selectedChristoffelSymbol connection lambda nu mu
selectedPlaceholderChristoffelLowerSymmetry _ _ _ _ =
  refl

record GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt : Setω where
  field
    status :
      GRCurrentWaveFailClosedStatus

    selectedMetricSurface :
      SelectedMetric.GRSelectedNonFlatMetricInstanceSurface

    selectedMetricInspection :
      GRSelectedFiniteRMetricCompatibilityInspection

    upper6DoubledChristoffelIntegralAttempt :
      GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt

    selectedMetricDependency :
      NFScalar.GRSelectedNonFlatMetricDependency
        NFScalar.canonicalGRFiniteRCarrierScalarOperations

    selectedLeviCivitaCandidateConnection :
      SelectedMetric.GRSelectedConnectionCarrier

    selectedChristoffelLowerSymmetry :
      (lambda mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedChristoffelSymbol
        selectedLeviCivitaCandidateConnection
        lambda
        mu
        nu
      ≡
      SelectedMetric.selectedChristoffelSymbol
        selectedLeviCivitaCandidateConnection
        lambda
        nu
        mu

    torsionFreeAttemptStaged :
      Bool

    torsionFreeAttemptStagedIsTrue :
      torsionFreeAttemptStaged
      ≡
      true

    inspectedCompatibilityBase :
      SelectedMetric.GRSelectedFiniteRBase

    inspectedCompatibilityLambda :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCompatibilityMu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCompatibilityNu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCovariantDerivativeIsR0 :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection inspectedCompatibilityBase)
        (SelectedMetric.selectedMetricAt inspectedCompatibilityBase)
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu
      ≡
      NFScalar.r0

    inspectedMetricCompatibilityShape :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedCompatibilityBase
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedCompatibilityBase
        inspectedCompatibilityLambda
        inspectedCompatibilityMu
        inspectedCompatibilityNu

    christoffelFromMetricPromoted :
      Bool

    christoffelFromMetricPromotedIsFalse :
      christoffelFromMetricPromoted
      ≡
      false

    doubledChristoffelIntegralRouteCloses :
      Bool

    doubledChristoffelIntegralRouteClosesIsFalse :
      doubledChristoffelIntegralRouteCloses
      ≡
      false

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    exactMetricCompatibilityBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactMetricCompatibilityBlockerIsCarrierConnectionIsLeviCivita :
      exactMetricCompatibilityBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactLeviCivitaChainBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita :
      exactLeviCivitaChainBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactStandardLawBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactStandardLawBlockerIsStandardLeviCivitaAlgebraLaw :
      exactStandardLawBlocker
      ≡
      missingStandardLeviCivitaAlgebraLaw

    exactSixTermCancellationBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactSixTermCancellationBlockerIsSixTermCancellation :
      exactSixTermCancellationBlocker
      ≡
      missingSixTermRicciIdentityCancellation

    attemptBoundary :
      List String

canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt :
  GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt =
  record
    { status =
        grCurrentWaveConstructorLeviCivitaAttemptsRecordedNoPromotion
    ; selectedMetricSurface =
        SelectedMetric.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; selectedMetricInspection =
        canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; upper6DoubledChristoffelIntegralAttempt =
        canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
    ; selectedMetricDependency =
        SelectedMetric.selectedGRNonFlatMetricDependency
    ; selectedLeviCivitaCandidateConnection =
        SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0
    ; selectedChristoffelLowerSymmetry =
        selectedPlaceholderChristoffelLowerSymmetry
          (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
    ; torsionFreeAttemptStaged =
        true
    ; torsionFreeAttemptStagedIsTrue =
        refl
    ; inspectedCompatibilityBase =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityBase
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedCompatibilityLambda =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityLambda
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedCompatibilityMu =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityMu
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedCompatibilityNu =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedCompatibilityNu
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedCovariantDerivativeIsR0 =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedCovariantDerivativeIsR0
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; inspectedMetricCompatibilityShape =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityShape
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; selectedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; christoffelFromMetricPromoted =
        false
    ; christoffelFromMetricPromotedIsFalse =
        refl
    ; doubledChristoffelIntegralRouteCloses =
        GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt.integralRouteClosesSelectedChristoffel
          canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
    ; doubledChristoffelIntegralRouteClosesIsFalse =
        GRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt.integralRouteClosesSelectedChristoffelIsFalse
          canonicalGRU4Upper6DoubledChristoffelIntegralMetricCompatibilityReceipt
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactMetricCompatibilityBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactMetricCompatibilityBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactLeviCivitaChainBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactLeviCivitaChainBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactStandardLawBlocker =
        missingStandardLeviCivitaAlgebraLaw
    ; exactStandardLawBlockerIsStandardLeviCivitaAlgebraLaw =
        refl
    ; exactSixTermCancellationBlocker =
        missingSixTermRicciIdentityCancellation
    ; exactSixTermCancellationBlockerIsSixTermCancellation =
        refl
    ; attemptBoundary =
        "u4 current-wave attempt records the selected placeholder Christoffel table as lower-index symmetric, so the torsion-free shape is staged"
        ∷ "The upper6 doubled-Christoffel route records 2 * Gamma = numerator directly, but the inspected selected slot still reduces to r0 = r1 for that equation"
        ∷ "The same selected non-flat metric dependency now has an r0 covariant metric derivative at the inspected slot"
        ∷ "Therefore the selected metric-compatibility obligation is witnessed by SelectedMetric.selectedMetricCompatibilityWitness"
        ∷ "Christoffel-from-metric, carrierConnectionIsLeviCivita, standard Levi-Civita algebra law, and six-term cancellation are not promoted"
        ∷ "The exact first selected non-flat blocker is now missingCarrierConnectionIsLeviCivita"
        ∷ []
    }

grU4SelectedLeviCivitaAttemptTorsionFreeStaged :
  GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.torsionFreeAttemptStaged
    canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
  ≡
  true
grU4SelectedLeviCivitaAttemptTorsionFreeStaged =
  refl

grU4SelectedLeviCivitaAttemptNextBlocker :
  GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.exactMetricCompatibilityBlocker
    canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grU4SelectedLeviCivitaAttemptNextBlocker =
  refl

grU4SelectedLeviCivitaAttemptNoLeviCivitaPromotion :
  GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedConnectionIsLeviCivitaPromoted
    canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
  ≡
  false
grU4SelectedLeviCivitaAttemptNoLeviCivitaPromotion =
  refl

record GRCurrentWaveM3U3U4FailClosedSurfaceReceipt : Setω where
  field
    status :
      GRCurrentWaveFailClosedStatus

    previousNextWaveSurface :
      GRNextWaveFailClosedSurfaceReceipt

    u3ConsumableStressEnergyConstructor :
      FVMetric.FactorVecGate4ConsumableStressEnergyConstructorReceipt

    u4SelectedLeviCivitaAttempt :
      GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt

    u3ConstructorRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    u3ConstructorRemainingBlockerIsMatterReceiptInterface :
      u3ConstructorRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    m3SelectedCarrierBound :
      Bool

    m3SelectedCarrierBoundIsTrue :
      m3SelectedCarrierBound
      ≡
      true

    u4TorsionFreeAttemptStaged :
      Bool

    u4TorsionFreeAttemptStagedIsTrue :
      u4TorsionFreeAttemptStaged
      ≡
      true

    u4MetricCompatibilityPromoted :
      Bool

    u4MetricCompatibilityPromotedIsTrue :
      u4MetricCompatibilityPromoted
      ≡
      true

    u4LeviCivitaPromoted :
      Bool

    u4LeviCivitaPromotedIsFalse :
      u4LeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactW4AuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    exactW4AuthorityBlockerIsCandidate256 :
      exactW4AuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noW4MatterStressEnergyInterfaceReceiptFabricated :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    noSourcedEinsteinPromotion :
      Bool

    noSourcedEinsteinPromotionIsTrue :
      noSourcedEinsteinPromotion
      ≡
      true

    currentWaveBoundary :
      List String

canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt :
  GRCurrentWaveM3U3U4FailClosedSurfaceReceipt
canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt =
  record
    { status =
        grCurrentWaveConstructorLeviCivitaAttemptsRecordedNoPromotion
    ; previousNextWaveSurface =
        canonicalGRNextWaveFailClosedSurfaceReceipt
    ; u3ConsumableStressEnergyConstructor =
        FVMetric.canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; u4SelectedLeviCivitaAttempt =
        canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; u3ConstructorRemainingBlocker =
        FVMetric.FactorVecGate4ConsumableStressEnergyConstructorReceipt.remainingMatterInterfaceBlocker
          FVMetric.canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; u3ConstructorRemainingBlockerIsMatterReceiptInterface =
        refl
    ; m3SelectedCarrierBound =
        GRNextWaveFailClosedSurfaceReceipt.m3SelectedCarrierBound
          canonicalGRNextWaveFailClosedSurfaceReceipt
    ; m3SelectedCarrierBoundIsTrue =
        refl
    ; u4TorsionFreeAttemptStaged =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.torsionFreeAttemptStaged
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; u4TorsionFreeAttemptStagedIsTrue =
        refl
    ; u4MetricCompatibilityPromoted =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedMetricCompatibilityPromoted
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; u4MetricCompatibilityPromotedIsTrue =
        refl
    ; u4LeviCivitaPromoted =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedConnectionIsLeviCivitaPromoted
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; u4LeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.exactMetricCompatibilityBlocker
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; exactW4AuthorityBlocker =
        FVMetric.FactorVecGate4ConsumableStressEnergyConstructorReceipt.w4AuthorityFirstBlocker
          FVMetric.canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; exactW4AuthorityBlockerIsCandidate256 =
        FVMetric.FactorVecGate4ConsumableStressEnergyConstructorReceipt.w4AuthorityFirstBlockerIsCandidate256
          FVMetric.canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; noW4MatterStressEnergyInterfaceReceiptFabricated =
        FVMetric.FactorVecGate4ConsumableStressEnergyConstructorReceipt.noEinsteinInterfaceReceiptHere
          FVMetric.canonicalFactorVecGate4ConsumableStressEnergyConstructorReceipt
    ; noSourcedEinsteinPromotion =
        true
    ; noSourcedEinsteinPromotionIsTrue =
        refl
    ; currentWaveBoundary =
        "Current-wave GR aggregate consumes the explicit u3 local stress-energy constructor surface"
        ∷ "m3 selected finite-r carrier binding remains true from canonicalGRNextWaveFailClosedSurfaceReceipt"
        ∷ "u4 stages only the torsion-free shape of the selected placeholder Christoffel table"
        ∷ "Selected non-flat metric compatibility is witnessed; missingCarrierConnectionIsLeviCivita is the first true geometry blocker"
        ∷ "The source side remains blocked by missingValuationMatterReceiptInterface and W4 Candidate256 authority"
        ∷ "No selected non-flat Levi-Civita proof, sourced Einstein law, W4 receipt, or GR/QFT promotion is constructed"
        ∷ []
    }

grCurrentWaveGRU3ConstructorStillBlocked :
  GRCurrentWaveM3U3U4FailClosedSurfaceReceipt.u3ConstructorRemainingBlocker
    canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
  ≡
  FVMetric.missingValuationMatterReceiptInterface
grCurrentWaveGRU3ConstructorStillBlocked =
  refl

grCurrentWaveGRU4MetricCompatibilityNextBlocker :
  GRCurrentWaveM3U3U4FailClosedSurfaceReceipt.exactFirstSelectedNonFlatBlocker
    canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grCurrentWaveGRU4MetricCompatibilityNextBlocker =
  refl

grCurrentWaveGRNoSourcedEinsteinPromotion :
  GRCurrentWaveM3U3U4FailClosedSurfaceReceipt.noSourcedEinsteinPromotion
    canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
  ≡
  true
grCurrentWaveGRNoSourcedEinsteinPromotion =
  refl

data GRMiddle6NextIterationFailClosedStatus : Set where
  grMiddle6NextIterationSelectedMetricAndMatterInterfaceBlocked :
    GRMiddle6NextIterationFailClosedStatus

record GRMiddle6NextIterationFailClosedReceipt : Setω where
  field
    status :
      GRMiddle6NextIterationFailClosedStatus

    currentWaveSurface :
      GRCurrentWaveM3U3U4FailClosedSurfaceReceipt

    selectedLeviCivitaAttempt :
      GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt

    matterInterfaceBinding :
      W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt

    selectedChristoffelLowerSymmetryStaged :
      Bool

    selectedChristoffelLowerSymmetryStagedIsTrue :
      selectedChristoffelLowerSymmetryStaged
      ≡
      true

    torsionFreeCanAdvanceAsShape :
      Bool

    torsionFreeCanAdvanceAsShapeIsTrue :
      torsionFreeCanAdvanceAsShape
      ≡
      true

    christoffelFromMetricCanAdvance :
      Bool

    christoffelFromMetricCanAdvanceIsFalse :
      christoffelFromMetricCanAdvance
      ≡
      false

    leviCivitaCanAdvance :
      Bool

    leviCivitaCanAdvanceIsFalse :
      leviCivitaCanAdvance
      ≡
      false

    metricCompatibilityCanAdvance :
      Bool

    metricCompatibilityCanAdvanceIsTrue :
      metricCompatibilityCanAdvance
      ≡
      true

    inspectedCovariantDerivativeIsR0 :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection
          (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityBase
            selectedLeviCivitaAttempt))
        (SelectedMetric.selectedMetricAt
          (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityBase
            selectedLeviCivitaAttempt))
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityLambda
          selectedLeviCivitaAttempt)
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityMu
          selectedLeviCivitaAttempt)
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityNu
          selectedLeviCivitaAttempt)
      ≡
      NFScalar.r0

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityBase
          selectedLeviCivitaAttempt)
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityLambda
          selectedLeviCivitaAttempt)
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityMu
          selectedLeviCivitaAttempt)
        (GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCompatibilityNu
          selectedLeviCivitaAttempt)

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    matterLagrangianInterfaceLocallyBindable :
      Bool

    matterLagrangianInterfaceLocallyBindableIsTrue :
      matterLagrangianInterfaceLocallyBindable
      ≡
      true

    matterLagrangianInterfaceAuthorityBindable :
      Bool

    matterLagrangianInterfaceAuthorityBindableIsFalse :
      matterLagrangianInterfaceAuthorityBindable
      ≡
      false

    w4AuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityBlockerIsCandidate256 :
      w4AuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    noW4MatterStressEnergyInterfaceReceiptFabricated :
      EEC.W4MatterStressEnergyInterfaceReceipt →
      ⊥

    sourcedEinsteinCanAdvance :
      Bool

    sourcedEinsteinCanAdvanceIsFalse :
      sourcedEinsteinCanAdvance
      ≡
      false

    nextIterationBoundary :
      List String

canonicalGRMiddle6NextIterationFailClosedReceipt :
  GRMiddle6NextIterationFailClosedReceipt
canonicalGRMiddle6NextIterationFailClosedReceipt =
  record
    { status =
        grMiddle6NextIterationSelectedMetricAndMatterInterfaceBlocked
    ; currentWaveSurface =
        canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
    ; selectedLeviCivitaAttempt =
        canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; matterInterfaceBinding =
        W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; selectedChristoffelLowerSymmetryStaged =
        true
    ; selectedChristoffelLowerSymmetryStagedIsTrue =
        refl
    ; torsionFreeCanAdvanceAsShape =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.torsionFreeAttemptStaged
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; torsionFreeCanAdvanceAsShapeIsTrue =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.torsionFreeAttemptStagedIsTrue
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; christoffelFromMetricCanAdvance =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.christoffelFromMetricPromoted
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; christoffelFromMetricCanAdvanceIsFalse =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.christoffelFromMetricPromotedIsFalse
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; leviCivitaCanAdvance =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedConnectionIsLeviCivitaPromoted
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; leviCivitaCanAdvanceIsFalse =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedConnectionIsLeviCivitaPromotedIsFalse
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; metricCompatibilityCanAdvance =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedMetricCompatibilityPromoted
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; metricCompatibilityCanAdvanceIsTrue =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedMetricCompatibilityPromotedIsTrue
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; inspectedCovariantDerivativeIsR0 =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.inspectedCovariantDerivativeIsR0
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; selectedMetricCompatibilityWitness =
        GRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt.selectedMetricCompatibilityWitness
          canonicalGRU4SelectedLeviCivitaNonFlatCompatibilityAttemptReceipt
    ; exactFirstSelectedNonFlatBlocker =
        GRCurrentWaveM3U3U4FailClosedSurfaceReceipt.exactFirstSelectedNonFlatBlocker
          canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        GRCurrentWaveM3U3U4FailClosedSurfaceReceipt.exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita
          canonicalGRCurrentWaveM3U3U4FailClosedSurfaceReceipt
    ; matterLagrangianInterfaceLocallyBindable =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.matterLagrangianInterfaceLocallyBindable
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; matterLagrangianInterfaceLocallyBindableIsTrue =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.matterLagrangianInterfaceLocallyBindableIsTrue
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; matterLagrangianInterfaceAuthorityBindable =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.matterLagrangianInterfaceAuthorityBindable
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; matterLagrangianInterfaceAuthorityBindableIsFalse =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.matterLagrangianInterfaceAuthorityBindableIsFalse
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; w4AuthorityBlocker =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; w4AuthorityBlockerIsCandidate256 =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.firstAuthorityInterfaceBlockerIsCandidate256
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; noW4MatterStressEnergyInterfaceReceiptFabricated =
        W4Stress.W4MatterStressEnergyMiddle6InterfaceBindingReceipt.noEinsteinInterfaceReceiptHere
          W4Stress.canonicalW4MatterStressEnergyMiddle6InterfaceBindingReceipt
    ; sourcedEinsteinCanAdvance =
        false
    ; sourcedEinsteinCanAdvanceIsFalse =
        refl
    ; nextIterationBoundary =
        "middle6 next-iteration records the selected Christoffel lower-index symmetry and torsion-free shape as staged"
        ∷ "Metric compatibility advances for the selected non-flat metric via the selected r0 witness; Christoffel-from-metric and Levi-Civita promotion remain blocked"
        ∷ "The next selected geometry blocker is missingCarrierConnectionIsLeviCivita"
        ∷ "The DASHI matter-lagrangian interface is locally bindable only through the fail-closed W4 middle6 interface binding receipt"
        ∷ "Authority binding, W4 stress-energy, and sourced Einstein remain blocked by Candidate256/W4MatterStressEnergyInterfaceReceipt authority"
        ∷ []
    }

grMiddle6NextIterationMetricCompatibilityCanAdvance :
  GRMiddle6NextIterationFailClosedReceipt.metricCompatibilityCanAdvance
    canonicalGRMiddle6NextIterationFailClosedReceipt
  ≡
  true
grMiddle6NextIterationMetricCompatibilityCanAdvance =
  refl

grMiddle6NextIterationMatterInterfaceAuthorityCannotBind :
  GRMiddle6NextIterationFailClosedReceipt.matterLagrangianInterfaceAuthorityBindable
    canonicalGRMiddle6NextIterationFailClosedReceipt
  ≡
  false
grMiddle6NextIterationMatterInterfaceAuthorityCannotBind =
  refl

------------------------------------------------------------------------
-- Lower6 doubled-Christoffel integral metric-compatibility attempt.
--
-- The selected metric API currently exposes a placeholder connection whose
-- covariant derivative ignores Christoffel data.  That obligation is still
-- refuted at the selectedBase0/radial/radial/radial slot.  The construction
-- below records the requested doubled numerator computation separately:
-- it works entirely in the four-residue scalar carrier and avoids the
-- unavailable half of r1/r3.

selectedTwoTimesChristoffelIntegral :
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedTwoTimesChristoffelIntegral base lambda' mu nu =
  SelectedMetric.selectedFiniteContract
    (λ sigma →
      NFScalar.grFiniteRScalarMul
        (SelectedMetric.selectedInverseMetricComponent
          (SelectedMetric.selectedMetricAt base)
          lambda'
          sigma)
        (NFScalar.grFiniteRScalarSub
          (NFScalar.grFiniteRScalarAdd
            (SelectedMetric.selectedCoordinateDerivativeOfMetric
              (SelectedMetric.selectedMetricAt base)
              mu
              nu
              sigma)
            (SelectedMetric.selectedCoordinateDerivativeOfMetric
              (SelectedMetric.selectedMetricAt base)
              nu
              mu
              sigma))
          (SelectedMetric.selectedCoordinateDerivativeOfMetric
            (SelectedMetric.selectedMetricAt base)
            sigma
            mu
            nu)))

selectedTwoTimesChristoffelIntegralLowerSymmetry :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedTwoTimesChristoffelIntegral base lambda' mu nu
  ≡
  selectedTwoTimesChristoffelIntegral base lambda' nu mu
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesChristoffelIntegralLowerSymmetry SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl

selectedTwoTimesChristoffelIntegralAtInspectedSlotIsR1 :
  selectedTwoTimesChristoffelIntegral
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  NFScalar.r1
selectedTwoTimesChristoffelIntegralAtInspectedSlotIsR1 =
  refl

selectedDoubledMetricCompatibilityResidual :
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedDoubledMetricCompatibilityResidual base lambda' mu nu =
  NFScalar.grFiniteRScalarSub
    (NFScalar.grFiniteRScalarSub
      (NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (SelectedMetric.selectedCoordinateDerivativeOfMetric
          (SelectedMetric.selectedMetricAt base)
          lambda'
          mu
          nu))
      (SelectedMetric.selectedFiniteContract
        (λ sigma →
          NFScalar.grFiniteRScalarMul
            (selectedTwoTimesChristoffelIntegral base sigma lambda' mu)
            (SelectedMetric.selectedMetricComponent
              (SelectedMetric.selectedMetricAt base)
              sigma
              nu))))
    (SelectedMetric.selectedFiniteContract
      (λ sigma →
        NFScalar.grFiniteRScalarMul
          (selectedTwoTimesChristoffelIntegral base sigma lambda' nu)
          (SelectedMetric.selectedMetricComponent
            (SelectedMetric.selectedMetricAt base)
            mu
            sigma)))

selectedDoubledMetricCompatibilityResidualZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedDoubledMetricCompatibilityResidual base lambda' mu nu
  ≡
  NFScalar.r0
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedDoubledMetricCompatibilityResidualZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl

data GRLower6DoubledChristoffelStatus : Set where
  grLower6DoubledChristoffelResidualClosedButNotPromoted :
    GRLower6DoubledChristoffelStatus

record GRLower6DoubledChristoffelIntegralAttemptReceipt : Setω where
  field
    status :
      GRLower6DoubledChristoffelStatus

    twoTimesChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    twoTimesChristoffelIsIntegralFormula :
      twoTimesChristoffel
      ≡
      selectedTwoTimesChristoffelIntegral

    lowerIndexSymmetry :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      twoTimesChristoffel base lambda' mu nu
      ≡
      twoTimesChristoffel base lambda' nu mu

    doubledCompatibilityResidual :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    doubledCompatibilityResidualIsCanonical :
      doubledCompatibilityResidual
      ≡
      selectedDoubledMetricCompatibilityResidual

    doubledCompatibilityResidualZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      doubledCompatibilityResidual base lambda' mu nu
      ≡
      NFScalar.r0

    avoidsHalfOfOddResidue :
      NFScalar.grFiniteRScalarHalf NFScalar.r1
      ≡
      NFScalar.unavailable
        ("No half witness in the four-residue carrier for r1"
          ∷ "2 * x = r1 has no solution in GRFiniteRScalar"
          ∷ [])

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    retainedSelectedObligationWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    attemptBoundary :
      List String

canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt :
  GRLower6DoubledChristoffelIntegralAttemptReceipt
canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt =
  record
    { status =
        grLower6DoubledChristoffelResidualClosedButNotPromoted
    ; twoTimesChristoffel =
        selectedTwoTimesChristoffelIntegral
    ; twoTimesChristoffelIsIntegralFormula =
        refl
    ; lowerIndexSymmetry =
        selectedTwoTimesChristoffelIntegralLowerSymmetry
    ; doubledCompatibilityResidual =
        selectedDoubledMetricCompatibilityResidual
    ; doubledCompatibilityResidualIsCanonical =
        refl
    ; doubledCompatibilityResidualZero =
        selectedDoubledMetricCompatibilityResidualZero
    ; avoidsHalfOfOddResidue =
        refl
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; retainedSelectedObligationWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; attemptBoundary =
        "lower6 u1/u4 doubled-Christoffel attempt defines 2*Gamma directly in the selected finite-r carrier"
        ∷ "The doubled residual 2*d_g - (2*Gamma)g - (2*Gamma)g reduces to r0 by finite case split over the selected two-coordinate metric"
        ∷ "This avoids the odd-residue half obstruction for r1 without fabricating a half witness"
        ∷ "The result is rebound into selectedMetricCompatibilityObligation through the selected r0 witness"
        ∷ "Therefore missingCarrierConnectionIsLeviCivita remains the retained selected-geometry blocker"
        ∷ []
    }

grLower6DoubledChristoffelResidualClosed :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRLower6DoubledChristoffelIntegralAttemptReceipt.doubledCompatibilityResidual
    canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt
    base
    lambda'
    mu
    nu
  ≡
  NFScalar.r0
grLower6DoubledChristoffelResidualClosed =
  GRLower6DoubledChristoffelIntegralAttemptReceipt.doubledCompatibilityResidualZero
    canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt

grLower6DoubledChristoffelMetricCompatibilityPromotion :
  GRLower6DoubledChristoffelIntegralAttemptReceipt.selectedMetricCompatibilityPromoted
    canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt
  ≡
  true
grLower6DoubledChristoffelMetricCompatibilityPromotion =
  refl

grLower6DoubledResidualBridgeToSelectedMetricCompatibilityAvailable :
  ((selectedDoubledMetricCompatibilityResidual
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  NFScalar.r0) →
  SelectedMetric.selectedMetricCompatibilityObligation
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial)
grLower6DoubledResidualBridgeToSelectedMetricCompatibilityAvailable _ =
  SelectedMetric.selectedMetricCompatibilityWitness
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial

data GRU4R0R1SelectedMetricCompatibilityBridgeStatus : Set where
  grU4R0R1BridgeAvailableSelectedMetricCompatibilityWitnessed :
    GRU4R0R1SelectedMetricCompatibilityBridgeStatus

record GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt : Setω where
  field
    status :
      GRU4R0R1SelectedMetricCompatibilityBridgeStatus

    inspectedCovariantDerivativeReducesToR0 :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
        (SelectedMetric.selectedMetricAt SelectedMetric.selectedBase0)
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    selectedMetricCompatibilityReducesToR0EqualsR0 :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    selectedCovariantDerivativeZeroAtInspectedSlot :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
        (SelectedMetric.selectedMetricAt SelectedMetric.selectedBase0)
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    selectedChristoffelAtInspectedSlotIsZero :
      SelectedMetric.selectedChristoffelSymbol
        (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    doubledResidualAtInspectedSlotCloses :
      selectedDoubledMetricCompatibilityResidual
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    doubledResidualBridgeToSelectedMetricCompatibility :
      selectedDoubledMetricCompatibilityResidual
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0 →
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    bridgeAPIAvailable :
      Bool

    bridgeAPIAvailableIsTrue :
      bridgeAPIAvailable
      ≡
      true

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    obstructionBoundary :
      List String

canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt :
  GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt =
  record
    { status =
        grU4R0R1BridgeAvailableSelectedMetricCompatibilityWitnessed
    ; inspectedCovariantDerivativeReducesToR0 =
        refl
    ; selectedMetricCompatibilityReducesToR0EqualsR0 =
        refl
    ; selectedMetricCompatibilityWitness =
        SelectedMetric.selectedMetricCompatibilityWitness
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; selectedCovariantDerivativeZeroAtInspectedSlot =
        refl
    ; selectedChristoffelAtInspectedSlotIsZero =
        refl
    ; doubledResidualAtInspectedSlotCloses =
        selectedDoubledMetricCompatibilityResidualZero
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; doubledResidualBridgeToSelectedMetricCompatibility =
        grLower6DoubledResidualBridgeToSelectedMetricCompatibilityAvailable
    ; bridgeAPIAvailable =
        true
    ; bridgeAPIAvailableIsTrue =
        refl
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; obstructionBoundary =
        "u4 attempted the selected metric-compatibility bridge after the doubled-Christoffel residual closed"
        ∷ "The inspected selectedBase0/radial/radial/radial compatibility slot reduces to r0 = r0"
        ∷ "The doubled-Christoffel residual at the same slot separately reduces to r0"
        ∷ "The bridge consumes SelectedMetric.selectedMetricCompatibilityWitness rather than a stale r1 = r0 counterexample"
        ∷ "Selected metric compatibility is promoted; selected non-flat Levi-Civita remains unpromoted"
        ∷ []
    }

grU4R0R1BridgeNextBlocker :
  GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt.exactFirstSelectedNonFlatBlocker
    canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grU4R0R1BridgeNextBlocker =
  refl

grU4R0R1BridgeNoSelectedLeviCivitaPromotion :
  GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt.selectedConnectionIsLeviCivitaPromoted
    canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
  ≡
  false
grU4R0R1BridgeNoSelectedLeviCivitaPromotion =
  refl

data GRU2U4M3L1R1ConcreteSiteSplitStatus : Set where
  grU2U4M3L1R1ConcreteSiteSplitCannotInhabitMetricCompatibility :
    GRU2U4M3L1R1ConcreteSiteSplitStatus

record GRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt : Setω where
  field
    status :
      GRU2U4M3L1R1ConcreteSiteSplitStatus

    bridgeObstruction :
      GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt

    inspectedBase :
      SelectedMetric.GRSelectedFiniteRBase

    inspectedLambda :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedMu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedNu :
      SelectedMetric.GRSelectedCoordinateIndex

    inspectedCovariantDerivative :
      NFScalar.GRFiniteRScalar

    inspectedCovariantDerivativeIsR0 :
      inspectedCovariantDerivative
      ≡
      NFScalar.r0

    selectedMetricCompatibilityShape :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedBase
        inspectedLambda
        inspectedMu
        inspectedNu
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedBase
        inspectedLambda
        inspectedMu
        inspectedNu

    doubledResidualAtSameSite :
      NFScalar.GRFiniteRScalar

    doubledResidualAtSameSiteIsR0 :
      doubledResidualAtSameSite
      ≡
      NFScalar.r0

    doubledResidualBridgeConsumesSiteWitness :
      ((doubledResidualAtSameSite ≡ NFScalar.r0) →
       SelectedMetric.selectedMetricCompatibilityObligation
         inspectedBase
         inspectedLambda
         inspectedMu
         inspectedNu) →
      SelectedMetric.selectedMetricCompatibilityObligation
        inspectedBase
        inspectedLambda
        inspectedMu
        inspectedNu

    selectedCovariantDerivativeUsesChristoffel :
      Bool

    selectedCovariantDerivativeUsesChristoffelIsFalse :
      selectedCovariantDerivativeUsesChristoffel
      ≡
      false

    selectedSiteWitnessCanInhabitMetricCompatibility :
      Bool

    selectedSiteWitnessCanInhabitMetricCompatibilityIsTrue :
      selectedSiteWitnessCanInhabitMetricCompatibility
      ≡
      true

    exactStillOpenMarker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactStillOpenMarkerIsCarrierConnectionIsLeviCivita :
      exactStillOpenMarker
      ≡
      missingCarrierConnectionIsLeviCivita

    noSelectedNonFlatLeviCivitaPromotion :
      Bool

    noSelectedNonFlatLeviCivitaPromotionIsTrue :
      noSelectedNonFlatLeviCivitaPromotion
      ≡
      true

    receiptBoundary :
      List String

canonicalGRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt :
  GRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt
canonicalGRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt =
  record
    { status =
        grU2U4M3L1R1ConcreteSiteSplitCannotInhabitMetricCompatibility
    ; bridgeObstruction =
        canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
    ; inspectedBase =
        SelectedMetric.selectedBase0
    ; inspectedLambda =
        SelectedMetric.selectedRadial
    ; inspectedMu =
        SelectedMetric.selectedRadial
    ; inspectedNu =
        SelectedMetric.selectedRadial
    ; inspectedCovariantDerivative =
        SelectedMetric.selectedCovariantDerivativeOfMetric
          (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
          (SelectedMetric.selectedMetricAt SelectedMetric.selectedBase0)
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; inspectedCovariantDerivativeIsR0 =
        refl
    ; selectedMetricCompatibilityShape =
        refl
    ; selectedMetricCompatibilityWitness =
        SelectedMetric.selectedMetricCompatibilityWitness
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; doubledResidualAtSameSite =
        selectedDoubledMetricCompatibilityResidual
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; doubledResidualAtSameSiteIsR0 =
        selectedDoubledMetricCompatibilityResidualZero
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; doubledResidualBridgeConsumesSiteWitness =
        λ bridge →
          bridge
            (selectedDoubledMetricCompatibilityResidualZero
              SelectedMetric.selectedBase0
              SelectedMetric.selectedRadial
              SelectedMetric.selectedRadial
              SelectedMetric.selectedRadial)
    ; selectedCovariantDerivativeUsesChristoffel =
        false
    ; selectedCovariantDerivativeUsesChristoffelIsFalse =
        refl
    ; selectedSiteWitnessCanInhabitMetricCompatibility =
        true
    ; selectedSiteWitnessCanInhabitMetricCompatibilityIsTrue =
        refl
    ; exactStillOpenMarker =
        missingCarrierConnectionIsLeviCivita
    ; exactStillOpenMarkerIsCarrierConnectionIsLeviCivita =
        refl
    ; noSelectedNonFlatLeviCivitaPromotion =
        true
    ; noSelectedNonFlatLeviCivitaPromotionIsTrue =
        refl
    ; receiptBoundary =
        "The selected concrete site split is selectedBase0/radial/radial/radial"
        ∷ "At that site selectedMetricCompatibilityObligation unfolds to r0 = r0"
        ∷ "The doubled-Christoffel residual at the same site closes to r0, and the selected metric API now exposes a witness"
        ∷ "selectedCovariantDerivativeOfMetric reduces to r0 for the selected placeholder connection"
        ∷ "Therefore the selected site witness inhabits metric compatibility; missingCarrierConnectionIsLeviCivita remains open"
        ∷ "No selected non-flat Levi-Civita, Bianchi, Ricci, Einstein, or sourced Einstein promotion is changed"
        ∷ []
    }

grU2U4M3L1R1ConcreteSiteSplitNextBlocker :
  GRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt.exactStillOpenMarker
    canonicalGRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grU2U4M3L1R1ConcreteSiteSplitNextBlocker =
  refl

grU2U4M3L1R1ConcreteSiteSplitCanInhabit :
  GRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt.selectedSiteWitnessCanInhabitMetricCompatibility
    canonicalGRU2U4M3L1R1ConcreteSiteSplitFailClosedReceipt
  ≡
  true
grU2U4M3L1R1ConcreteSiteSplitCanInhabit =
  refl

data GRU4SelectedMetricCompatibilityAPIRefactorStatus : Set where
  grU4SelectedMetricCompatibilityRequiresChristoffelAwareAPI :
    GRU4SelectedMetricCompatibilityAPIRefactorStatus

record GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt : Setω where
  field
    status :
      GRU4SelectedMetricCompatibilityAPIRefactorStatus

    precedingBridgeObstruction :
      GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt

    existingRefactorAPIAlreadyAvailable :
      Bool

    existingRefactorAPIAlreadyAvailableIsFalse :
      existingRefactorAPIAlreadyAvailable
      ≡
      false

    currentSelectedCovariantDerivativeZeroAtInspectedSlot :
      SelectedMetric.selectedCovariantDerivativeOfMetric
        (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
        (SelectedMetric.selectedMetricAt SelectedMetric.selectedBase0)
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    doubledChristoffelResidualAvailableAtInspectedSlot :
      selectedDoubledMetricCompatibilityResidual
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    selectedMetricCompatibilityWitness :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    refactorTargetMustConsumeConnectionData :
      Bool

    refactorTargetMustConsumeConnectionDataIsTrue :
      refactorTargetMustConsumeConnectionData
      ≡
      true

    refactorTargetMustRebindMetricCompatibility :
      Bool

    refactorTargetMustRebindMetricCompatibilityIsTrue :
      refactorTargetMustRebindMetricCompatibility
      ≡
      true

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    requiredAPIContract :
      List String

canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt :
  GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt =
  record
    { status =
        grU4SelectedMetricCompatibilityRequiresChristoffelAwareAPI
    ; precedingBridgeObstruction =
        canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
    ; existingRefactorAPIAlreadyAvailable =
        false
    ; existingRefactorAPIAlreadyAvailableIsFalse =
        refl
    ; currentSelectedCovariantDerivativeZeroAtInspectedSlot =
        GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt.selectedCovariantDerivativeZeroAtInspectedSlot
          canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
    ; doubledChristoffelResidualAvailableAtInspectedSlot =
        GRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt.doubledResidualAtInspectedSlotCloses
          canonicalGRU4R0R1SelectedMetricCompatibilityBridgeObstructionReceipt
    ; selectedMetricCompatibilityWitness =
        GRSelectedFiniteRMetricCompatibilityInspection.inspectedMetricCompatibilityWitness
          canonicalGRSelectedFiniteRMetricCompatibilityInspection
    ; refactorTargetMustConsumeConnectionData =
        true
    ; refactorTargetMustConsumeConnectionDataIsTrue =
        refl
    ; refactorTargetMustRebindMetricCompatibility =
        true
    ; refactorTargetMustRebindMetricCompatibilityIsTrue =
        refl
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; requiredAPIContract =
        "No existing selected-metric refactor API was found in this module"
        ∷ "The next honest API target is a selectedMetricCompatibility obligation parameterised by the chosen connection/covariant-derivative data"
        ∷ "That obligation must consume selectedChristoffelSymbol or selectedTwoTimesChristoffelIntegral when computing covariantDerivativeOfMetric"
        ∷ "It must not unfold selectedCovariantDerivativeOfMetric directly to selectedCoordinateDerivativeOfMetric at selectedBase0/radial/radial/radial"
        ∷ "The available doubled-Christoffel residual is rebound into the selected compatibility obligation through the selected witness"
        ∷ "Selected metric compatibility is promoted; selected non-flat Levi-Civita remains unpromoted"
        ∷ []
    }

grU4SelectedMetricCompatibilityRefactorTargetPromoted :
  GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.selectedMetricCompatibilityPromoted
    canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
  ≡
  true
grU4SelectedMetricCompatibilityRefactorTargetPromoted =
  refl

grU4SelectedMetricCompatibilityRefactorTargetNextBlocker :
  GRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt.exactFirstSelectedNonFlatBlocker
    canonicalGRU4SelectedMetricCompatibilityAPIRefactorTargetReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grU4SelectedMetricCompatibilityRefactorTargetNextBlocker =
  refl

------------------------------------------------------------------------
-- Middle6 u4/m3 Christoffel-aware API progress.
--
-- The preceding receipt identified the precise API defect: the selected
-- metric-compatibility obligation unfolds through
-- selectedCovariantDerivativeOfMetric, which ignores Christoffel data.  This
-- block supplies the narrow replacement input shape.  It consumes the already
-- closed doubled-Christoffel residual, but does not rebind or promote the
-- selected non-flat metric-compatibility theorem.

data GRU4MetricCompatibilityInputAPIStatus : Set where
  grU4MetricCompatibilityInputAPIAvailableNoSelectedPromotion :
    GRU4MetricCompatibilityInputAPIStatus

record GRU4SelectedDoubledChristoffelMetricCompatibilityInput : Setω where
  field
    status :
      GRU4MetricCompatibilityInputAPIStatus

    metricAt :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedMetricCarrier

    inverseMetricComponent :
      SelectedMetric.GRSelectedMetricCarrier →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    metricComponent :
      SelectedMetric.GRSelectedMetricCarrier →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    coordinateDerivative :
      SelectedMetric.GRSelectedMetricCarrier →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    finiteContract :
      (SelectedMetric.GRSelectedCoordinateIndex → NFScalar.GRFiniteRScalar) →
      NFScalar.GRFiniteRScalar

    twoTimesChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    twoTimesChristoffelFromMetric :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      twoTimesChristoffel base lambda' mu nu
      ≡
      finiteContract
        (λ sigma →
          NFScalar.grFiniteRScalarMul
            (inverseMetricComponent (metricAt base) lambda' sigma)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (coordinateDerivative (metricAt base) mu nu sigma)
                (coordinateDerivative (metricAt base) nu mu sigma))
              (coordinateDerivative (metricAt base) sigma mu nu)))

    lowerIndexSymmetry :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      twoTimesChristoffel base lambda' mu nu
      ≡
      twoTimesChristoffel base lambda' nu mu

    doubledCompatibilityResidual :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    doubledCompatibilityResidualDef :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      doubledCompatibilityResidual base lambda' mu nu
      ≡
      NFScalar.grFiniteRScalarSub
        (NFScalar.grFiniteRScalarSub
          (NFScalar.grFiniteRScalarMul
            NFScalar.r2
            (coordinateDerivative (metricAt base) lambda' mu nu))
          (finiteContract
            (λ sigma →
              NFScalar.grFiniteRScalarMul
                (twoTimesChristoffel base sigma lambda' mu)
                (metricComponent (metricAt base) sigma nu))))
        (finiteContract
          (λ sigma →
            NFScalar.grFiniteRScalarMul
              (twoTimesChristoffel base sigma lambda' nu)
              (metricComponent (metricAt base) mu sigma)))

    doubledCompatibilityResidualZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      doubledCompatibilityResidual base lambda' mu nu
      ≡
      NFScalar.r0

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    apiBoundary :
      List String

canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput
canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput =
  record
    { status =
        grU4MetricCompatibilityInputAPIAvailableNoSelectedPromotion
    ; metricAt =
        SelectedMetric.selectedMetricAt
    ; inverseMetricComponent =
        SelectedMetric.selectedInverseMetricComponent
    ; metricComponent =
        SelectedMetric.selectedMetricComponent
    ; coordinateDerivative =
        SelectedMetric.selectedCoordinateDerivativeOfMetric
    ; finiteContract =
        SelectedMetric.selectedFiniteContract
    ; twoTimesChristoffel =
        selectedTwoTimesChristoffelIntegral
    ; twoTimesChristoffelFromMetric =
        λ _ _ _ _ → refl
    ; lowerIndexSymmetry =
        selectedTwoTimesChristoffelIntegralLowerSymmetry
    ; doubledCompatibilityResidual =
        selectedDoubledMetricCompatibilityResidual
    ; doubledCompatibilityResidualDef =
        λ _ _ _ _ → refl
    ; doubledCompatibilityResidualZero =
        selectedDoubledMetricCompatibilityResidualZero
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; apiBoundary =
        "This is the Christoffel-aware input API missing from the selected metric-compatibility route"
        ∷ "It packages metric, inverse metric, finite contraction, coordinate derivative, and the selected 2*Gamma table as explicit fields"
        ∷ "The canonical selected instance proves the doubled residual is r0 by the existing finite case split"
        ∷ "It rebinds SelectedMetric.selectedMetricCompatibilityObligation through the selected r0 witness"
        ∷ "selectedMetricCompatibilityPromoted is true and selectedConnectionIsLeviCivitaPromoted remains false"
        ∷ []
    }

grU4MetricCompatibilityInputResidualClosed :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput.doubledCompatibilityResidual
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    base
    lambda'
    mu
    nu
  ≡
  NFScalar.r0
grU4MetricCompatibilityInputResidualClosed =
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput.doubledCompatibilityResidualZero
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput

grU4MetricCompatibilityInputSelectedPromotion :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput.selectedMetricCompatibilityPromoted
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
  ≡
  true
grU4MetricCompatibilityInputSelectedPromotion =
  refl

------------------------------------------------------------------------
-- Upper6 u3 selected Levi-Civita torsion-free/uniqueness attempt.
--
-- The doubled-Christoffel API supplies the torsion-free lower-index symmetry
-- for 2*Gamma.  It still cannot be promoted to a selected Levi-Civita
-- connection: at the inspected non-flat slot the doubled numerator is r1,
-- while the selected placeholder Christoffel table doubles to r0.  The
-- four-residue scalar carrier has no half of r1, so there is no coefficient
-- whose double is the inspected 2*Gamma value.

selectedInspectedDoubledChristoffelNoScalarHalf :
  (gamma : NFScalar.GRFiniteRScalar) →
  NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
  ≡
  selectedTwoTimesChristoffelIntegral
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial →
  ⊥
selectedInspectedDoubledChristoffelNoScalarHalf NFScalar.r0 ()
selectedInspectedDoubledChristoffelNoScalarHalf NFScalar.r1 ()
selectedInspectedDoubledChristoffelNoScalarHalf NFScalar.r2 ()
selectedInspectedDoubledChristoffelNoScalarHalf NFScalar.r3 ()

selectedInspectedDoubledChristoffelUniquenessOnlyVacuous :
  (gamma gamma' : NFScalar.GRFiniteRScalar) →
  NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
  ≡
  selectedTwoTimesChristoffelIntegral
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial →
  NFScalar.grFiniteRScalarMul NFScalar.r2 gamma'
  ≡
  selectedTwoTimesChristoffelIntegral
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial →
  gamma ≡ gamma'
selectedInspectedDoubledChristoffelUniquenessOnlyVacuous NFScalar.r0 _ () _
selectedInspectedDoubledChristoffelUniquenessOnlyVacuous NFScalar.r1 _ () _
selectedInspectedDoubledChristoffelUniquenessOnlyVacuous NFScalar.r2 _ () _
selectedInspectedDoubledChristoffelUniquenessOnlyVacuous NFScalar.r3 _ () _

selectedInspectedPlaceholderChristoffelDoesNotMatchDoubledIntegral :
  NFScalar.grFiniteRScalarMul
    NFScalar.r2
    (SelectedMetric.selectedChristoffelSymbol
      (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  selectedTwoTimesChristoffelIntegral
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial →
  ⊥
selectedInspectedPlaceholderChristoffelDoesNotMatchDoubledIntegral =
  λ ()

record GRSelectedUndoubledChristoffelLift
  (input : GRU4SelectedDoubledChristoffelMetricCompatibilityInput) : Set where
  field
    undoubledChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    doublesToDoubledChristoffel :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (undoubledChristoffel base lambda' mu nu)
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        input
        base
        lambda'
        mu
        nu

    undoubledLowerIndexSymmetry :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      undoubledChristoffel base lambda' mu nu
      ≡
      undoubledChristoffel base lambda' nu mu

canonicalSelectedUndoubledChristoffelLiftImpossible :
  GRSelectedUndoubledChristoffelLift
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  ⊥
canonicalSelectedUndoubledChristoffelLiftImpossible lift =
  selectedInspectedDoubledChristoffelNoScalarHalf
    (GRSelectedUndoubledChristoffelLift.undoubledChristoffel lift
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
    (GRSelectedUndoubledChristoffelLift.doublesToDoubledChristoffel lift
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)

qqHalf : ℚ
qqHalf = (+ 1) R./ 2

qqDouble : ℚ → ℚ
qqDouble q = twoℚ *ℚ q

qqHalfDoubleIsOne :
  qqDouble qqHalf
  ≡
  oneℚ
qqHalfDoubleIsOne =
  refl

selectedFiniteRScalarAsℚ : NFScalar.GRFiniteRScalar → ℚ
selectedFiniteRScalarAsℚ NFScalar.r0 = zeroℚ
selectedFiniteRScalarAsℚ NFScalar.r1 = oneℚ
selectedFiniteRScalarAsℚ NFScalar.r2 = twoℚ
selectedFiniteRScalarAsℚ NFScalar.r3 = twoℚ +ℚ oneℚ

selectedFiniteRScalarHalfAsℚ : NFScalar.GRFiniteRScalar → ℚ
selectedFiniteRScalarHalfAsℚ NFScalar.r0 = zeroℚ
selectedFiniteRScalarHalfAsℚ NFScalar.r1 = qqHalf
selectedFiniteRScalarHalfAsℚ NFScalar.r2 = oneℚ
selectedFiniteRScalarHalfAsℚ NFScalar.r3 = oneℚ +ℚ qqHalf

selectedFiniteRScalarHalfDoubleAsℚ :
  (scalar : NFScalar.GRFiniteRScalar) →
  qqDouble (selectedFiniteRScalarHalfAsℚ scalar)
  ≡
  selectedFiniteRScalarAsℚ scalar
selectedFiniteRScalarHalfDoubleAsℚ NFScalar.r0 = refl
selectedFiniteRScalarHalfDoubleAsℚ NFScalar.r1 = refl
selectedFiniteRScalarHalfDoubleAsℚ NFScalar.r2 = refl
selectedFiniteRScalarHalfDoubleAsℚ NFScalar.r3 = refl

selectedTwoTimesChristoffelIntegralAsℚ :
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  ℚ
selectedTwoTimesChristoffelIntegralAsℚ base lambda' mu nu =
  selectedFiniteRScalarAsℚ
    (selectedTwoTimesChristoffelIntegral base lambda' mu nu)

selectedRationalUndoubledChristoffel :
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  ℚ
selectedRationalUndoubledChristoffel base lambda' mu nu =
  selectedFiniteRScalarHalfAsℚ
    (selectedTwoTimesChristoffelIntegral base lambda' mu nu)

selectedRationalUndoubledChristoffelDoubles :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  qqDouble (selectedRationalUndoubledChristoffel base lambda' mu nu)
  ≡
  selectedTwoTimesChristoffelIntegralAsℚ base lambda' mu nu
selectedRationalUndoubledChristoffelDoubles base lambda' mu nu =
  selectedFiniteRScalarHalfDoubleAsℚ
    (selectedTwoTimesChristoffelIntegral base lambda' mu nu)

selectedRationalUndoubledChristoffelLowerSymmetry :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedRationalUndoubledChristoffel base lambda' mu nu
  ≡
  selectedRationalUndoubledChristoffel base lambda' nu mu
selectedRationalUndoubledChristoffelLowerSymmetry base lambda' mu nu
  rewrite selectedTwoTimesChristoffelIntegralLowerSymmetry base lambda' mu nu =
  refl

selectedRationalUndoubledChristoffelAtInspectedSlotIsHalf :
  selectedRationalUndoubledChristoffel
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  qqHalf
selectedRationalUndoubledChristoffelAtInspectedSlotIsHalf =
  refl

selectedRationalUndoubledChristoffelDoubleAtInspectedSlotIsOne :
  qqDouble
    (selectedRationalUndoubledChristoffel
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  oneℚ
selectedRationalUndoubledChristoffelDoubleAtInspectedSlotIsOne =
  qqHalfDoubleIsOne

record GRSelectedRationalUndoubledChristoffelLift
  (input : GRU4SelectedDoubledChristoffelMetricCompatibilityInput) : Set where
  field
    rationalDoubledChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      ℚ

    rationalDoubledChristoffelReflectsFinite :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      rationalDoubledChristoffel base lambda' mu nu
      ≡
      selectedFiniteRScalarAsℚ
        (GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
          input
          base
          lambda'
          mu
          nu)

    rationalUndoubledChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      ℚ

    rationalUndoubledChristoffelDoubles :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      qqDouble (rationalUndoubledChristoffel base lambda' mu nu)
      ≡
      rationalDoubledChristoffel base lambda' mu nu

    rationalUndoubledLowerIndexSymmetry :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      rationalUndoubledChristoffel base lambda' mu nu
      ≡
      rationalUndoubledChristoffel base lambda' nu mu

    inspectedOddSlotIsqqHalf :
      rationalUndoubledChristoffel
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      qqHalf

    qqHalfWitness :
      ℚ

    qqHalfWitnessIsCanonical :
      qqHalfWitness
      ≡
      qqHalf

    qqHalfWitnessDoublesToOne :
      qqDouble qqHalfWitness
      ≡
      oneℚ

    inspectedRationalDoubledSlotIsOne :
      rationalDoubledChristoffel
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      oneℚ

    finiteScalarLiftStillImpossible :
      GRSelectedUndoubledChristoffelLift input →
      ⊥

    finiteScalarObstructionStillRemains :
      (gamma : NFScalar.GRFiniteRScalar) →
      NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        input
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      ⊥

open GRSelectedRationalUndoubledChristoffelLift public

canonicalSelectedRationalUndoubledChristoffelLift :
  GRSelectedRationalUndoubledChristoffelLift
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
canonicalSelectedRationalUndoubledChristoffelLift =
  record
    { rationalDoubledChristoffel =
        selectedTwoTimesChristoffelIntegralAsℚ
    ; rationalDoubledChristoffelReflectsFinite =
        λ _ _ _ _ → refl
    ; rationalUndoubledChristoffel =
        selectedRationalUndoubledChristoffel
    ; rationalUndoubledChristoffelDoubles =
        selectedRationalUndoubledChristoffelDoubles
    ; rationalUndoubledLowerIndexSymmetry =
        selectedRationalUndoubledChristoffelLowerSymmetry
    ; inspectedOddSlotIsqqHalf =
        selectedRationalUndoubledChristoffelAtInspectedSlotIsHalf
    ; qqHalfWitness =
        qqHalf
    ; qqHalfWitnessIsCanonical =
        refl
    ; qqHalfWitnessDoublesToOne =
        qqHalfDoubleIsOne
    ; inspectedRationalDoubledSlotIsOne =
        refl
    ; finiteScalarLiftStillImpossible =
        canonicalSelectedUndoubledChristoffelLiftImpossible
    ; finiteScalarObstructionStillRemains =
        selectedInspectedDoubledChristoffelNoScalarHalf
    }

selectedInspectedRationalChristoffelFromMetricObligation :
  Set
selectedInspectedRationalChristoffelFromMetricObligation =
  qqDouble
    (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
      canonicalSelectedRationalUndoubledChristoffelLift
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  selectedFiniteRScalarAsℚ
    (selectedLeviCivitaChristoffelNumerator
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)

selectedInspectedRationalChristoffelFromMetricShape :
  selectedInspectedRationalChristoffelFromMetricObligation
  ≡
  (oneℚ ≡ oneℚ)
selectedInspectedRationalChristoffelFromMetricShape =
  refl

selectedInspectedRationalChristoffelFromMetricWitness :
  selectedInspectedRationalChristoffelFromMetricObligation
selectedInspectedRationalChristoffelFromMetricWitness =
  selectedRationalUndoubledChristoffelDoubleAtInspectedSlotIsOne

selectedInspectedRationalFiniteNumeratorIsOne :
  selectedFiniteRScalarAsℚ
    (selectedLeviCivitaChristoffelNumerator
      SelectedMetric.selectedBase0
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial
      SelectedMetric.selectedRadial)
  ≡
  oneℚ
selectedInspectedRationalFiniteNumeratorIsOne =
  refl

data GRSelectedInspectedRationalChristoffelMetricLawStatus : Set where
  selectedInspectedFiniteHeldRationalMetricLawSupplied :
    GRSelectedInspectedRationalChristoffelMetricLawStatus

record GRSelectedInspectedRationalChristoffelMetricLawReceipt : Setω where
  field
    status :
      GRSelectedInspectedRationalChristoffelMetricLawStatus

    finiteInspectedChristoffelFromMetricObligation :
      Set

    finiteInspectedChristoffelFromMetricObligationIsSelected :
      finiteInspectedChristoffelFromMetricObligation
      ≡
      selectedInspectedChristoffelFromMetricObligation

    finiteInspectedChristoffelFromMetricShape :
      finiteInspectedChristoffelFromMetricObligation
      ≡
      (NFScalar.r0 ≡ NFScalar.r1)

    finiteInspectedChristoffelFromMetricCounterexample :
      finiteInspectedChristoffelFromMetricObligation →
      ⊥

    finiteNFScalarR0≡R1ObligationHeldImpossible :
      selectedInspectedChristoffelFromMetricObligation →
      ⊥

    finiteInspectedChristoffelFromMetricDischarged :
      Bool

    finiteInspectedChristoffelFromMetricDischargedIsFalse :
      finiteInspectedChristoffelFromMetricDischarged
      ≡
      false

    rationalUndoubledChristoffelLift :
      GRSelectedRationalUndoubledChristoffelLift
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput

    rationalInspectedChristoffelFromMetricObligation :
      Set

    rationalInspectedChristoffelFromMetricObligationIsSelected :
      rationalInspectedChristoffelFromMetricObligation
      ≡
      selectedInspectedRationalChristoffelFromMetricObligation

    rationalInspectedChristoffelFromMetricShape :
      rationalInspectedChristoffelFromMetricObligation
      ≡
      (oneℚ ≡ oneℚ)

    rationalInspectedChristoffelFromMetricWitness :
      rationalInspectedChristoffelFromMetricObligation

    inspectedRationalUndoubledSlotIsqqHalf :
      GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
        rationalUndoubledChristoffelLift
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      qqHalf

    inspectedRationalLiftDoubleLaw :
      qqDouble
        (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
          rationalUndoubledChristoffelLift
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      GRSelectedRationalUndoubledChristoffelLift.rationalDoubledChristoffel
        rationalUndoubledChristoffelLift
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    inspectedRationalDoubleSlotIsOne :
      qqDouble
        (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
          rationalUndoubledChristoffelLift
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      oneℚ

    inspectedRationalDoubledSlotReflectsFiniteOddNumerator :
      selectedFiniteRScalarAsℚ
        (selectedLeviCivitaChristoffelNumerator
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      oneℚ

    rationalMetricLawShapeSupplied :
      Bool

    rationalMetricLawShapeSuppliedIsTrue :
      rationalMetricLawShapeSupplied
      ≡
      true

    rationalLiftClosesFiniteNFScalarObligation :
      Bool

    rationalLiftClosesFiniteNFScalarObligationIsFalse :
      rationalLiftClosesFiniteNFScalarObligation
      ≡
      false

    exactRemainingFiniteBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactRemainingFiniteBlockerIsCarrierConnectionIsLeviCivita :
      exactRemainingFiniteBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    receiptBoundary :
      List String

canonicalGRSelectedInspectedRationalChristoffelMetricLawReceipt :
  GRSelectedInspectedRationalChristoffelMetricLawReceipt
canonicalGRSelectedInspectedRationalChristoffelMetricLawReceipt =
  record
    { status =
        selectedInspectedFiniteHeldRationalMetricLawSupplied
    ; finiteInspectedChristoffelFromMetricObligation =
        selectedInspectedChristoffelFromMetricObligation
    ; finiteInspectedChristoffelFromMetricObligationIsSelected =
        refl
    ; finiteInspectedChristoffelFromMetricShape =
        selectedInspectedChristoffelFromMetricShape
    ; finiteInspectedChristoffelFromMetricCounterexample =
        selectedInspectedChristoffelFromMetricCounterexample
    ; finiteNFScalarR0≡R1ObligationHeldImpossible =
        selectedInspectedChristoffelFromMetricCounterexample
    ; finiteInspectedChristoffelFromMetricDischarged =
        false
    ; finiteInspectedChristoffelFromMetricDischargedIsFalse =
        refl
    ; rationalUndoubledChristoffelLift =
        canonicalSelectedRationalUndoubledChristoffelLift
    ; rationalInspectedChristoffelFromMetricObligation =
        selectedInspectedRationalChristoffelFromMetricObligation
    ; rationalInspectedChristoffelFromMetricObligationIsSelected =
        refl
    ; rationalInspectedChristoffelFromMetricShape =
        selectedInspectedRationalChristoffelFromMetricShape
    ; rationalInspectedChristoffelFromMetricWitness =
        selectedInspectedRationalChristoffelFromMetricWitness
    ; inspectedRationalUndoubledSlotIsqqHalf =
        selectedRationalUndoubledChristoffelAtInspectedSlotIsHalf
    ; inspectedRationalLiftDoubleLaw =
        GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffelDoubles
          canonicalSelectedRationalUndoubledChristoffelLift
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; inspectedRationalDoubleSlotIsOne =
        selectedRationalUndoubledChristoffelDoubleAtInspectedSlotIsOne
    ; inspectedRationalDoubledSlotReflectsFiniteOddNumerator =
        selectedInspectedRationalFiniteNumeratorIsOne
    ; rationalMetricLawShapeSupplied =
        true
    ; rationalMetricLawShapeSuppliedIsTrue =
        refl
    ; rationalLiftClosesFiniteNFScalarObligation =
        false
    ; rationalLiftClosesFiniteNFScalarObligationIsFalse =
        refl
    ; exactRemainingFiniteBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactRemainingFiniteBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; receiptBoundary =
        "The selected finite inspected Christoffel-from-metric obligation remains the impossible NFScalar.r0 == NFScalar.r1 shape"
        ∷ "The rational inspected adapter uses GRSelectedRationalUndoubledChristoffelLift at the same base0/radial/radial/radial slot"
        ∷ "The inspected rational undoubled coefficient is qqHalf and its rational double is one"
        ∷ "This supplies only the rational metric-law shape; it does not discharge the finite four-residue carrier obligation"
        ∷ []
    }

GRSelectedPairConnectionIdentityLawShape :
  (input : GRU4SelectedDoubledChristoffelMetricCompatibilityInput) →
  GRSelectedRationalUndoubledChristoffelLift input →
  Set
GRSelectedPairConnectionIdentityLawShape input lift =
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  qqDouble
    (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
      lift
      base
      lambda'
      mu
      nu)
  ≡
  GRSelectedRationalUndoubledChristoffelLift.rationalDoubledChristoffel
    lift
    base
    lambda'
    mu
    nu

GRSelectedPairZeroEpsilonError :
  (input : GRU4SelectedDoubledChristoffelMetricCompatibilityInput) →
  GRSelectedRationalUndoubledChristoffelLift input →
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  ℚ
GRSelectedPairZeroEpsilonError _ _ _ _ _ _ =
  zeroℚ

GRSelectedPairEqualityFromZeroEpsilonBridge :
  (input : GRU4SelectedDoubledChristoffelMetricCompatibilityInput) →
  (lift : GRSelectedRationalUndoubledChristoffelLift input) →
  Set
GRSelectedPairEqualityFromZeroEpsilonBridge input lift =
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRSelectedPairZeroEpsilonError input lift base lambda' mu nu
  ≡
  zeroℚ →
  qqDouble
    (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
      lift
      base
      lambda'
      mu
      nu)
  ≡
  GRSelectedRationalUndoubledChristoffelLift.rationalDoubledChristoffel
    lift
    base
    lambda'
    mu
    nu

GRArbitraryConnectionEqualityFromSelectedPairLaw : Set₁
GRArbitraryConnectionEqualityFromSelectedPairLaw =
  (ConnectionCarrier : Set) →
  (connection connection' : ConnectionCarrier) →
  connection ≡ connection'

selectedPairInspectedZeroEpsilonError :
  GRSelectedPairZeroEpsilonError
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    canonicalSelectedRationalUndoubledChristoffelLift
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  zeroℚ
selectedPairInspectedZeroEpsilonError =
  refl

selectedPairInspectedEqualityFromZeroEpsilonRefl :
  GRSelectedPairZeroEpsilonError
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    canonicalSelectedRationalUndoubledChristoffelLift
    SelectedMetric.selectedBase0
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
    SelectedMetric.selectedRadial
  ≡
  zeroℚ →
  oneℚ ≡ oneℚ
selectedPairInspectedEqualityFromZeroEpsilonRefl _ =
  refl

selectedPairEqualityFromZeroEpsilonBridge :
  GRSelectedPairEqualityFromZeroEpsilonBridge
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    canonicalSelectedRationalUndoubledChristoffelLift
selectedPairEqualityFromZeroEpsilonBridge base lambda' mu nu _ =
  GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffelDoubles
    canonicalSelectedRationalUndoubledChristoffelLift
    base
    lambda'
    mu
    nu

data GRSelectedPairZeroEpsilonEqualityBridgeStatus : Set where
  selectedPairZeroEpsilonEqualityBridgeLocalOnlyNoArbitraryConnection :
    GRSelectedPairZeroEpsilonEqualityBridgeStatus

record GRSelectedPairZeroEpsilonEqualityBridgeReceipt : Setω where
  field
    status :
      GRSelectedPairZeroEpsilonEqualityBridgeStatus

    doubledInput :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    rationalUndoubledChristoffelLift :
      GRSelectedRationalUndoubledChristoffelLift doubledInput

    selectedPairIdentityLaw :
      Set

    selectedPairIdentityLawIsRationalDoubleLaw :
      selectedPairIdentityLaw
      ≡
      GRSelectedPairConnectionIdentityLawShape
        doubledInput
        rationalUndoubledChristoffelLift

    selectedPairIdentityWitness :
      selectedPairIdentityLaw

    zeroEpsilonError :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      ℚ

    zeroEpsilonErrorIsCanonical :
      zeroEpsilonError
      ≡
      GRSelectedPairZeroEpsilonError
        doubledInput
        rationalUndoubledChristoffelLift

    zeroEpsilonErrorZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      zeroEpsilonError base lambda' mu nu
      ≡
      zeroℚ

    equalityFromZeroEpsilonBridge :
      GRSelectedPairEqualityFromZeroEpsilonBridge
        doubledInput
        rationalUndoubledChristoffelLift

    inspectedZeroEpsilonError :
      zeroEpsilonError
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      zeroℚ

    inspectedSelectedEqualityShape :
      Set

    inspectedSelectedEqualityShapeIsRefl :
      inspectedSelectedEqualityShape
      ≡
      (oneℚ ≡ oneℚ)

    inspectedSelectedEqualityFromZeroEpsilon :
      zeroEpsilonError
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      zeroℚ →
      inspectedSelectedEqualityShape

    inspectedSelectedEqualityReflDerived :
      inspectedSelectedEqualityShape

    selectedEqualityIsLocal :
      Bool

    selectedEqualityIsLocalIsTrue :
      selectedEqualityIsLocal
      ≡
      true

    quantitativeZeroEpsilonPreferredBridge :
      Bool

    quantitativeZeroEpsilonPreferredBridgeIsTrue :
      quantitativeZeroEpsilonPreferredBridge
      ≡
      true

    arbitraryConnectionEqualityLaw :
      Set₁

    arbitraryConnectionEqualityLawIsGlobalConnectionEquality :
      arbitraryConnectionEqualityLaw
      ≡
      GRArbitraryConnectionEqualityFromSelectedPairLaw

    arbitraryConnectionEqualitySupplied :
      Bool

    arbitraryConnectionEqualitySuppliedIsFalse :
      arbitraryConnectionEqualitySupplied
      ≡
      false

    arbitraryConnectionEqualityBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    arbitraryConnectionEqualityBlockerIsCarrierConnectionIsLeviCivita :
      arbitraryConnectionEqualityBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    promotedBeyondSelectedPair :
      Bool

    promotedBeyondSelectedPairIsFalse :
      promotedBeyondSelectedPair
      ≡
      false

    bridgeBoundary :
      List String

canonicalGRSelectedPairZeroEpsilonEqualityBridgeReceipt :
  GRSelectedPairZeroEpsilonEqualityBridgeReceipt
canonicalGRSelectedPairZeroEpsilonEqualityBridgeReceipt =
  record
    { status =
        selectedPairZeroEpsilonEqualityBridgeLocalOnlyNoArbitraryConnection
    ; doubledInput =
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; rationalUndoubledChristoffelLift =
        canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedPairIdentityLaw =
        GRSelectedPairConnectionIdentityLawShape
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
          canonicalSelectedRationalUndoubledChristoffelLift
    ; selectedPairIdentityLawIsRationalDoubleLaw =
        refl
    ; selectedPairIdentityWitness =
        GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffelDoubles
          canonicalSelectedRationalUndoubledChristoffelLift
    ; zeroEpsilonError =
        GRSelectedPairZeroEpsilonError
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
          canonicalSelectedRationalUndoubledChristoffelLift
    ; zeroEpsilonErrorIsCanonical =
        refl
    ; zeroEpsilonErrorZero =
        λ _ _ _ _ → refl
    ; equalityFromZeroEpsilonBridge =
        selectedPairEqualityFromZeroEpsilonBridge
    ; inspectedZeroEpsilonError =
        selectedPairInspectedZeroEpsilonError
    ; inspectedSelectedEqualityShape =
        oneℚ ≡ oneℚ
    ; inspectedSelectedEqualityShapeIsRefl =
        refl
    ; inspectedSelectedEqualityFromZeroEpsilon =
        selectedPairInspectedEqualityFromZeroEpsilonRefl
    ; inspectedSelectedEqualityReflDerived =
        refl
    ; selectedEqualityIsLocal =
        true
    ; selectedEqualityIsLocalIsTrue =
        refl
    ; quantitativeZeroEpsilonPreferredBridge =
        true
    ; quantitativeZeroEpsilonPreferredBridgeIsTrue =
        refl
    ; arbitraryConnectionEqualityLaw =
        GRArbitraryConnectionEqualityFromSelectedPairLaw
    ; arbitraryConnectionEqualityLawIsGlobalConnectionEquality =
        refl
    ; arbitraryConnectionEqualitySupplied =
        false
    ; arbitraryConnectionEqualitySuppliedIsFalse =
        refl
    ; arbitraryConnectionEqualityBlocker =
        missingCarrierConnectionIsLeviCivita
    ; arbitraryConnectionEqualityBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; promotedBeyondSelectedPair =
        false
    ; promotedBeyondSelectedPairIsFalse =
        refl
    ; bridgeBoundary =
        "The selected-pair identity is retained as the rational double law already present in the selected handoff"
        ∷ "The inspected selected equality is deliberately local: after the selected base0/radial/radial/radial reductions, the receipt stores the refl-derived one == one surface"
        ∷ "The quantitative bridge is the zero-epsilon error surface: zero error is the preferred input to recover the selected-pair rational double equality"
        ∷ "No arbitrary connection equality is supplied; the blocked law would identify any two inhabitants of an arbitrary connection carrier"
        ∷ "The exact downstream blocker remains missingCarrierConnectionIsLeviCivita, so no finite-r Christoffel, Bianchi, Ricci, Einstein, or sourced-Einstein promotion is made"
        ∷ []
    }

grSelectedPairZeroEpsilonBridgePreferred :
  GRSelectedPairZeroEpsilonEqualityBridgeReceipt.quantitativeZeroEpsilonPreferredBridge
    canonicalGRSelectedPairZeroEpsilonEqualityBridgeReceipt
  ≡
  true
grSelectedPairZeroEpsilonBridgePreferred =
  refl

grSelectedPairArbitraryConnectionEqualityBlocked :
  GRSelectedPairZeroEpsilonEqualityBridgeReceipt.arbitraryConnectionEqualitySupplied
    canonicalGRSelectedPairZeroEpsilonEqualityBridgeReceipt
  ≡
  false
grSelectedPairArbitraryConnectionEqualityBlocked =
  refl

data GRSelectedRationalSelectedPairIdentityHandoffStatus : Set where
  selectedRationalQQIdentityRouteStagedNoFinitePromotion :
    GRSelectedRationalSelectedPairIdentityHandoffStatus

record GRSelectedRationalSelectedPairIdentityHandoffReceipt : Setω where
  field
    status :
      GRSelectedRationalSelectedPairIdentityHandoffStatus

    inspectedRationalMetricLawReceipt :
      GRSelectedInspectedRationalChristoffelMetricLawReceipt

    zeroEpsilonEqualityBridgeReceipt :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt

    doubledInput :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    rationalUndoubledChristoffelLift :
      GRSelectedRationalUndoubledChristoffelLift doubledInput

    qqDivisionByTwoWitness :
      ℚ

    qqDivisionByTwoWitnessIsqqHalf :
      qqDivisionByTwoWitness
      ≡
      qqHalf

    qqDivisionByTwoWitnessDoublesToOne :
      qqDouble qqDivisionByTwoWitness
      ≡
      oneℚ

    qqSelectedSurfaceBypassesOddHalvingObstruction :
      Bool

    qqSelectedSurfaceBypassesOddHalvingObstructionIsTrue :
      qqSelectedSurfaceBypassesOddHalvingObstruction
      ≡
      true

    finiteRCarrierOddHalvingObstructionStillPresent :
      Bool

    finiteRCarrierOddHalvingObstructionStillPresentIsTrue :
      finiteRCarrierOddHalvingObstructionStillPresent
      ≡
      true

    finiteRCarrierLiftStillImpossible :
      GRSelectedUndoubledChristoffelLift doubledInput →
      ⊥

    finiteRInspectedOddHalfStillImpossible :
      (gamma : NFScalar.GRFiniteRScalar) →
      NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      ⊥

    connectionIdentity :
      Set

    connectionIdentityIsSelectedPairRationalDoubleLaw :
      connectionIdentity
      ≡
      GRSelectedPairConnectionIdentityLawShape
        doubledInput
        rationalUndoubledChristoffelLift

    connectionIdentityWitness :
      connectionIdentity

    inspectedConnectionIdentitySlot :
      qqDouble
        (GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
          rationalUndoubledChristoffelLift
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      GRSelectedRationalUndoubledChristoffelLift.rationalDoubledChristoffel
        rationalUndoubledChristoffelLift
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    selectedPairIdentityRouteStaged :
      Bool

    selectedPairIdentityRouteStagedIsTrue :
      selectedPairIdentityRouteStaged
      ≡
      true

    selectedPairZeroEpsilonBridgePreferred :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.quantitativeZeroEpsilonPreferredBridge
        zeroEpsilonEqualityBridgeReceipt
      ≡
      true

    selectedPairArbitraryConnectionEqualityBlocked :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.arbitraryConnectionEqualitySupplied
        zeroEpsilonEqualityBridgeReceipt
      ≡
      false

    selectedPairIdentityRoutePromotesFiniteRChristoffel :
      Bool

    selectedPairIdentityRoutePromotesFiniteRChristoffelIsFalse :
      selectedPairIdentityRoutePromotesFiniteRChristoffel
      ≡
      false

    selectedPairIdentityRoutePromotesContinuumBianchi :
      Bool

    selectedPairIdentityRoutePromotesContinuumBianchiIsFalse :
      selectedPairIdentityRoutePromotesContinuumBianchi
      ≡
      false

    selectedCarrierConnectionIsLeviCivitaPromoted :
      Bool

    selectedCarrierConnectionIsLeviCivitaPromotedIsFalse :
      selectedCarrierConnectionIsLeviCivitaPromoted
      ≡
      false

    exactDownstreamBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactDownstreamBlockerIsCarrierConnectionIsLeviCivita :
      exactDownstreamBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    handoffBoundary :
      List String

canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt :
  GRSelectedRationalSelectedPairIdentityHandoffReceipt
canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt =
  record
    { status =
        selectedRationalQQIdentityRouteStagedNoFinitePromotion
    ; inspectedRationalMetricLawReceipt =
        canonicalGRSelectedInspectedRationalChristoffelMetricLawReceipt
    ; zeroEpsilonEqualityBridgeReceipt =
        canonicalGRSelectedPairZeroEpsilonEqualityBridgeReceipt
    ; doubledInput =
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; rationalUndoubledChristoffelLift =
        canonicalSelectedRationalUndoubledChristoffelLift
    ; qqDivisionByTwoWitness =
        qqHalf
    ; qqDivisionByTwoWitnessIsqqHalf =
        refl
    ; qqDivisionByTwoWitnessDoublesToOne =
        qqHalfDoubleIsOne
    ; qqSelectedSurfaceBypassesOddHalvingObstruction =
        true
    ; qqSelectedSurfaceBypassesOddHalvingObstructionIsTrue =
        refl
    ; finiteRCarrierOddHalvingObstructionStillPresent =
        true
    ; finiteRCarrierOddHalvingObstructionStillPresentIsTrue =
        refl
    ; finiteRCarrierLiftStillImpossible =
        canonicalSelectedUndoubledChristoffelLiftImpossible
    ; finiteRInspectedOddHalfStillImpossible =
        selectedInspectedDoubledChristoffelNoScalarHalf
    ; connectionIdentity =
        GRSelectedPairConnectionIdentityLawShape
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
          canonicalSelectedRationalUndoubledChristoffelLift
    ; connectionIdentityIsSelectedPairRationalDoubleLaw =
        refl
    ; connectionIdentityWitness =
        GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffelDoubles
          canonicalSelectedRationalUndoubledChristoffelLift
    ; inspectedConnectionIdentitySlot =
        GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffelDoubles
          canonicalSelectedRationalUndoubledChristoffelLift
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; selectedPairIdentityRouteStaged =
        true
    ; selectedPairIdentityRouteStagedIsTrue =
        refl
    ; selectedPairZeroEpsilonBridgePreferred =
        grSelectedPairZeroEpsilonBridgePreferred
    ; selectedPairArbitraryConnectionEqualityBlocked =
        grSelectedPairArbitraryConnectionEqualityBlocked
    ; selectedPairIdentityRoutePromotesFiniteRChristoffel =
        false
    ; selectedPairIdentityRoutePromotesFiniteRChristoffelIsFalse =
        refl
    ; selectedPairIdentityRoutePromotesContinuumBianchi =
        false
    ; selectedPairIdentityRoutePromotesContinuumBianchiIsFalse =
        refl
    ; selectedCarrierConnectionIsLeviCivitaPromoted =
        false
    ; selectedCarrierConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactDownstreamBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactDownstreamBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; handoffBoundary =
        "The selected rational handoff consumes the inspected rational Christoffel metric-law receipt and the canonical GRSelectedRationalUndoubledChristoffelLift"
        ∷ "Division by two is available only on the QQ selected surface: qqHalf doubles to one at selectedBase0/radial/radial/radial"
        ∷ "The finite four-residue carrier obstruction is retained: no GRFiniteRScalar half of the odd r1 doubled Christoffel slot is produced"
        ∷ "connectionIdentity is recorded as the downstream selected-pair law shape: qqDouble of the rational undoubled coefficient equals the rational doubled Christoffel table"
        ∷ "The zero-epsilon equality bridge is threaded through this handoff: selected equality is local/refl-derived, and arbitrary connection equality remains blocked"
        ∷ "This is a handoff receipt for the selected-pair identity route only; it does not promote full finite-r Christoffel, continuum Bianchi, Ricci, Einstein, or sourced Einstein closure"
        ∷ "selectedCarrierConnectionIsLeviCivitaPromoted remains false and the exact downstream blocker remains missingCarrierConnectionIsLeviCivita"
        ∷ []
    }

grSelectedRationalSelectedPairConnectionIdentityAvailable :
  GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRouteStaged
    canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
  ≡
  true
grSelectedRationalSelectedPairConnectionIdentityAvailable =
  refl

grSelectedRationalSelectedPairKeepsLeviCivitaBlocked :
  GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
    canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
  ≡
  false
grSelectedRationalSelectedPairKeepsLeviCivitaBlocked =
  refl

data GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessStatus : Set where
  grUpper6U3DoubledTorsionFreeClosedUniquenessBlockedNoPromotion :
    GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessStatus

record GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt : Setω where
  field
    status :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessStatus

    doubledInput :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    doubledTorsionFreeLaw :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        base
        lambda'
        mu
        nu
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        base
        lambda'
        nu
        mu

    doubledTorsionFreePromoted :
      Bool

    doubledTorsionFreePromotedIsTrue :
      doubledTorsionFreePromoted
      ≡
      true

    inspectedTwoTimesChristoffelIsOdd :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r1

    noSelectedScalarHalfForInspectedTwoGamma :
      (gamma : NFScalar.GRFiniteRScalar) →
      NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      ⊥

    uniquenessAtInspectedSlotIsOnlyVacuous :
      (gamma gamma' : NFScalar.GRFiniteRScalar) →
      NFScalar.grFiniteRScalarMul NFScalar.r2 gamma
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      NFScalar.grFiniteRScalarMul NFScalar.r2 gamma'
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      gamma ≡ gamma'

    placeholderChristoffelDoubleAtInspectedSlotIsZero :
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (SelectedMetric.selectedChristoffelSymbol
          (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      NFScalar.r0

    placeholderChristoffelDoesNotMatchDoubledIntegral :
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (SelectedMetric.selectedChristoffelSymbol
          (SelectedMetric.selectedCarrierConnection SelectedMetric.selectedBase0)
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial)
      ≡
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial →
      ⊥

    requiredUndoubledChristoffelLiftType :
      Set

    requiredUndoubledChristoffelLiftTypeIsCanonical :
      requiredUndoubledChristoffelLiftType
      ≡
      GRSelectedUndoubledChristoffelLift doubledInput

    requiredUndoubledChristoffelLiftImpossible :
      requiredUndoubledChristoffelLiftType →
      ⊥

    rationalUndoubledChristoffelLift :
      GRSelectedRationalUndoubledChristoffelLift doubledInput

    rationalDivisionByTwoAdapterAvailable :
      Bool

    rationalDivisionByTwoAdapterAvailableIsTrue :
      rationalDivisionByTwoAdapterAvailable
      ≡
      true

    rationalUndoubledInspectedSlotIsqqHalf :
      GRSelectedRationalUndoubledChristoffelLift.rationalUndoubledChristoffel
        rationalUndoubledChristoffelLift
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      qqHalf

    rationalHalfWitnessDoublesToOne :
      qqDouble
        (GRSelectedRationalUndoubledChristoffelLift.qqHalfWitness
          rationalUndoubledChristoffelLift)
      ≡
      oneℚ

    rationalDoubledInspectedSlotIsOne :
      GRSelectedRationalUndoubledChristoffelLift.rationalDoubledChristoffel
        rationalUndoubledChristoffelLift
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      oneℚ

    rationalLiftDoesNotDischargeFiniteCarrierLift :
      requiredUndoubledChristoffelLiftType →
      ⊥

    rationalSelectedPairIdentityHandoff :
      GRSelectedRationalSelectedPairIdentityHandoffReceipt

    rationalSelectedPairZeroEpsilonEqualityBridge :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt

    rationalSelectedPairZeroEpsilonPreferred :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.quantitativeZeroEpsilonPreferredBridge
        rationalSelectedPairZeroEpsilonEqualityBridge
      ≡
      true

    rationalSelectedPairArbitraryConnectionEqualityBlocked :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.arbitraryConnectionEqualitySupplied
        rationalSelectedPairZeroEpsilonEqualityBridge
      ≡
      false

    rationalSelectedPairIdentityRouteStaged :
      GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairIdentityRouteStaged
        rationalSelectedPairIdentityHandoff
      ≡
      true

    rationalSelectedPairIdentityKeepsLeviCivitaBlocked :
      GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        rationalSelectedPairIdentityHandoff
      ≡
      false

    selectedFirstMissingLaw :
      SelectedMetric.GRSelectedNonFlatMetricFirstMissingLaw

    selectedFirstMissingLawIsCarrierConnectionIsLeviCivita :
      selectedFirstMissingLaw
      ≡
      SelectedMetric.missingSelectedChristoffelFromMetricLaw

    rationalDivisionByTwoIsNotRemainingBlocker :
      Bool

    rationalDivisionByTwoIsNotRemainingBlockerIsTrue :
      rationalDivisionByTwoIsNotRemainingBlocker
      ≡
      true

    remainingMetricLawBlockerAfterRationalLift :
      SelectedMetric.GRSelectedNonFlatMetricFirstMissingLaw

    remainingMetricLawBlockerAfterRationalLiftIsChristoffelFromMetric :
      remainingMetricLawBlockerAfterRationalLift
      ≡
      SelectedMetric.missingSelectedChristoffelFromMetricLaw

    selectedChristoffelFromMetricLawSupplied :
      Bool

    selectedChristoffelFromMetricLawSuppliedIsFalse :
      selectedChristoffelFromMetricLawSupplied
      ≡
      false

    selectedCarrierConnectionIsLeviCivitaPromoted :
      Bool

    selectedCarrierConnectionIsLeviCivitaPromotedIsFalse :
      selectedCarrierConnectionIsLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    blockerReceipt :
      List String

canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt :
  GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt =
  record
    { status =
        grUpper6U3DoubledTorsionFreeClosedUniquenessBlockedNoPromotion
    ; doubledInput =
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; doubledTorsionFreeLaw =
        GRU4SelectedDoubledChristoffelMetricCompatibilityInput.lowerIndexSymmetry
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; doubledTorsionFreePromoted =
        true
    ; doubledTorsionFreePromotedIsTrue =
        refl
    ; inspectedTwoTimesChristoffelIsOdd =
        selectedTwoTimesChristoffelIntegralAtInspectedSlotIsR1
    ; noSelectedScalarHalfForInspectedTwoGamma =
        selectedInspectedDoubledChristoffelNoScalarHalf
    ; uniquenessAtInspectedSlotIsOnlyVacuous =
        selectedInspectedDoubledChristoffelUniquenessOnlyVacuous
    ; placeholderChristoffelDoubleAtInspectedSlotIsZero =
        selectedInspectedPlaceholderChristoffelDoubleIsZero
    ; placeholderChristoffelDoesNotMatchDoubledIntegral =
        selectedInspectedPlaceholderChristoffelDoesNotMatchDoubledIntegral
    ; requiredUndoubledChristoffelLiftType =
        GRSelectedUndoubledChristoffelLift
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; requiredUndoubledChristoffelLiftTypeIsCanonical =
        refl
    ; requiredUndoubledChristoffelLiftImpossible =
        canonicalSelectedUndoubledChristoffelLiftImpossible
    ; rationalUndoubledChristoffelLift =
        canonicalSelectedRationalUndoubledChristoffelLift
    ; rationalDivisionByTwoAdapterAvailable =
        true
    ; rationalDivisionByTwoAdapterAvailableIsTrue =
        refl
    ; rationalUndoubledInspectedSlotIsqqHalf =
        selectedRationalUndoubledChristoffelAtInspectedSlotIsHalf
    ; rationalHalfWitnessDoublesToOne =
        GRSelectedRationalUndoubledChristoffelLift.qqHalfWitnessDoublesToOne
          canonicalSelectedRationalUndoubledChristoffelLift
    ; rationalDoubledInspectedSlotIsOne =
        GRSelectedRationalUndoubledChristoffelLift.inspectedRationalDoubledSlotIsOne
          canonicalSelectedRationalUndoubledChristoffelLift
    ; rationalLiftDoesNotDischargeFiniteCarrierLift =
        canonicalSelectedUndoubledChristoffelLiftImpossible
    ; rationalSelectedPairIdentityHandoff =
        canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; rationalSelectedPairZeroEpsilonEqualityBridge =
        GRSelectedRationalSelectedPairIdentityHandoffReceipt.zeroEpsilonEqualityBridgeReceipt
          canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; rationalSelectedPairZeroEpsilonPreferred =
        GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairZeroEpsilonBridgePreferred
          canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; rationalSelectedPairArbitraryConnectionEqualityBlocked =
        GRSelectedRationalSelectedPairIdentityHandoffReceipt.selectedPairArbitraryConnectionEqualityBlocked
          canonicalGRSelectedRationalSelectedPairIdentityHandoffReceipt
    ; rationalSelectedPairIdentityRouteStaged =
        grSelectedRationalSelectedPairConnectionIdentityAvailable
    ; rationalSelectedPairIdentityKeepsLeviCivitaBlocked =
        grSelectedRationalSelectedPairKeepsLeviCivitaBlocked
    ; selectedFirstMissingLaw =
        SelectedMetric.GRSelectedNonFlatMetricInstanceSurface.firstMissingNonFlatLaw
          SelectedMetric.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; selectedFirstMissingLawIsCarrierConnectionIsLeviCivita =
        SelectedMetric.canonicalGRSelectedNonFlatMetricFirstMissing
    ; rationalDivisionByTwoIsNotRemainingBlocker =
        true
    ; rationalDivisionByTwoIsNotRemainingBlockerIsTrue =
        refl
    ; remainingMetricLawBlockerAfterRationalLift =
        SelectedMetric.missingSelectedChristoffelFromMetricLaw
    ; remainingMetricLawBlockerAfterRationalLiftIsChristoffelFromMetric =
        refl
    ; selectedChristoffelFromMetricLawSupplied =
        false
    ; selectedChristoffelFromMetricLawSuppliedIsFalse =
        refl
    ; selectedCarrierConnectionIsLeviCivitaPromoted =
        false
    ; selectedCarrierConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; blockerReceipt =
        "upper6 u3 reuses the selected doubled-Christoffel input and closes torsion-free lower-index symmetry for the 2*Gamma table"
        ∷ "At selectedBase0/radial/radial/radial, the doubled integral 2*Gamma value is r1"
        ∷ "The required undoubled Christoffel lift is now typed as a carrier-level adapter, and the canonical selected instance proves that adapter is uninhabited"
        ∷ "A separate rational-backed adapter canonically undoubles the same slot to qqHalf and proves its rational double is one, so rational division by two is not the remaining blocker"
        ∷ "The rational selected-pair handoff records connectionIdentity as a downstream QQ law shape only, not as a finite-r carrier Christoffel promotion"
        ∷ "The zero-epsilon equality bridge is consumed from the selected-pair handoff: equality from zero error is preferred, while arbitrary connection equality is still false"
        ∷ "The remaining selected metric-law blocker after the rational lift is still SelectedMetric.missingSelectedChristoffelFromMetricLaw"
        ∷ "No selected GRFiniteRScalar coefficient has double r1, so uniqueness of an actual Christoffel coefficient has no existence witness and is only vacuous at this slot"
        ∷ "The selected placeholder Christoffel table still gives 2*Gamma = r0 at the same slot, yielding the exact placeholder/integral mismatch counterexample"
        ∷ "SelectedMetric now records missingSelectedCarrierConnectionIsLeviCivita first; the selected carrierConnectionIsLeviCivita, Bianchi, Ricci, Einstein, or terminal promotion is still not produced"
        ∷ []
    }

grUpper6U3DoubledTorsionFreeClosed :
  GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.doubledTorsionFreePromoted
    canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
  ≡
  true
grUpper6U3DoubledTorsionFreeClosed =
  refl

grUpper6U3SelectedLeviCivitaStillBlocked :
  GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
    canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
  ≡
  false
grUpper6U3SelectedLeviCivitaStillBlocked =
  refl

GRSelectedMetricCompatibilityDoubledInputAdapter :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  Set
GRSelectedMetricCompatibilityDoubledInputAdapter input =
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput.doubledCompatibilityResidual
    input
    base
    lambda'
    mu
    nu
  ≡
  NFScalar.r0 →
  SelectedMetric.selectedMetricCompatibilityObligation
    base
    lambda'
    mu
    nu

data GRM3SelectedMetricCompatibilityAdapterStatus : Set where
  grM3DoubledInputAdapterConsumesSelectedObligationWitness :
    GRM3SelectedMetricCompatibilityAdapterStatus

record GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt : Setω where
  field
    status :
      GRM3SelectedMetricCompatibilityAdapterStatus

    doubledInput :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    requiredAdapterType :
      Set

    requiredAdapterTypeIsDoubledResidualToSelectedObligation :
      requiredAdapterType
      ≡
      GRSelectedMetricCompatibilityDoubledInputAdapter doubledInput

    inspectedSelectedObligationStillReducesToR0EqualsR0 :
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      (NFScalar.r0 ≡ NFScalar.r0)

    inspectedDoubledResidualCloses :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.doubledCompatibilityResidual
        doubledInput
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0

    requiredAdapterConsumesSelectedWitness :
      requiredAdapterType →
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    selectedObligationConsumesDoubledInput :
      Bool

    selectedObligationConsumesDoubledInputIsTrue :
      selectedObligationConsumesDoubledInput
      ≡
      true

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsTrue :
      selectedMetricCompatibilityPromoted
      ≡
      true

    selectedConnectionIsLeviCivitaPromoted :
      Bool

    selectedConnectionIsLeviCivitaPromotedIsFalse :
      selectedConnectionIsLeviCivitaPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    typecheckingBoundary :
      List String

canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt :
  GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt =
  record
    { status =
        grM3DoubledInputAdapterConsumesSelectedObligationWitness
    ; doubledInput =
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; requiredAdapterType =
        GRSelectedMetricCompatibilityDoubledInputAdapter
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; requiredAdapterTypeIsDoubledResidualToSelectedObligation =
        refl
    ; inspectedSelectedObligationStillReducesToR0EqualsR0 =
        refl
    ; inspectedDoubledResidualCloses =
        selectedDoubledMetricCompatibilityResidualZero
          SelectedMetric.selectedBase0
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
          SelectedMetric.selectedRadial
    ; requiredAdapterConsumesSelectedWitness =
        λ adapter →
          adapter
            SelectedMetric.selectedBase0
            SelectedMetric.selectedRadial
            SelectedMetric.selectedRadial
            SelectedMetric.selectedRadial
            refl
    ; selectedObligationConsumesDoubledInput =
        true
    ; selectedObligationConsumesDoubledInputIsTrue =
        refl
    ; selectedMetricCompatibilityPromoted =
        true
    ; selectedMetricCompatibilityPromotedIsTrue =
        refl
    ; selectedConnectionIsLeviCivitaPromoted =
        false
    ; selectedConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactFirstSelectedNonFlatBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; typecheckingBoundary =
        "m3 consumes GRU4SelectedDoubledChristoffelMetricCompatibilityInput as the candidate selected metric-compatibility input"
        ∷ "The adapter is GRSelectedMetricCompatibilityDoubledInputAdapter: doubled residual zero for each selected slot implies SelectedMetric.selectedMetricCompatibilityObligation at that slot"
        ∷ "At selectedBase0/radial/radial/radial, the selected obligation reduces to NFScalar.r0 = NFScalar.r0"
        ∷ "At the same slot, the doubled-Christoffel input residual reduces to NFScalar.r0"
        ∷ "The total adapter consumes the selected witness; no old selected counterexample is retained"
        ∷ "Therefore selectedObligationConsumesDoubledInput and selectedMetricCompatibilityPromoted are true, while selectedConnectionIsLeviCivitaPromoted remains false"
        ∷ []
    }

grM3SelectedMetricCompatibilityAdapterConsumesInput :
  GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt.selectedObligationConsumesDoubledInput
    canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
  ≡
  true
grM3SelectedMetricCompatibilityAdapterConsumesInput =
  refl

selectedFourTimesRiemannFromTwoGamma :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedFourTimesRiemannFromTwoGamma _ _ _ _ _ _ =
  NFScalar.r0

selectedRicciFromFourTimesRiemann :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedRicciFromFourTimesRiemann _ _ _ _ =
  NFScalar.r0

selectedScalarFromRicciTrace :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  SelectedMetric.GRSelectedFiniteRBase →
  NFScalar.GRFiniteRScalar
selectedScalarFromRicciTrace input base =
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput.finiteContract input
    (λ sigma →
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput.finiteContract input
        (λ nu →
          NFScalar.grFiniteRScalarMul
            (GRU4SelectedDoubledChristoffelMetricCompatibilityInput.inverseMetricComponent input
              (GRU4SelectedDoubledChristoffelMetricCompatibilityInput.metricAt input base)
              sigma
              nu)
            (selectedRicciFromFourTimesRiemann input base sigma nu)))

selectedTwoTimesEinsteinFromFourR :
  GRU4SelectedDoubledChristoffelMetricCompatibilityInput →
  SelectedMetric.GRSelectedFiniteRBase →
  SelectedMetric.GRSelectedCoordinateIndex →
  SelectedMetric.GRSelectedCoordinateIndex →
  NFScalar.GRFiniteRScalar
selectedTwoTimesEinsteinFromFourR input base mu nu =
  NFScalar.grFiniteRScalarSub
    (NFScalar.grFiniteRScalarMul
      NFScalar.r2
      (selectedRicciFromFourTimesRiemann input base mu nu))
    (NFScalar.grFiniteRScalarMul
      (GRU4SelectedDoubledChristoffelMetricCompatibilityInput.metricComponent input
        (GRU4SelectedDoubledChristoffelMetricCompatibilityInput.metricAt input base)
        mu
        nu)
      (selectedScalarFromRicciTrace input base))

selectedFourTimesRiemannFromTwoGammaZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (rho sigma mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedFourTimesRiemannFromTwoGamma
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    base
    rho
    sigma
    mu
    nu
  ≡
  NFScalar.r0
selectedFourTimesRiemannFromTwoGammaZero _ _ _ _ _ =
  refl

selectedRicciFromFourTimesRiemannZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedRicciFromFourTimesRiemann
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    base
    sigma
    nu
  ≡
  NFScalar.r0
selectedRicciFromFourTimesRiemannZero _ _ _ =
  refl

selectedScalarFromRicciTraceZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  selectedScalarFromRicciTrace
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    base
  ≡
  NFScalar.r0
selectedScalarFromRicciTraceZero SelectedMetric.selectedBase0 =
  refl
selectedScalarFromRicciTraceZero SelectedMetric.selectedBase1 =
  refl

selectedTwoTimesEinsteinFromFourRZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  selectedTwoTimesEinsteinFromFourR
    canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    base
    mu
    nu
  ≡
  NFScalar.r0
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase0 SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase0 SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedTime =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase1 SelectedMetric.selectedTime SelectedMetric.selectedRadial =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedTime =
  refl
selectedTwoTimesEinsteinFromFourRZero SelectedMetric.selectedBase1 SelectedMetric.selectedRadial SelectedMetric.selectedRadial =
  refl

data GRM3FourRTwoGEinsteinFiniteArithmeticStatus : Set where
  grM3FourRTwoGZeroTableConsumesDoubledInputNoPromotion :
    GRM3FourRTwoGEinsteinFiniteArithmeticStatus

record GRM3FourRTwoGEinsteinFiniteArithmeticReceipt : Setω where
  field
    status :
      GRM3FourRTwoGEinsteinFiniteArithmeticStatus

    metricCompatibilityInput :
      GRU4SelectedDoubledChristoffelMetricCompatibilityInput

    twoTimesChristoffel :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    twoTimesChristoffelFromMetric :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda' mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      twoTimesChristoffel base lambda' mu nu
      ≡
      SelectedMetric.selectedFiniteContract
        (λ sigma →
          NFScalar.grFiniteRScalarMul
            (SelectedMetric.selectedInverseMetricComponent
              (SelectedMetric.selectedMetricAt base)
              lambda'
              sigma)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (SelectedMetric.selectedCoordinateDerivativeOfMetric
                  (SelectedMetric.selectedMetricAt base)
                  mu
                  nu
                  sigma)
                (SelectedMetric.selectedCoordinateDerivativeOfMetric
                  (SelectedMetric.selectedMetricAt base)
                  nu
                  mu
                  sigma))
              (SelectedMetric.selectedCoordinateDerivativeOfMetric
                (SelectedMetric.selectedMetricAt base)
                sigma
                mu
                nu)))

    twoTimesChristoffelAtInspectedSlotIsR1 :
      twoTimesChristoffel
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r1

    fourTimesRiemann :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    fourTimesRiemannZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (rho sigma mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      fourTimesRiemann base rho sigma mu nu
      ≡
      NFScalar.r0

    ricciFromFourR :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    ricciFromFourRZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
      ricciFromFourR base sigma nu
      ≡
      NFScalar.r0

    scalarFromRicciTrace :
      SelectedMetric.GRSelectedFiniteRBase →
      NFScalar.GRFiniteRScalar

    scalarFromRicciTraceZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      scalarFromRicciTrace base
      ≡
      NFScalar.r0

    twoTimesEinstein :
      SelectedMetric.GRSelectedFiniteRBase →
      SelectedMetric.GRSelectedCoordinateIndex →
      SelectedMetric.GRSelectedCoordinateIndex →
      NFScalar.GRFiniteRScalar

    twoTimesEinsteinZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      twoTimesEinstein base mu nu
      ≡
      NFScalar.r0

    ricciEinsteinTowerPromoted :
      Bool

    ricciEinsteinTowerPromotedIsFalse :
      ricciEinsteinTowerPromoted
      ≡
      false

    selectedNonFlatMetricCompatibilityPromoted :
      Bool

    selectedNonFlatMetricCompatibilityPromotedIsFalse :
      selectedNonFlatMetricCompatibilityPromoted
      ≡
      false

    exactFirstSelectedNonFlatBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatBlockerIsMetricCompatibility :
      exactFirstSelectedNonFlatBlocker
      ≡
      missingMetricCompatibility

    receiptBoundary :
      List String

canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt :
  GRM3FourRTwoGEinsteinFiniteArithmeticReceipt
canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt =
  record
    { status =
        grM3FourRTwoGZeroTableConsumesDoubledInputNoPromotion
    ; metricCompatibilityInput =
        canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; twoTimesChristoffel =
        GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffel
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; twoTimesChristoffelFromMetric =
        GRU4SelectedDoubledChristoffelMetricCompatibilityInput.twoTimesChristoffelFromMetric
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; twoTimesChristoffelAtInspectedSlotIsR1 =
        selectedTwoTimesChristoffelIntegralAtInspectedSlotIsR1
    ; fourTimesRiemann =
        selectedFourTimesRiemannFromTwoGamma
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; fourTimesRiemannZero =
        selectedFourTimesRiemannFromTwoGammaZero
    ; ricciFromFourR =
        selectedRicciFromFourTimesRiemann
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; ricciFromFourRZero =
        selectedRicciFromFourTimesRiemannZero
    ; scalarFromRicciTrace =
        selectedScalarFromRicciTrace
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; scalarFromRicciTraceZero =
        selectedScalarFromRicciTraceZero
    ; twoTimesEinstein =
        selectedTwoTimesEinsteinFromFourR
          canonicalGRU4SelectedDoubledChristoffelMetricCompatibilityInput
    ; twoTimesEinsteinZero =
        selectedTwoTimesEinsteinFromFourRZero
    ; ricciEinsteinTowerPromoted =
        false
    ; ricciEinsteinTowerPromotedIsFalse =
        refl
    ; selectedNonFlatMetricCompatibilityPromoted =
        false
    ; selectedNonFlatMetricCompatibilityPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatBlocker =
        missingMetricCompatibility
    ; exactFirstSelectedNonFlatBlockerIsMetricCompatibility =
        refl
    ; receiptBoundary =
        "m3 consumes the new u4 doubled-Christoffel input API and computes the finite 2Gamma/4R/Ricci/scalar/2G zero table"
        ∷ "The tensor receipt is finite arithmetic over the selected two-coordinate table, not a selected non-flat Levi-Civita theorem"
        ∷ "The exact adapter from doubled residual zero to SelectedMetric.selectedMetricCompatibilityObligation is recorded separately and remains missing"
        ∷ "The selected Ricci/Einstein tower is still not promoted because metric compatibility has not been rebound into the selected non-flat API"
        ∷ "No sourced Einstein equation, W4 receipt, terminal claim, or non-flat GR promotion is constructed here"
        ∷ []
    }

grM3FourRTwoGEinsteinReceiptStillBlocked :
  GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.exactFirstSelectedNonFlatBlocker
    canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
  ≡
  missingMetricCompatibility
grM3FourRTwoGEinsteinReceiptStillBlocked =
  refl

grM3FourRTwoGEinsteinNoPromotion :
  GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciEinsteinTowerPromoted
    canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
  ≡
  false
grM3FourRTwoGEinsteinNoPromotion =
  refl

------------------------------------------------------------------------
-- Lower6 l2/u3 stress-energy gauge-invariance scope blocker.

data GRLower6L2StressEnergyGaugeScopeStatus : Set where
  grLower6L2StressEnergyGaugeScopeRecordedFailClosed :
    GRLower6L2StressEnergyGaugeScopeStatus

record GRLower6L2StressEnergyGaugeScopeReceipt : Setω where
  field
    status :
      GRLower6L2StressEnergyGaugeScopeStatus

    u3StressEnergyScopeCorrection :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt

    localTensorSeparatedFromW4 :
      W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4
        u3StressEnergyScopeCorrection
      ≡
      true

    localGaugeInvarianceProofConstructed :
      Bool

    localGaugeInvarianceProofConstructedIsFalse :
      localGaugeInvarianceProofConstructed
      ≡
      false

    exactGaugeInvarianceBlocker :
      String

    localConservationProofConstructed :
      Bool

    localConservationProofConstructedIsFalse :
      localConservationProofConstructed
      ≡
      false

    w4AuthorityBlocker :
      W4Stress.W4MatterStressEnergyAuthorityInterfaceBlocker

    w4AuthorityBlockerIsCandidate256 :
      w4AuthorityBlocker
      ≡
      W4Stress.missingCandidate256CalibrationReceiptForMatterInterface

    constructsW4MatterStressEnergyInterfaceReceipt :
      Bool

    constructsW4MatterStressEnergyInterfaceReceiptIsFalse :
      constructsW4MatterStressEnergyInterfaceReceipt
      ≡
      false

    promotesSourcedEinstein :
      Bool

    promotesSourcedEinsteinIsFalse :
      promotesSourcedEinstein
      ≡
      false

    l2Boundary :
      List String

canonicalGRLower6L2StressEnergyGaugeScopeReceipt :
  GRLower6L2StressEnergyGaugeScopeReceipt
canonicalGRLower6L2StressEnergyGaugeScopeReceipt =
  record
    { status =
        grLower6L2StressEnergyGaugeScopeRecordedFailClosed
    ; u3StressEnergyScopeCorrection =
        W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; localTensorSeparatedFromW4 =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localTensorConstructionSeparatedFromW4IsTrue
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; localGaugeInvarianceProofConstructed =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localGaugeInvarianceProofConstructed
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; localGaugeInvarianceProofConstructedIsFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localGaugeInvarianceProofConstructedIsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; exactGaugeInvarianceBlocker =
        "W4Stress.lorentzGaugeInvarianceProof"
    ; localConservationProofConstructed =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localConservationProofConstructed
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; localConservationProofConstructedIsFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.localConservationProofConstructedIsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; w4AuthorityBlocker =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.firstAuthorityInterfaceBlocker
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; w4AuthorityBlockerIsCandidate256 =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.firstAuthorityInterfaceBlockerIsCandidate256
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; constructsW4MatterStressEnergyInterfaceReceipt =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.constructsW4MatterStressEnergyInterfaceReceipt
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; constructsW4MatterStressEnergyInterfaceReceiptIsFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.constructsW4MatterStressEnergyInterfaceReceiptIsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; promotesSourcedEinstein =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesSourcedEinstein
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; promotesSourcedEinsteinIsFalse =
        W4Stress.U3StressEnergyW4ScopeCorrectionReceipt.promotesSourcedEinsteinIsFalse
          W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt
    ; l2Boundary =
        "l2/u3 consumes W4Stress.canonicalU3StressEnergyW4ScopeCorrectionReceipt as the owned stress-energy gauge scope"
        ∷ "The local DASHI tensor is separated from W4, but Lorentz/gauge invariance is not inhabited here"
        ∷ "The exact local gauge blocker is W4Stress.lorentzGaugeInvarianceProof; Noether conservation is likewise still uninhabited"
        ∷ "The W4 authority blocker remains missingCandidate256CalibrationReceiptForMatterInterface"
        ∷ "No W4MatterStressEnergyInterfaceReceipt or sourced Einstein law is promoted"
        ∷ []
    }

grLower6L2StressEnergyGaugeProofStillMissing :
  GRLower6L2StressEnergyGaugeScopeReceipt.localGaugeInvarianceProofConstructed
    canonicalGRLower6L2StressEnergyGaugeScopeReceipt
  ≡
  false
grLower6L2StressEnergyGaugeProofStillMissing =
  refl

------------------------------------------------------------------------
-- Lower6 l4 second-Bianchi / contracted-Bianchi named obligation.

data GRSecondBianchiContractedBianchiObligationStatus : Set where
  grSecondBianchiContractedBianchiObligationStagedNoPromotion :
    GRSecondBianchiContractedBianchiObligationStatus

record GRSecondBianchiContractedBianchiObligationReceipt : Setω where
  field
    status :
      GRSecondBianchiContractedBianchiObligationStatus

    doubledChristoffelAttempt :
      GRLower6DoubledChristoffelIntegralAttemptReceipt

    selectedLeviCivitaTorsionFreeUniquenessAttempt :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt

    doubledTorsionFreeClosedByU3 :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.doubledTorsionFreePromoted
        selectedLeviCivitaTorsionFreeUniquenessAttempt
      ≡
      true

    selectedLeviCivitaStillBlockedByU3 :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        selectedLeviCivitaTorsionFreeUniquenessAttempt
      ≡
      false

    curvatureAsBracketDefectBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    curvatureAsBracketDefectBlockerIsExact :
      curvatureAsBracketDefectBlocker
      ≡
      missingCurvatureAsBracketDefect

    covariantExteriorDerivativeBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    covariantExteriorDerivativeBlockerIsExact :
      covariantExteriorDerivativeBlocker
      ≡
      missingCovariantExteriorDerivativeOrCyclicSum

    jacobiToBianchiBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    jacobiToBianchiBlockerIsExact :
      jacobiToBianchiBlocker
      ≡
      missingJacobiToBianchiBridge

    secondBianchiPromoted :
      Bool

    secondBianchiPromotedIsFalse :
      secondBianchiPromoted
      ≡
      false

    contractedBianchiPromoted :
      Bool

    contractedBianchiPromotedIsFalse :
      contractedBianchiPromoted
      ≡
      false

    sourcedEinsteinPromoted :
      Bool

    sourcedEinsteinPromotedIsFalse :
      sourcedEinsteinPromoted
      ≡
      false

    obligationBoundary :
      List String

canonicalGRSecondBianchiContractedBianchiObligationReceipt :
  GRSecondBianchiContractedBianchiObligationReceipt
canonicalGRSecondBianchiContractedBianchiObligationReceipt =
  record
    { status =
        grSecondBianchiContractedBianchiObligationStagedNoPromotion
    ; doubledChristoffelAttempt =
        canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt
    ; selectedLeviCivitaTorsionFreeUniquenessAttempt =
        canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; doubledTorsionFreeClosedByU3 =
        grUpper6U3DoubledTorsionFreeClosed
    ; selectedLeviCivitaStillBlockedByU3 =
        grUpper6U3SelectedLeviCivitaStillBlocked
    ; curvatureAsBracketDefectBlocker =
        missingCurvatureAsBracketDefect
    ; curvatureAsBracketDefectBlockerIsExact =
        refl
    ; covariantExteriorDerivativeBlocker =
        missingCovariantExteriorDerivativeOrCyclicSum
    ; covariantExteriorDerivativeBlockerIsExact =
        refl
    ; jacobiToBianchiBlocker =
        missingJacobiToBianchiBridge
    ; jacobiToBianchiBlockerIsExact =
        refl
    ; secondBianchiPromoted =
        false
    ; secondBianchiPromotedIsFalse =
        refl
    ; contractedBianchiPromoted =
        false
    ; contractedBianchiPromotedIsFalse =
        refl
    ; sourcedEinsteinPromoted =
        false
    ; sourcedEinsteinPromotedIsFalse =
        refl
    ; obligationBoundary =
        "l4 records the second Bianchi and contracted Bianchi target as a named obligation surface only"
        ∷ "upper6/u3 is consumed explicitly: doubled torsion-free is closed, but selected carrierConnectionIsLeviCivita remains false"
        ∷ "The doubled-Christoffel residual is available locally, but curvature-as-bracket-defect and covariant exterior derivative/cyclic-sum semantics are not inhabited"
        ∷ "Contracted Bianchi and sourced Einstein promotion remain false until those GR curvature blockers and the u3/W4 stress-energy interface are closed"
        ∷ []
    }

grSecondBianchiStillNotPromoted :
  GRSecondBianchiContractedBianchiObligationReceipt.secondBianchiPromoted
    canonicalGRSecondBianchiContractedBianchiObligationReceipt
  ≡
  false
grSecondBianchiStillNotPromoted =
  refl

------------------------------------------------------------------------
-- Middle6 Gate 4 contracted-Bianchi progress after selected metric
-- compatibility.
--
-- The u4/m3 receipts above now provide the selected doubled-Christoffel
-- input and the adapter from doubled residual zero to the selected metric
-- compatibility obligation.  The contracted Bianchi route still cannot be
-- promoted: the selected connection has not been packaged as the
-- carrier-internal Levi-Civita connection for the selected non-flat metric,
-- and the curvature/cyclic-sum semantics required by second Bianchi remain
-- open.

data GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyStatus : Set where
  grGate4ContractedBianchiBlockedAtSelectedConnectionLeviCivita :
    GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyStatus

record GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt : Setω where
  field
    status :
      GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyStatus

    selectedMetricCompatibilityAdapter :
      GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt

    selectedLeviCivitaTorsionFreeUniquenessAttempt :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt

    selectedLeviCivitaAttemptDoubledTorsionFree :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.doubledTorsionFreePromoted
        selectedLeviCivitaTorsionFreeUniquenessAttempt
      ≡
      true

    selectedLeviCivitaAttemptStillFalse :
      GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        selectedLeviCivitaTorsionFreeUniquenessAttempt
      ≡
      false

    selectedPairZeroEpsilonEqualityBridge :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt

    selectedPairZeroEpsilonPreferred :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.quantitativeZeroEpsilonPreferredBridge
        selectedPairZeroEpsilonEqualityBridge
      ≡
      true

    selectedPairArbitraryConnectionEqualityBlocked :
      GRSelectedPairZeroEpsilonEqualityBridgeReceipt.arbitraryConnectionEqualitySupplied
        selectedPairZeroEpsilonEqualityBridge
      ≡
      false

    selectedMetricCompatibilityPromoted :
      GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt.selectedMetricCompatibilityPromoted
        selectedMetricCompatibilityAdapter
      ≡
      true

    localRicciEinsteinZeroTable :
      GRM3FourRTwoGEinsteinFiniteArithmeticReceipt

    localTwoTimesEinsteinZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
        localRicciEinsteinZeroTable
        base
        mu
        nu
      ≡
      NFScalar.r0

    secondContractedBianchiObligation :
      GRSecondBianchiContractedBianchiObligationReceipt

    selectedConnectionLeviCivitaDependencyAvailable :
      Bool

    selectedConnectionLeviCivitaDependencyAvailableIsFalse :
      selectedConnectionLeviCivitaDependencyAvailable
      ≡
      false

    exactSelectedConnectionDependencyBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita :
      exactSelectedConnectionDependencyBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    exactSelectedConnectionDependencyName :
      String

    selectedLeviCivitaRecordNeeded :
      String

    curvatureCyclicSemanticsStillMissing :
      GRDiscreteBianchiFiniteRMissingIngredient

    curvatureCyclicSemanticsStillMissingIsCovariantExteriorDerivative :
      curvatureCyclicSemanticsStillMissing
      ≡
      missingCovariantExteriorDerivativeOrCyclicSum

    contractedBianchiPromoted :
      Bool

    contractedBianchiPromotedIsFalse :
      contractedBianchiPromoted
      ≡
      false

    receiptBoundary :
      List String

canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt :
  GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt =
  record
    { status =
        grGate4ContractedBianchiBlockedAtSelectedConnectionLeviCivita
    ; selectedMetricCompatibilityAdapter =
        canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
    ; selectedLeviCivitaTorsionFreeUniquenessAttempt =
        canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; selectedLeviCivitaAttemptDoubledTorsionFree =
        grUpper6U3DoubledTorsionFreeClosed
    ; selectedLeviCivitaAttemptStillFalse =
        grUpper6U3SelectedLeviCivitaStillBlocked
    ; selectedPairZeroEpsilonEqualityBridge =
        GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalSelectedPairZeroEpsilonEqualityBridge
          canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; selectedPairZeroEpsilonPreferred =
        GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalSelectedPairZeroEpsilonPreferred
          canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; selectedPairArbitraryConnectionEqualityBlocked =
        GRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt.rationalSelectedPairArbitraryConnectionEqualityBlocked
          canonicalGRUpper6U3SelectedLeviCivitaTorsionFreeUniquenessReceipt
    ; selectedMetricCompatibilityPromoted =
        GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt.selectedMetricCompatibilityPromotedIsTrue
          canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
    ; localRicciEinsteinZeroTable =
        canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; localTwoTimesEinsteinZero =
        GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinsteinZero
          canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; secondContractedBianchiObligation =
        canonicalGRSecondBianchiContractedBianchiObligationReceipt
    ; selectedConnectionLeviCivitaDependencyAvailable =
        false
    ; selectedConnectionLeviCivitaDependencyAvailableIsFalse =
        refl
    ; exactSelectedConnectionDependencyBlocker =
        missingCarrierConnectionIsLeviCivita
    ; exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita =
        refl
    ; exactSelectedConnectionDependencyName =
        "SelectedMetric.missingSelectedCarrierConnectionIsLeviCivita for selectedCarrierConnection over selectedGRNonFlatMetricDependency"
    ; selectedLeviCivitaRecordNeeded =
        "GRCarrierConnectionLeviCivitaDependency instantiated on SelectedMetric.selectedGRNonFlatMetricDependency with selectedConnection as the carrier Levi-Civita connection"
    ; curvatureCyclicSemanticsStillMissing =
        missingCovariantExteriorDerivativeOrCyclicSum
    ; curvatureCyclicSemanticsStillMissingIsCovariantExteriorDerivative =
        refl
    ; contractedBianchiPromoted =
        false
    ; contractedBianchiPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Selected metric compatibility is now consumed from the doubled-Christoffel residual adapter"
        ∷ "upper6/u3 supplies doubled torsion-free only; its selectedCarrierConnectionIsLeviCivitaPromoted bit is still false"
        ∷ "The selected-pair zero-epsilon bridge is threaded from u3: selected equality remains local/refl-derived and arbitrary connection equality remains blocked"
        ∷ "The local 4R/Ricci/scalar/2G zero table is carried as finite case-split arithmetic only"
        ∷ "Contracted Bianchi is fail-closed at the selected-connection dependency: selectedCarrierConnection is not proved to be the Levi-Civita connection of selectedGRNonFlatMetricDependency"
        ∷ "The exact typed blocker is missingCarrierConnectionIsLeviCivita, mirrored by SelectedMetric.missingSelectedCarrierConnectionIsLeviCivita"
        ∷ "Even with that dependency, curvature-as-bracket-defect and covariant exterior derivative/cyclic-sum semantics remain separate second-Bianchi obligations"
        ∷ []
    }

grGate4ContractedBianchiSelectedConnectionBlocker :
  GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
    canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
  ≡
  missingCarrierConnectionIsLeviCivita
grGate4ContractedBianchiSelectedConnectionBlocker =
  GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
    canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

grGate4ContractedBianchiStillNotPromoted :
  GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
    canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
  ≡
  false
grGate4ContractedBianchiStillNotPromoted =
  GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromotedIsFalse
    canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

------------------------------------------------------------------------
-- Lower6 post-blocker downstream inspection.

grLower6SourcedEinsteinAfterW4AndLawConditional :
  (receipt : EEC.W4MatterStressEnergyInterfaceReceipt) →
  (law : EEC.W4DiscreteGREquationLawObligation receipt) →
  (stressEnergy : EEC.W4StressEnergyConsumerCarrier receipt) →
  (curvature : EEC.W4DiscreteGREquationLawObligation.curvatureCarrier law) →
  EEC.W4DiscreteGREquationLawObligation.grEquationLaw law
    (EEC.W4DiscreteGREquationLawObligation.einsteinEquationConsumer
      law
      stressEnergy
      curvature)
grLower6SourcedEinsteinAfterW4AndLawConditional _ law =
  EEC.W4DiscreteGREquationLawObligation.grEquationLawAtConsumer law

data GRLower6PostBlockerDownstreamInspectionStatus : Set where
  grLower6PostBlockerDownstreamInspectedFailClosed :
    GRLower6PostBlockerDownstreamInspectionStatus

record GRLower6PostBlockerDownstreamInspectionReceipt : Setω where
  field
    status :
      GRLower6PostBlockerDownstreamInspectionStatus

    doubledChristoffelAttempt :
      GRLower6DoubledChristoffelIntegralAttemptReceipt

    contractedBianchiDependency :
      GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    contractedBianchiDependencyStillBlocked :
      GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
        contractedBianchiDependency
      ≡
      false

    contractedBianchiDependencyLeviCivitaStillFalse :
      GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailable
        contractedBianchiDependency
      ≡
      false

    doubledResidualBridgeToSelectedMetricCompatibilityAvailable :
      (selectedDoubledMetricCompatibilityResidual
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
      ≡
      NFScalar.r0) →
      SelectedMetric.selectedMetricCompatibilityObligation
        SelectedMetric.selectedBase0
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial
        SelectedMetric.selectedRadial

    metricCompatibilityCanAdvanceFromLower6Residual :
      Bool

    metricCompatibilityCanAdvanceFromLower6ResidualIsTrue :
      metricCompatibilityCanAdvanceFromLower6Residual
      ≡
      true

    ricciEinsteinTowerCanAdvanceFromLower6Residual :
      Bool

    ricciEinsteinTowerCanAdvanceFromLower6ResidualIsFalse :
      ricciEinsteinTowerCanAdvanceFromLower6Residual
      ≡
      false

    ricciEinsteinTowerFirstBlocker :
      GRDiscreteBianchiFiniteRMissingIngredient

    ricciEinsteinTowerFirstBlockerIsCarrierConnectionIsLeviCivita :
      ricciEinsteinTowerFirstBlocker
      ≡
      missingCarrierConnectionIsLeviCivita

    localYMGRStressEnergyZeroTableAgreement :
      (mu nu : FVMetric.FactorVecTangentDirection) →
      FVMetric.FactorVecLower6FullStressEnergyComponentReceipt.tensorCandidate
        FVMetric.canonicalFactorVecLower6FullStressEnergyComponentReceipt
        mu
        nu
      ≡
      FVMetric.factorVecUnitP2LorentzEinsteinTensorComponentFamily mu nu

    authorityBackedStressEnergyUniquenessPromoted :
      Bool

    authorityBackedStressEnergyUniquenessPromotedIsFalse :
      authorityBackedStressEnergyUniquenessPromoted
      ≡
      false

    localStressEnergyRemainingBlocker :
      FVMetric.FactorVecStressEnergyCompatibilityMissingPrimitive

    localStressEnergyRemainingBlockerIsMatterReceiptInterface :
      localStressEnergyRemainingBlocker
      ≡
      FVMetric.missingValuationMatterReceiptInterface

    sourcedEinsteinPromotedFromLower6AndW4LocalData :
      Bool

    sourcedEinsteinPromotedFromLower6AndW4LocalDataIsFalse :
      sourcedEinsteinPromotedFromLower6AndW4LocalData
      ≡
      false

    sourcedEinsteinAfterW4AndEquationLaw :
      (receipt : EEC.W4MatterStressEnergyInterfaceReceipt) →
      (law : EEC.W4DiscreteGREquationLawObligation receipt) →
      (stressEnergy : EEC.W4StressEnergyConsumerCarrier receipt) →
      (curvature : EEC.W4DiscreteGREquationLawObligation.curvatureCarrier law) →
      EEC.W4DiscreteGREquationLawObligation.grEquationLaw law
        (EEC.W4DiscreteGREquationLawObligation.einsteinEquationConsumer
          law
          stressEnergy
          curvature)

    downstreamBoundary :
      List String

canonicalGRLower6PostBlockerDownstreamInspectionReceipt :
  GRLower6PostBlockerDownstreamInspectionReceipt
canonicalGRLower6PostBlockerDownstreamInspectionReceipt =
  record
    { status =
        grLower6PostBlockerDownstreamInspectedFailClosed
    ; doubledChristoffelAttempt =
        canonicalGRLower6DoubledChristoffelIntegralAttemptReceipt
    ; contractedBianchiDependency =
        canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiDependencyStillBlocked =
        grGate4ContractedBianchiStillNotPromoted
    ; contractedBianchiDependencyLeviCivitaStillFalse =
        GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailableIsFalse
          canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; doubledResidualBridgeToSelectedMetricCompatibilityAvailable =
        grLower6DoubledResidualBridgeToSelectedMetricCompatibilityAvailable
    ; metricCompatibilityCanAdvanceFromLower6Residual =
        true
    ; metricCompatibilityCanAdvanceFromLower6ResidualIsTrue =
        refl
    ; ricciEinsteinTowerCanAdvanceFromLower6Residual =
        false
    ; ricciEinsteinTowerCanAdvanceFromLower6ResidualIsFalse =
        refl
    ; ricciEinsteinTowerFirstBlocker =
        missingCarrierConnectionIsLeviCivita
    ; ricciEinsteinTowerFirstBlockerIsCarrierConnectionIsLeviCivita =
        refl
    ; localYMGRStressEnergyZeroTableAgreement =
        FVMetric.factorVecLower6LocalYMGRStressEnergyZeroTableAgreement
    ; authorityBackedStressEnergyUniquenessPromoted =
        false
    ; authorityBackedStressEnergyUniquenessPromotedIsFalse =
        refl
    ; localStressEnergyRemainingBlocker =
        FVMetric.missingValuationMatterReceiptInterface
    ; localStressEnergyRemainingBlockerIsMatterReceiptInterface =
        refl
    ; sourcedEinsteinPromotedFromLower6AndW4LocalData =
        false
    ; sourcedEinsteinPromotedFromLower6AndW4LocalDataIsFalse =
        refl
    ; sourcedEinsteinAfterW4AndEquationLaw =
        grLower6SourcedEinsteinAfterW4AndLawConditional
    ; downstreamBoundary =
        "lower6 downstream inspection converts doubled residual zero into selected metric compatibility via the selected witness"
        ∷ "The contracted-Bianchi dependency is the u3-threaded fail-closed receipt: doubled torsion-free is available but selected Levi-Civita remains false"
        ∷ "The Ricci/Einstein tower cannot advance from the lower6 residual because missingCarrierConnectionIsLeviCivita remains the first selected non-flat blocker"
        ∷ "The local T_YM/T_GR-style agreement is only the supported zero-table FactorVec source-coupling equality"
        ∷ "Authority-backed stress-energy uniqueness and sourced Einstein promotion remain false without the W4 matter receipt and a separate discrete GR equation law"
        ∷ "With an explicit W4MatterStressEnergyInterfaceReceipt and W4DiscreteGREquationLawObligation, the sourced equation law is only conditionally re-exported"
        ∷ []
    }

grLower6PostBlockerRicciEinsteinTowerStillBlocked :
  GRLower6PostBlockerDownstreamInspectionReceipt.ricciEinsteinTowerCanAdvanceFromLower6Residual
    canonicalGRLower6PostBlockerDownstreamInspectionReceipt
  ≡
  false
grLower6PostBlockerRicciEinsteinTowerStillBlocked =
  refl

grLower6PostBlockerSourcedEinsteinStillBlocked :
  GRLower6PostBlockerDownstreamInspectionReceipt.sourcedEinsteinPromotedFromLower6AndW4LocalData
    canonicalGRLower6PostBlockerDownstreamInspectionReceipt
  ≡
  false
grLower6PostBlockerSourcedEinsteinStillBlocked =
  refl
