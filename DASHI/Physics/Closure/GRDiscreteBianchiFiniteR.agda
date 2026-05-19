module DASHI.Physics.Closure.GRDiscreteBianchiFiniteR where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Combinatorics.String.LieAlgebra as StringLie
import DASHI.Physics.Constraints.Bracket as Bracket
import DASHI.Physics.Constraints.Generators as GEN
import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.GRFirstOrderGravityScope as G4
import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar

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

    flatConstantMetricFiniteRPrerequisite :
      GRFlatConstantMetricFiniteRPrerequisiteReceipt

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
    ; flatConstantMetricFiniteRPrerequisite =
        canonicalGRFlatConstantMetricFiniteRPrerequisiteReceipt
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
        "A flat constant finite-r prerequisite is typed from MinkowskiLimitReceipt, but the selected GR finite-r route still lacks non-trivial scalar algebra"
        ∷ "A selected non-flat finite-r scalar-algebra dependency request now names the scalar algebra, metric, inverse metric, inverse law, coordinate derivative, finite contraction, Christoffel law, trace, six-term cancellation, and trace=4 law"
        ∷ "GRNonFlatScalarAlgebraSurface now types the selected CarrierScalar operations, non-flat metric dependency, inverse-metric contraction laws, derivative expansion, Christoffel-from-metric law, finite contraction, trace, and six-term cancellation law"
        ∷ "No metric table, inverse metric table, coordinate derivative, trace law, or finite contraction law is bound to the selected GR finite-r metric"
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
        ∷ "This sidecar does not inhabit carrierConnectionIsLeviCivita for any selected non-flat carrier"
        ∷ "This sidecar does not convert the flat-vacuum diagnostic into finite-r GR"
        ∷ "This sidecar does not construct a non-flat connection, Ricci contraction, ricciFromBianchi theorem, vacuum Ricci-zero theorem, Einstein tensor law, or sourced Einstein law"
        ∷ "This sidecar does not construct W4MatterStressEnergyInterfaceReceipt"
        ∷ "This sidecar does not promote GR, G4, G6, W4, W5, or GR/QFT closure"
        ∷ []
    }

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
