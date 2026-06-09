module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)

import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- Carrier vocabulary
------------------------------------------------------------------------

data SourceKind : Set where
  sphereSurface : SourceKind
  bodyMeshSurface : SourceKind
  garmentPanelMesh : SourceKind
  imageCorrespondenceSurface : SourceKind

data TargetKind : Set where
  rectangleTarget : TargetKind
  squareTarget : TargetKind
  cubeFaceTarget : TargetKind
  octaFoldTarget : TargetKind
  healpixPixelTarget : TargetKind
  geodesicCellTarget : TargetKind
  uvAtlasTarget : TargetKind
  patternSheetTarget : TargetKind
  coefficientTarget : TargetKind

record SurfaceCarrier : Set₁ where
  field
    Point : Set
    Cell : Set
    sourceKind : SourceKind
    area : Cell → Nat
    adjacency : Cell → Cell → Bool

open SurfaceCarrier public

record TargetCarrier : Set₁ where
  field
    TargetPoint : Set
    TargetCell : Set
    targetKind : TargetKind

open TargetCarrier public

------------------------------------------------------------------------
-- Map contracts
------------------------------------------------------------------------

record MapContract
    (source : SurfaceCarrier)
    (target : TargetCarrier) : Set₁ where
  field
    chartMap :
      Point source →
      TargetPoint target

    pullback :
      TargetPoint target →
      Maybe (Point source)

    hasRoundTripWitness :
      Bool

    roundTripError :
      Nat

    mapBoundary :
      List String

open MapContract public

record CorrespondenceNotInverse
    (source : SurfaceCarrier)
    (target : TargetCarrier)
    (contract : MapContract source target) : Set₁ where
  field
    forwardExists :
      Set

    backwardMaybe :
      Set

    noInverseClaim :
      hasRoundTripWitness contract ≡ false →
      Set

open CorrespondenceNotInverse public

record RoundTripPromotable
    (source : SurfaceCarrier)
    (target : TargetCarrier)
    (contract : MapContract source target)
    (epsilon : Nat) : Set where
  field
    hasWitness :
      hasRoundTripWitness contract ≡ true

    errorBound :
      roundTripError contract ≤ epsilon

open RoundTripPromotable public

------------------------------------------------------------------------
-- Metrics
------------------------------------------------------------------------

data MetricAvailability : Set where
  measured : MetricAvailability
  unavailable : MetricAvailability
  notApplicable : MetricAvailability

record MetricValue : Set where
  field
    availability : MetricAvailability
    value : Nat
    reason : Maybe String

open MetricValue public

record DistortionVector : Set where
  field
    edgeLengthResidual : MetricValue
    areaResidual : MetricValue
    angleResidual : MetricValue
    foldoverCount : MetricValue
    aggregateResidual : MetricValue
    agreementDepthDistance : MetricValue
    seamLength : MetricValue
    chartCount : MetricValue
    packingWaste : MetricValue
    roundTripMetric : MetricValue
    fieldReconstructionError : MetricValue
    dartPressureScore : MetricValue
    grainAlignmentScore : MetricValue
    panelInternalVariance : MetricValue
    seamHighStrainPenalty : MetricValue
    manufacturabilityScore : MetricValue

open DistortionVector public

zeroMetric : MetricValue
zeroMetric =
  record
    { availability = measured
    ; value = 0
    ; reason = nothing
    }

notApplicableMetric : String → MetricValue
notApplicableMetric why =
  record
    { availability = notApplicable
    ; value = 0
    ; reason = just why
    }

unavailableMetric : String → MetricValue
unavailableMetric why =
  record
    { availability = unavailable
    ; value = 0
    ; reason = just why
    }

zeroDistortionVector : DistortionVector
zeroDistortionVector =
  record
    { edgeLengthResidual = zeroMetric
    ; areaResidual = zeroMetric
    ; angleResidual = zeroMetric
    ; foldoverCount = zeroMetric
    ; aggregateResidual = zeroMetric
    ; agreementDepthDistance = zeroMetric
    ; seamLength = zeroMetric
    ; chartCount = zeroMetric
    ; packingWaste = zeroMetric
    ; roundTripMetric = zeroMetric
    ; fieldReconstructionError = zeroMetric
    ; dartPressureScore = zeroMetric
    ; grainAlignmentScore = zeroMetric
    ; panelInternalVariance = zeroMetric
    ; seamHighStrainPenalty = zeroMetric
    ; manufacturabilityScore = zeroMetric
    }

------------------------------------------------------------------------
-- UFTC severity gate
------------------------------------------------------------------------

data FailureClass : Set where
  noFailure : FailureClass
  missingDependency : FailureClass
  noPullback : FailureClass
  roundTripTooHigh : FailureClass
  foldoverFailure : FailureClass
  highDistortion : FailureClass
  seamBoundaryFailure : FailureClass
  nonDiskPanelFailure : FailureClass
  manufacturingFailure : FailureClass
  externalBlackBox : FailureClass
  claimBoundaryViolation : FailureClass

failureSeverity : FailureClass → UFTC.Severity
failureSeverity noFailure = 0
failureSeverity missingDependency = 2
failureSeverity noPullback = 2
failureSeverity externalBlackBox = 3
failureSeverity highDistortion = 4
failureSeverity seamBoundaryFailure = 5
failureSeverity nonDiskPanelFailure = 6
failureSeverity roundTripTooHigh = 6
failureSeverity foldoverFailure = 8
failureSeverity manufacturingFailure = 8
failureSeverity claimBoundaryViolation = 9

failureCode : FailureClass → UFTC.Code
failureCode noFailure = UFTC.normal 0
failureCode failure = UFTC.special (failureSeverity failure)

record MethodSeverityReport : Set₁ where
  field
    failures : List FailureClass
    aggregateSeverity : UFTC.Severity
    aggregateCode : UFTC.Code
    aggregateCodeMatchesSeverity :
      UFTC.severity aggregateCode ≡ aggregateSeverity
    nonMaskingWitness :
      Set

open MethodSeverityReport public

noFailureSeverityReport : MethodSeverityReport
noFailureSeverityReport =
  record
    { failures = noFailure ∷ []
    ; aggregateSeverity = 0
    ; aggregateCode = UFTC.normal 0
    ; aggregateCodeMatchesSeverity = refl
    ; nonMaskingWitness = Nat
    }

------------------------------------------------------------------------
-- Claim boundary
------------------------------------------------------------------------

record ClaimBoundary : Set where
  field
    claimsBestDeclaredCandidate : Bool
    claimsGlobalOptimality : Bool
    claimsIsometry : Bool
    claimsTrueInverse : Bool
    claimsManufacturingAuthority : Bool
    claimsLearnedOutputPromoted : Bool

    noGlobalOptimality :
      claimsGlobalOptimality ≡ false

    noIsometry :
      claimsIsometry ≡ false

    noFakeInverse :
      claimsTrueInverse ≡ false

open ClaimBoundary public

standardBenchmarkBoundary : ClaimBoundary
standardBenchmarkBoundary =
  record
    { claimsBestDeclaredCandidate = true
    ; claimsGlobalOptimality = false
    ; claimsIsometry = false
    ; claimsTrueInverse = false
    ; claimsManufacturingAuthority = false
    ; claimsLearnedOutputPromoted = false
    ; noGlobalOptimality = refl
    ; noIsometry = refl
    ; noFakeInverse = refl
    }
