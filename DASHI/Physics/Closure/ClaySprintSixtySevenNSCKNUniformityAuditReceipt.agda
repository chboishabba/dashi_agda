module DASHI.Physics.Closure.ClaySprintSixtySevenNSCKNUniformityAuditReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSixtySevenNSCKNLemmaTestLadderReceipt
  as Sprint67CKN

------------------------------------------------------------------------
-- Sprint 67B NS CKN uniformity audit receipt.
--
-- Sprint 66 sampled hot spots and found decay under zoom.  Sprint 67B records
-- the next proof-facing diagnostic: audit every candidate ascended cylinder,
-- cluster persistence, pressure fraction, epsilon sweep, and N/cadence
-- stability.  This receipt is a test contract only.

Scalar : Set
Scalar = String

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

data Sprint67BRouteDecision : Set where
  hotspotEvidenceFavorable :
    Sprint67BRouteDecision
  sampledFailureRateNotTheoremZero :
    Sprint67BRouteDecision
  boundedAscendedCylinderAuditComputed :
    Sprint67BRouteDecision
  pressureContributionBoundedDiagnostic :
    Sprint67BRouteDecision
  noPersistentClustersObservedDiagnostic :
    Sprint67BRouteDecision
  noClayPromotion :
    Sprint67BRouteDecision

canonicalSprint67BRouteDecisions :
  List Sprint67BRouteDecision
canonicalSprint67BRouteDecisions =
  hotspotEvidenceFavorable
  ∷ sampledFailureRateNotTheoremZero
  ∷ boundedAscendedCylinderAuditComputed
  ∷ pressureContributionBoundedDiagnostic
  ∷ noPersistentClustersObservedDiagnostic
  ∷ noClayPromotion
  ∷ []

data Sprint67BOpenGate : Set where
  gateAllCandidateAscendedCylinders :
    Sprint67BOpenGate
  gateScaleEpsilonPersistenceCalibration :
    Sprint67BOpenGate
  gatePressureFractionBound :
    Sprint67BOpenGate
  gateClusterPersistenceBound :
    Sprint67BOpenGate
  gateMaxCKNStableUnderN :
    Sprint67BOpenGate
  gateUniformCKNEpsilonTheorem :
    Sprint67BOpenGate
  gateSuitableWeakSolutionBridge :
    Sprint67BOpenGate
  gateNoFiniteTimeBlowup :
    Sprint67BOpenGate

canonicalSprint67BOpenGates :
  List Sprint67BOpenGate
canonicalSprint67BOpenGates =
  gateAllCandidateAscendedCylinders
  ∷ gateScaleEpsilonPersistenceCalibration
  ∷ gatePressureFractionBound
  ∷ gateClusterPersistenceBound
  ∷ gateMaxCKNStableUnderN
  ∷ gateUniformCKNEpsilonTheorem
  ∷ gateSuitableWeakSolutionBridge
  ∷ gateNoFiniteTimeBlowup
  ∷ []

data Sprint67BOutputSurface : Set where
  byCylinderCSV :
    Sprint67BOutputSurface
  byClusterCSV :
    Sprint67BOutputSurface
  summaryJSON :
    Sprint67BOutputSurface

canonicalSprint67BOutputSurfaces :
  List Sprint67BOutputSurface
canonicalSprint67BOutputSurfaces =
  byCylinderCSV
  ∷ byClusterCSV
  ∷ summaryJSON
  ∷ []

data Sprint67BPromotion : Set where

sprint67BPromotionImpossibleHere :
  Sprint67BPromotion →
  ⊥
sprint67BPromotionImpossibleHere ()

cknUniformityQuantity : String
cknUniformityQuantity =
  "C(r,x0,t0) = r^-2 integral_{t0-r^2}^{t0} integral_{B_r(x0)} (|u|^3 + |p|^(3/2)) dx dt"

sprint67BOutputContract : String
sprint67BOutputContract =
  "ns_sprint67_ckn_uniformity_by_cylinder.csv, ns_sprint67_ckn_uniformity_by_cluster.csv, ns_sprint67_ckn_uniformity_summary.json"

sprint67BRouteLabels : String
sprint67BRouteLabels =
  "CKN_UNIFORM_DECAY_SUPPORTED, CKN_LOCALIZED_PERSISTENT_PLATEAU, CKN_CONCENTRATION_CANDIDATE_FOUND, CKN_PRESSURE_DOMINATED_ARTIFACT, CKN_INCONCLUSIVE_NEEDS_HIGHER_N"

sprint67BBoundary : String
sprint67BBoundary =
  "Sprint 67B records favorable bounded CKN uniformity evidence: 1536/1536 selected ascended cylinders decay under zoom, with 120 clusters, no flat or concentrating cylinders, pressure_fraction_max~=0.1307, and max_C_total decreasing from N32 to N64. This is diagnostic only; unbounded candidate coverage, theorem-level pressure control, N-ladder stability beyond tested artifacts, uniform CKN epsilon, suitable weak solution bridge, no-blowup, and Clay/NS promotion remain unproved."

record ClaySprintSixtySevenNSCKNUniformityAuditReceipt : Set₁ where
  field
    sprint67CKNNoPromotion :
      Sprint67CKN.clayNavierStokesPromoted ≡ false

    cknRouteInheritedOpen :
      Bool
    cknRouteInheritedOpenIsTrue :
      cknRouteInheritedOpen ≡ true

    pooledHotspotDecayCount :
      Nat
    pooledHotspotDecayCountIs80 :
      pooledHotspotDecayCount ≡ 80

    pooledHotspotConcentratingCount :
      Nat
    pooledHotspotConcentratingCountIs0 :
      pooledHotspotConcentratingCount ≡ 0

    wilsonFailureUpper95 :
      Scalar
    wilsonFailureUpper95IsCanonical :
      wilsonFailureUpper95 ≡ "0.0458"

    fixedBlockAscendedSixRun :
      Scalar
    fixedBlockAscendedSixRunIsCanonical :
      fixedBlockAscendedSixRun ≡ "0.43666666666666665"

    fixedBlockAscendedN128Seed0 :
      Scalar
    fixedBlockAscendedN128Seed0IsCanonical :
      fixedBlockAscendedN128Seed0 ≡ "0.116"

    fixedBlockAscendedAbsoluteDrop :
      Scalar
    fixedBlockAscendedAbsoluteDropIsCanonical :
      fixedBlockAscendedAbsoluteDrop ≡ "0.32066666666666666"

    fixedBlockAscendedRelativeDrop :
      Scalar
    fixedBlockAscendedRelativeDropIsCanonical :
      fixedBlockAscendedRelativeDrop ≡ "0.7343511450381679"

    boundedCylinderCount :
      Nat
    boundedCylinderCountIs1536 :
      boundedCylinderCount ≡ 1536

    boundedClusterCount :
      Nat
    boundedClusterCountIs120 :
      boundedClusterCount ≡ 120

    boundedDecayingCylinderCount :
      Nat
    boundedDecayingCylinderCountIs1536 :
      boundedDecayingCylinderCount ≡ 1536

    boundedFlatCylinderCount :
      Nat
    boundedFlatCylinderCountIs0 :
      boundedFlatCylinderCount ≡ 0

    boundedConcentratingCylinderCount :
      Nat
    boundedConcentratingCylinderCountIs0 :
      boundedConcentratingCylinderCount ≡ 0

    boundedPersistentClusterCount :
      Nat
    boundedPersistentClusterCountIs0 :
      boundedPersistentClusterCount ≡ 0

    boundedPressureFractionMax :
      Scalar
    boundedPressureFractionMaxIsCanonical :
      boundedPressureFractionMax ≡ "0.13074814940071125"

    boundedMaxCTotalN32 :
      Scalar
    boundedMaxCTotalN32IsCanonical :
      boundedMaxCTotalN32 ≡ "0.6157542190448191"

    boundedMaxCTotalN64 :
      Scalar
    boundedMaxCTotalN64IsCanonical :
      boundedMaxCTotalN64 ≡ "0.2939492011581624"

    boundedMaxCKNGrowsWithN :
      Bool
    boundedMaxCKNGrowsWithNIsFalse :
      boundedMaxCKNGrowsWithN ≡ false

    boundedAscendedCylinderUniformityComputed :
      Bool
    boundedAscendedCylinderUniformityComputedIsTrue :
      boundedAscendedCylinderUniformityComputed ≡ true

    clusterPersistenceComputed :
      Bool
    clusterPersistenceComputedIsTrue :
      clusterPersistenceComputed ≡ true

    pressureFractionBounded :
      Bool
    pressureFractionBoundedIsTrue :
      pressureFractionBounded ≡ true

    maxCKNStableUnderN :
      Bool
    maxCKNStableUnderNIsTrue :
      maxCKNStableUnderN ≡ true

    uniformCKNEpsilonBoundProved :
      Bool
    uniformCKNEpsilonBoundProvedIsFalse :
      uniformCKNEpsilonBoundProved ≡ false

    suitableWeakSolutionBridgeProved :
      Bool
    suitableWeakSolutionBridgeProvedIsFalse :
      suitableWeakSolutionBridgeProved ≡ false

    noFiniteTimeBlowup :
      Bool
    noFiniteTimeBlowupIsFalse :
      noFiniteTimeBlowup ≡ false

    cknQuantity :
      String
    cknQuantityIsCanonical :
      cknQuantity ≡ cknUniformityQuantity

    outputContract :
      String
    outputContractIsCanonical :
      outputContract ≡ sprint67BOutputContract

    routeLabels :
      String
    routeLabelsAreCanonical :
      routeLabels ≡ sprint67BRouteLabels

    outputSurfaces :
      List Sprint67BOutputSurface
    outputSurfacesAreCanonical :
      outputSurfaces ≡ canonicalSprint67BOutputSurfaces

    routeDecisions :
      List Sprint67BRouteDecision
    routeDecisionsAreCanonical :
      routeDecisions ≡ canonicalSprint67BRouteDecisions

    openGates :
      List Sprint67BOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint67BOpenGates

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List Sprint67BPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint67BPromotion → ⊥

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint67BBoundary

canonicalSprint67BReceipt :
  ClaySprintSixtySevenNSCKNUniformityAuditReceipt
canonicalSprint67BReceipt =
  record
    { sprint67CKNNoPromotion = refl
    ; cknRouteInheritedOpen = true
    ; cknRouteInheritedOpenIsTrue = refl
    ; pooledHotspotDecayCount = 80
    ; pooledHotspotDecayCountIs80 = refl
    ; pooledHotspotConcentratingCount = 0
    ; pooledHotspotConcentratingCountIs0 = refl
    ; wilsonFailureUpper95 = "0.0458"
    ; wilsonFailureUpper95IsCanonical = refl
    ; fixedBlockAscendedSixRun = "0.43666666666666665"
    ; fixedBlockAscendedSixRunIsCanonical = refl
    ; fixedBlockAscendedN128Seed0 = "0.116"
    ; fixedBlockAscendedN128Seed0IsCanonical = refl
    ; fixedBlockAscendedAbsoluteDrop = "0.32066666666666666"
    ; fixedBlockAscendedAbsoluteDropIsCanonical = refl
    ; fixedBlockAscendedRelativeDrop = "0.7343511450381679"
    ; fixedBlockAscendedRelativeDropIsCanonical = refl
    ; boundedCylinderCount = 1536
    ; boundedCylinderCountIs1536 = refl
    ; boundedClusterCount = 120
    ; boundedClusterCountIs120 = refl
    ; boundedDecayingCylinderCount = 1536
    ; boundedDecayingCylinderCountIs1536 = refl
    ; boundedFlatCylinderCount = 0
    ; boundedFlatCylinderCountIs0 = refl
    ; boundedConcentratingCylinderCount = 0
    ; boundedConcentratingCylinderCountIs0 = refl
    ; boundedPersistentClusterCount = 0
    ; boundedPersistentClusterCountIs0 = refl
    ; boundedPressureFractionMax = "0.13074814940071125"
    ; boundedPressureFractionMaxIsCanonical = refl
    ; boundedMaxCTotalN32 = "0.6157542190448191"
    ; boundedMaxCTotalN32IsCanonical = refl
    ; boundedMaxCTotalN64 = "0.2939492011581624"
    ; boundedMaxCTotalN64IsCanonical = refl
    ; boundedMaxCKNGrowsWithN = false
    ; boundedMaxCKNGrowsWithNIsFalse = refl
    ; boundedAscendedCylinderUniformityComputed = true
    ; boundedAscendedCylinderUniformityComputedIsTrue = refl
    ; clusterPersistenceComputed = true
    ; clusterPersistenceComputedIsTrue = refl
    ; pressureFractionBounded = true
    ; pressureFractionBoundedIsTrue = refl
    ; maxCKNStableUnderN = true
    ; maxCKNStableUnderNIsTrue = refl
    ; uniformCKNEpsilonBoundProved = false
    ; uniformCKNEpsilonBoundProvedIsFalse = refl
    ; suitableWeakSolutionBridgeProved = false
    ; suitableWeakSolutionBridgeProvedIsFalse = refl
    ; noFiniteTimeBlowup = false
    ; noFiniteTimeBlowupIsFalse = refl
    ; cknQuantity = cknUniformityQuantity
    ; cknQuantityIsCanonical = refl
    ; outputContract = sprint67BOutputContract
    ; outputContractIsCanonical = refl
    ; routeLabels = sprint67BRouteLabels
    ; routeLabelsAreCanonical = refl
    ; outputSurfaces = canonicalSprint67BOutputSurfaces
    ; outputSurfacesAreCanonical = refl
    ; routeDecisions = canonicalSprint67BRouteDecisions
    ; routeDecisionsAreCanonical = refl
    ; openGates = canonicalSprint67BOpenGates
    ; openGatesAreCanonical = refl
    ; clayNavierStokesPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint67BPromotionImpossibleHere
    ; boundary = sprint67BBoundary
    ; boundaryIsCanonical = refl
    }
