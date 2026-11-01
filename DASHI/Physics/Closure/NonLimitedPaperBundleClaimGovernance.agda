module DASHI.Physics.Closure.NonLimitedPaperBundleClaimGovernance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BlockerKillConditions as Kill

------------------------------------------------------------------------
-- Non-limited paper roadmap bundle / W7 claim-governance surface.
--
-- This module is deliberately non-promoting.  It defines the theorem-facing
-- dependency object for the non-limited paper roadmap and computes paper
-- admissibility from typed statuses, not from prose.

data RoadmapStepStatus : Set where
  acceptedByTypedReceipt :
    RoadmapStepStatus
  obligationSurfaceOnly :
    RoadmapStepStatus
  routeCandidateOnly :
    RoadmapStepStatus
  blockedByMissingAuthority :
    RoadmapStepStatus
  blockedByMissingTheorem :
    RoadmapStepStatus

data W9RoadmapStatus : Setω where
  w9AcceptedKillRoute :
    W9RoadmapStatus
  w9AcceptedMDLTerminationSeamKillRoute :
    Kill.W9KillReceipt →
    W9RoadmapStatus
  w9BlockedNoConstructiveKillRoute :
    W9RoadmapStatus
  w9RetargetCandidateOnly :
    W9RoadmapStatus

data HardCorePressurePoint : Set where
  w9MdlKillMatrixConsumer :
    HardCorePressurePoint
  g2OrientedBoundaryIncidence :
    HardCorePressurePoint
  g3CarrierOperatorContraction :
    HardCorePressurePoint
  grLeviCivitaMetricCompatibility :
    HardCorePressurePoint
  g6LaneEmbeddingOrthogonality :
    HardCorePressurePoint

data PressurePointStatus : Set where
  pressurePointClosed :
    PressurePointStatus
  pressurePointTypedButUninhabited :
    PressurePointStatus
  pressurePointRouteChangeRequired :
    PressurePointStatus
  pressurePointDownstreamGated :
    PressurePointStatus

record HardCorePressurePointStatus : Set where
  field
    pressurePoint :
      HardCorePressurePoint

    status :
      PressurePointStatus

    firstMissing :
      String

    noPromotionBoundary :
      List String

record HardCorePressurePointBundle : Set where
  field
    w9MdlConsumer :
      HardCorePressurePointStatus

    g2Boundary :
      HardCorePressurePointStatus

    g3Contraction :
      HardCorePressurePointStatus

    grMetricCompatibility :
      HardCorePressurePointStatus

    g6Embeddings :
      HardCorePressurePointStatus

canonicalHardCorePressurePointBundle :
  HardCorePressurePointBundle
canonicalHardCorePressurePointBundle =
  record
    { w9MdlConsumer =
        record
          { pressurePoint =
              w9MdlKillMatrixConsumer
          ; status =
              pressurePointRouteChangeRequired
          ; firstMissing =
              "accepted W9 kill-matrix consumer for MDLTerminationSeamWitness"
          ; noPromotionBoundary =
              "MDL termination witness does not close W9 until the kill matrix consumes it"
              ∷ []
          }
    ; g2Boundary =
        record
          { pressurePoint =
              g2OrientedBoundaryIncidence
          ; status =
              pressurePointTypedButUninhabited
          ; firstMissing =
              "oriented endpoints, signed plaquette boundary, incidence summation, and boundaryOfBoundaryZero"
          ; noPromotionBoundary =
              "primeBumpCommutes alone does not construct DiscreteCurvatureCarrier or Maxwell closure"
              ∷ []
          }
    ; g3Contraction =
        record
          { pressurePoint =
              g3CarrierOperatorContraction
          ; status =
              pressurePointTypedButUninhabited
          ; firstMissing =
              "concrete CarrierOperator, commutator closure, metric/signature binding, and IW contraction carrier"
          ; noPromotionBoundary =
              "carrier-chain records alone do not construct SchrodingerEvolutionTheorem"
              ∷ []
          }
    ; grMetricCompatibility =
        record
          { pressurePoint =
              grLeviCivitaMetricCompatibility
          ; status =
              pressurePointTypedButUninhabited
          ; firstMissing =
              "carrierConnectionIsLeviCivita and finite-r metric compatibility"
          ; noPromotionBoundary =
              "Jacobi-to-Bianchi sidecar alone does not imply finite-r Einstein closure"
              ∷ []
          }
    ; g6Embeddings =
        record
          { pressurePoint =
              g6LaneEmbeddingOrthogonality
          ; status =
              pressurePointDownstreamGated
          ; firstMissing =
              "actual Maxwell, Schrodinger, GR, and empirical lane embeddings plus orthogonality laws"
          ; noPromotionBoundary =
              "conditional Re/Im and prime-sector lemmas do not close G6"
              ∷ []
          }
    }

data ClaimPromotionBoundary : Set where
  noNonLimitedPaperPromotion :
    ClaimPromotionBoundary
  noFullUnificationPromotion :
    ClaimPromotionBoundary
  noPaperAdmissibilityByProse :
    ClaimPromotionBoundary
  noRoadmapStepUpgradeBySummary :
    ClaimPromotionBoundary

data NonLimitedPaperMissingField : Set where
  missingRoadmapGovernance :
    NonLimitedPaperMissingField
  missingW9AcceptedKillRoute :
    NonLimitedPaperMissingField
  missingW4Anchor :
    NonLimitedPaperMissingField
  missingCT18Convention :
    NonLimitedPaperMissingField
  missingPDFAuthority :
    NonLimitedPaperMissingField
  missingW4Calibration :
    NonLimitedPaperMissingField
  missingG2Closure :
    NonLimitedPaperMissingField
  missingG3Closure :
    NonLimitedPaperMissingField
  missingGRClosure :
    NonLimitedPaperMissingField
  missingG6Commutativity :
    NonLimitedPaperMissingField
  missingG4FullConsumer :
    NonLimitedPaperMissingField
  missingW7ClaimGovernance :
    NonLimitedPaperMissingField

data RoadmapGovernanceExternalGate : Set where
  w2ExternalAuthorityGate :
    RoadmapGovernanceExternalGate
  w3ExternalEvidenceAuthorityGate :
    RoadmapGovernanceExternalGate
  w4ExternalCalibrationGate :
    RoadmapGovernanceExternalGate
  w5ExternalPDFAndGRQFTGate :
    RoadmapGovernanceExternalGate

data RoadmapGovernanceInternalGate : Set where
  g2InternalDiscreteCurvatureGate :
    RoadmapGovernanceInternalGate
  g3InternalPoincareGalileiGate :
    RoadmapGovernanceInternalGate
  grInternalFiniteRBianchiGate :
    RoadmapGovernanceInternalGate

data RoadmapGovernanceDownstreamGate : Set where
  g6DownstreamCommutativityGate :
    RoadmapGovernanceDownstreamGate

data RoadmapGovernanceFinalReceiptGate : Set where
  w7FinalClaimGovernanceReceiptGate :
    RoadmapGovernanceFinalReceiptGate

record CurrentRoadmapGovernanceGapReceipt : Setω where
  field
    gapField :
      NonLimitedPaperMissingField

    gapFieldIsRoadmapGovernance :
      gapField
      ≡
      missingRoadmapGovernance

    externalGates :
      List RoadmapGovernanceExternalGate

    internalGates :
      List RoadmapGovernanceInternalGate

    downstreamGate :
      RoadmapGovernanceDownstreamGate

    finalReceiptGate :
      RoadmapGovernanceFinalReceiptGate

    w9StatusAlreadyClosed :
      W9RoadmapStatus

    decompositionSummary :
      List String

    noPaperAdmissibilityFromThisGapReceipt :
      ClaimPromotionBoundary

canonicalCurrentRoadmapGovernanceGapReceipt :
  CurrentRoadmapGovernanceGapReceipt
canonicalCurrentRoadmapGovernanceGapReceipt =
  record
    { gapField =
        missingRoadmapGovernance
    ; gapFieldIsRoadmapGovernance =
        refl
    ; externalGates =
        w2ExternalAuthorityGate
        ∷ w3ExternalEvidenceAuthorityGate
        ∷ w4ExternalCalibrationGate
        ∷ w5ExternalPDFAndGRQFTGate
        ∷ []
    ; internalGates =
        g2InternalDiscreteCurvatureGate
        ∷ g3InternalPoincareGalileiGate
        ∷ grInternalFiniteRBianchiGate
        ∷ []
    ; downstreamGate =
        g6DownstreamCommutativityGate
    ; finalReceiptGate =
        w7FinalClaimGovernanceReceiptGate
    ; w9StatusAlreadyClosed =
        w9AcceptedMDLTerminationSeamKillRoute
          Kill.canonicalMDLTerminationSeamW9KillReceipt
    ; decompositionSummary =
        "missingRoadmapGovernance now decomposes into W2/W3/W4/W5 external gates"
        ∷ "It also requires G2/G3/GR internal gates before downstream G6 commutativity"
        ∷ "W7 remains the final claim-governance receipt after those gates"
        ∷ "W9 is already represented by the accepted MDL termination seam kill receipt"
        ∷ []
    ; noPaperAdmissibilityFromThisGapReceipt =
        noRoadmapStepUpgradeBySummary
    }

data PaperAdmissibility : Set where
  paperAdmissibleFromTypedRoadmap :
    PaperAdmissibility
  paperBlocked :
    NonLimitedPaperMissingField →
    PaperAdmissibility

record NonLimitedPaperRoadmapBundle : Setω where
  field
    roadmapGovernance :
      RoadmapStepStatus

    currentRoadmapGovernanceGap :
      CurrentRoadmapGovernanceGapReceipt

    w9Status :
      W9RoadmapStatus

    hardCorePressurePoints :
      HardCorePressurePointBundle

    w4Anchor :
      RoadmapStepStatus

    ct18Convention :
      RoadmapStepStatus

    pdfAuthority :
      RoadmapStepStatus

    w4Calibration :
      RoadmapStepStatus

    g2Closure :
      RoadmapStepStatus

    g3Closure :
      RoadmapStepStatus

    grClosure :
      RoadmapStepStatus

    g6Commutativity :
      RoadmapStepStatus

    g4FullConsumer :
      RoadmapStepStatus

    w7ClaimGovernance :
      RoadmapStepStatus

    claimPromotionBoundary :
      List ClaimPromotionBoundary

    roadmapNotes :
      List String

statusMissing :
  NonLimitedPaperMissingField →
  RoadmapStepStatus →
  PaperAdmissibility →
  PaperAdmissibility
statusMissing missing acceptedByTypedReceipt next =
  next
statusMissing missing obligationSurfaceOnly next =
  paperBlocked missing
statusMissing missing routeCandidateOnly next =
  paperBlocked missing
statusMissing missing blockedByMissingAuthority next =
  paperBlocked missing
statusMissing missing blockedByMissingTheorem next =
  paperBlocked missing

w9Missing :
  W9RoadmapStatus →
  PaperAdmissibility →
  PaperAdmissibility
w9Missing w9AcceptedKillRoute next =
  next
w9Missing (w9AcceptedMDLTerminationSeamKillRoute receipt) next =
  next
w9Missing w9BlockedNoConstructiveKillRoute next =
  paperBlocked missingW9AcceptedKillRoute
w9Missing w9RetargetCandidateOnly next =
  paperBlocked missingW9AcceptedKillRoute

paperAdmissibility :
  NonLimitedPaperRoadmapBundle →
  PaperAdmissibility
paperAdmissibility bundle =
  statusMissing
    missingRoadmapGovernance
    (NonLimitedPaperRoadmapBundle.roadmapGovernance bundle)
    (w9Missing
      (NonLimitedPaperRoadmapBundle.w9Status bundle)
      (statusMissing
        missingW4Anchor
        (NonLimitedPaperRoadmapBundle.w4Anchor bundle)
        (statusMissing
          missingCT18Convention
          (NonLimitedPaperRoadmapBundle.ct18Convention bundle)
          (statusMissing
            missingPDFAuthority
            (NonLimitedPaperRoadmapBundle.pdfAuthority bundle)
            (statusMissing
              missingW4Calibration
              (NonLimitedPaperRoadmapBundle.w4Calibration bundle)
              (statusMissing
                missingG2Closure
                (NonLimitedPaperRoadmapBundle.g2Closure bundle)
                (statusMissing
                  missingG3Closure
                  (NonLimitedPaperRoadmapBundle.g3Closure bundle)
                  (statusMissing
                    missingGRClosure
                    (NonLimitedPaperRoadmapBundle.grClosure bundle)
                    (statusMissing
                      missingG6Commutativity
                      (NonLimitedPaperRoadmapBundle.g6Commutativity bundle)
                      (statusMissing
                        missingG4FullConsumer
                        (NonLimitedPaperRoadmapBundle.g4FullConsumer bundle)
                        (statusMissing
                          missingW7ClaimGovernance
                          (NonLimitedPaperRoadmapBundle.w7ClaimGovernance bundle)
                          paperAdmissibleFromTypedRoadmap)))))))))))

record NonLimitedPaperClaimGovernanceReceipt : Setω where
  field
    roadmapBundle :
      NonLimitedPaperRoadmapBundle

    computedAdmissibility :
      PaperAdmissibility

    computedFromTypedStatuses :
      paperAdmissibility roadmapBundle
      ≡
      computedAdmissibility

    consumedRoadmapGovernanceGap :
      CurrentRoadmapGovernanceGapReceipt

    theoremFacingDependencyObject :
      String

    noClaimPromotion :
      List ClaimPromotionBoundary

    governanceBoundary :
      List String

canonicalNonLimitedPaperRoadmapBundle :
  NonLimitedPaperRoadmapBundle
canonicalNonLimitedPaperRoadmapBundle =
  record
    { roadmapGovernance =
        obligationSurfaceOnly
    ; currentRoadmapGovernanceGap =
        canonicalCurrentRoadmapGovernanceGapReceipt
    ; w9Status =
        w9AcceptedMDLTerminationSeamKillRoute
          Kill.canonicalMDLTerminationSeamW9KillReceipt
    ; hardCorePressurePoints =
        canonicalHardCorePressurePointBundle
    ; w4Anchor =
        obligationSurfaceOnly
    ; ct18Convention =
        blockedByMissingAuthority
    ; pdfAuthority =
        blockedByMissingAuthority
    ; w4Calibration =
        blockedByMissingAuthority
    ; g2Closure =
        obligationSurfaceOnly
    ; g3Closure =
        obligationSurfaceOnly
    ; grClosure =
        routeCandidateOnly
    ; g6Commutativity =
        routeCandidateOnly
    ; g4FullConsumer =
        obligationSurfaceOnly
    ; w7ClaimGovernance =
        obligationSurfaceOnly
    ; claimPromotionBoundary =
        noNonLimitedPaperPromotion
        ∷ noFullUnificationPromotion
        ∷ noPaperAdmissibilityByProse
        ∷ noRoadmapStepUpgradeBySummary
        ∷ []
    ; roadmapNotes =
        "12-step non-limited paper roadmap is represented as typed status fields"
        ∷ "Current bundle is intentionally non-promoting"
        ∷ "missingRoadmapGovernance decomposes into W2/W3/W4/W5 external gates; G2/G3/GR internal gates; G6 downstream; and W7 final receipt"
        ∷ "W9 has an accepted MDL termination seam kill route; W4 anchor/calibration and CT18/PDF authority remain missing or obligation-only"
        ∷ "G2, G3, GR, G6, G4 full consumer, and W7 claim governance are not accepted closures here"
        ∷ []
    }

canonicalNonLimitedPaperAdmissibility :
  PaperAdmissibility
canonicalNonLimitedPaperAdmissibility =
  paperAdmissibility canonicalNonLimitedPaperRoadmapBundle

canonicalNonLimitedPaperClaimGovernanceReceipt :
  NonLimitedPaperClaimGovernanceReceipt
canonicalNonLimitedPaperClaimGovernanceReceipt =
  record
    { roadmapBundle =
        canonicalNonLimitedPaperRoadmapBundle
    ; computedAdmissibility =
        paperBlocked missingRoadmapGovernance
    ; computedFromTypedStatuses =
        refl
    ; consumedRoadmapGovernanceGap =
        NonLimitedPaperRoadmapBundle.currentRoadmapGovernanceGap
          canonicalNonLimitedPaperRoadmapBundle
    ; theoremFacingDependencyObject =
        "NonLimitedPaperRoadmapBundle"
    ; noClaimPromotion =
        noNonLimitedPaperPromotion
        ∷ noFullUnificationPromotion
        ∷ noPaperAdmissibilityByProse
        ∷ noRoadmapStepUpgradeBySummary
        ∷ []
    ; governanceBoundary =
        "Admissibility is computed from the 12 typed roadmap statuses"
        ∷ "missingRoadmapGovernance is the current typed gap receipt: W2/W3/W4/W5 external, G2/G3/GR internal, G6 downstream, W7 final receipt"
        ∷ "This surface consumes the accepted W9 MDL termination seam kill receipt but does not construct W4, CT18/PDF, G2, G3, GR, G6, G4, or W7 receipts"
        ∷ "Current admissibility is blocked at missingRoadmapGovernance"
        ∷ []
    }

canonicalNonLimitedPaperMissingField :
  NonLimitedPaperMissingField
canonicalNonLimitedPaperMissingField =
  missingRoadmapGovernance
