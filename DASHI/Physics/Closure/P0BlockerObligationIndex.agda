module DASHI.Physics.Closure.P0BlockerObligationIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualConsumerNextObligation as W6
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation as W1
import DASHI.Physics.Closure.ClaimGovernancePromotionObligation as W7
import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as W3
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4

------------------------------------------------------------------------
-- P0 blocker obligation index.
--
-- This module is only a narrow discoverability and validation surface.  It
-- imports the current W1-W9 obligation modules and co-locates their present
-- blocked/current statuses without promoting any lane.

data P0WorkerLane : Set where
  W1RetargetedMdlSeam :
    P0WorkerLane
  W2NaturalP2Convergence :
    P0WorkerLane
  W3EmpiricalAdequacy :
    P0WorkerLane
  W4ChemistryPhysicalCalibration :
    P0WorkerLane
  W5GRQFTConsumer :
    P0WorkerLane
  W6PNFResidualConsumer :
    P0WorkerLane
  W7ClaimGovernance :
    P0WorkerLane
  W8OriginReceipt :
    P0WorkerLane
  W9CancellationPressure :
    P0WorkerLane

record P0BlockerObligationIndex : Setω where
  field
    lanes :
      List P0WorkerLane

    w1RetargetedSeamStatus :
      W1.RetargetedFinalSeamObligationStatus

    w2NaturalP2Status :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w3AcceptedAuthorityStatus :
      W3.W3AcceptedAuthorityExternalReceiptCurrentStatus

    w4PhysicalCalibrationStatus :
      W4.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    w5GRQFTStatus :
      W5.GRQFTConsumerNextObligationCurrentStatus

    w6PNFResidualStatus :
      W6.PNFResidualConsumerMissingReceiptDiagnostic

    w7ClaimGovernanceStatus :
      W7.ClaimGovernancePromotionCurrentStatus

    w8OriginPromotionStatus :
      W8.OriginReceiptPromotionExternalCurrentStatus

    w9KnownRoute :
      W9.W9CompatibilityRoute

    indexBoundary :
      List String

p0BlockerObligationIndex :
  P0BlockerObligationIndex
p0BlockerObligationIndex =
  record
    { lanes =
        W1RetargetedMdlSeam
        ∷ W2NaturalP2Convergence
        ∷ W3EmpiricalAdequacy
        ∷ W4ChemistryPhysicalCalibration
        ∷ W5GRQFTConsumer
        ∷ W6PNFResidualConsumer
        ∷ W7ClaimGovernance
        ∷ W8OriginReceipt
        ∷ W9CancellationPressure
        ∷ []
    ; w1RetargetedSeamStatus =
        W1.canonicalRetargetedFinalSeamObligationStatus
    ; w2NaturalP2Status =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w3AcceptedAuthorityStatus =
        W3.currentW3AcceptedAuthorityExternalReceiptStatus
    ; w4PhysicalCalibrationStatus =
        W4.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; w5GRQFTStatus =
        W5.canonicalGRQFTConsumerNextObligationCurrentStatus
    ; w6PNFResidualStatus =
        W6.canonicalPNFResidualConsumerMissingReceiptDiagnostic
    ; w7ClaimGovernanceStatus =
        W7.canonicalClaimGovernancePromotionCurrentStatus
    ; w8OriginPromotionStatus =
        W8.canonicalOriginReceiptPromotionExternalCurrentStatus
    ; w9KnownRoute =
        W9.diagnosticOnly
    ; indexBoundary =
        "This index imports the W1-W9 current obligation surfaces"
        ∷ "It is a validation and discoverability surface only"
        ∷ "It does not inhabit any external authority token"
        ∷ "It does not promote empirical, chemistry, GR/QFT, PNF, origin, natural, or cancellation-pressure closure"
        ∷ []
    }

p0IndexedLanes :
  List P0WorkerLane
p0IndexedLanes =
  P0BlockerObligationIndex.lanes p0BlockerObligationIndex
