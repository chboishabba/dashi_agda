module DASHI.Physics.Closure.W7ClaimGovernanceReceiptRequest where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- W7 claim-governance receipt request.
--
-- This module records the current typed gate board for the W7 final
-- claim-governance receipt.  It is deliberately non-promoting: W9 is closed,
-- but W2/W3/W4/W5 still require external authority, G2/G3/GR remain internal
-- pending, and G6 remains downstream pending.

data GateStatus : Set where
  gateClosed :
    GateStatus
  externalRequired :
    GateStatus
  internalPending :
    GateStatus
  downstreamPending :
    GateStatus

data W7ClaimGovernanceGate : Set where
  W9Gate :
    W7ClaimGovernanceGate
  W2Gate :
    W7ClaimGovernanceGate
  W3Gate :
    W7ClaimGovernanceGate
  W4Gate :
    W7ClaimGovernanceGate
  W5Gate :
    W7ClaimGovernanceGate
  G2Gate :
    W7ClaimGovernanceGate
  G3Gate :
    W7ClaimGovernanceGate
  GRGate :
    W7ClaimGovernanceGate
  G6Gate :
    W7ClaimGovernanceGate

record GateReport : Set where
  field
    gate :
      W7ClaimGovernanceGate

    status :
      GateStatus

    firstMissing :
      String

    nonPromotionBoundary :
      List String

record W7ClaimGovernanceCurrentGateBoard : Set where
  field
    w9 :
      GateReport

    w2 :
      GateReport

    w3 :
      GateReport

    w4 :
      GateReport

    w5 :
      GateReport

    g2 :
      GateReport

    g3 :
      GateReport

    gr :
      GateReport

    g6 :
      GateReport

record AllW7ClaimGovernanceGatesClosed
  (board : W7ClaimGovernanceCurrentGateBoard) : Set where
  field
    w9Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.w9 board)
      ≡
      gateClosed

    w2Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.w2 board)
      ≡
      gateClosed

    w3Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.w3 board)
      ≡
      gateClosed

    w4Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.w4 board)
      ≡
      gateClosed

    w5Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.w5 board)
      ≡
      gateClosed

    g2Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.g2 board)
      ≡
      gateClosed

    g3Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.g3 board)
      ≡
      gateClosed

    grClosed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.gr board)
      ≡
      gateClosed

    g6Closed :
      GateReport.status (W7ClaimGovernanceCurrentGateBoard.g6 board)
      ≡
      gateClosed

data W7RequestStatus : Set where
  blockedAwaitingGateClosure :
    W7RequestStatus
  readyOnlyWhenAllGatesClosed :
    W7RequestStatus

data W7PaperAdmissibilityRequestResult : Set where
  paperAdmissibilityBlocked :
    W7ClaimGovernanceGate →
    W7PaperAdmissibilityRequestResult
  paperAdmissibilityAvailableOnlyWithAllGatesClosed :
    {board : W7ClaimGovernanceCurrentGateBoard} →
    AllW7ClaimGovernanceGatesClosed board →
    W7PaperAdmissibilityRequestResult

record W7ClaimGovernanceReceiptRequest : Setω where
  field
    status :
      W7RequestStatus

    gateBoard :
      W7ClaimGovernanceCurrentGateBoard

    currentPaperAdmissibility :
      W7PaperAdmissibilityRequestResult

    w7ReceiptConstructedHere :
      Bool

    w7ReceiptConstructedHereIsFalse :
      w7ReceiptConstructedHere ≡ false

    nonPromotionBoundary :
      List String

    allGatesClosedPrerequisite :
      String

    impossibleCurrentAllGatesClosed :
      AllW7ClaimGovernanceGatesClosed gateBoard →
      ⊥

canonicalW7ClaimGovernanceCurrentGateBoard :
  W7ClaimGovernanceCurrentGateBoard
canonicalW7ClaimGovernanceCurrentGateBoard =
  record
    { w9 =
        record
          { gate =
              W9Gate
          ; status =
              gateClosed
          ; firstMissing =
              "none: W9 accepted MDL termination seam kill route is closed"
          ; nonPromotionBoundary =
              "W9 closure alone does not authorize W7 claim governance"
              ∷ []
          }
    ; w2 =
        record
          { gate =
              W2Gate
          ; status =
              externalRequired
          ; firstMissing =
              "external W2 promotion authority / NaturalP2 convergence receipt"
          ; nonPromotionBoundary =
              "W2 is not self-issued by this request skeleton"
              ∷ []
          }
    ; w3 =
        record
          { gate =
              W3Gate
          ; status =
              externalRequired
          ; firstMissing =
              "external W3 accepted empirical evidence authority"
          ; nonPromotionBoundary =
              "W3 empirical authority is not fabricated here"
              ∷ []
          }
    ; w4 =
        record
          { gate =
              W4Gate
          ; status =
              externalRequired
          ; firstMissing =
              "external W4 physical calibration authority and receipt"
          ; nonPromotionBoundary =
              "W4 calibration is not promoted from a surrogate Nat surface"
              ∷ []
          }
    ; w5 =
        record
          { gate =
              W5Gate
          ; status =
              externalRequired
          ; firstMissing =
              "external W5 PDF / GR-QFT carrier and validation authority"
          ; nonPromotionBoundary =
              "W5 PDF and GR-QFT closure are not constructed here"
              ∷ []
          }
    ; g2 =
        record
          { gate =
              G2Gate
          ; status =
              internalPending
          ; firstMissing =
              "internal G2 discrete-curvature closure"
          ; nonPromotionBoundary =
              "G2 carrier status is pending, not accepted closure"
              ∷ []
          }
    ; g3 =
        record
          { gate =
              G3Gate
          ; status =
              internalPending
          ; firstMissing =
              "internal G3 Poincare-Galilei carrier-chain closure"
          ; nonPromotionBoundary =
              "G3 carrier status is pending, not accepted closure"
              ∷ []
          }
    ; gr =
        record
          { gate =
              GRGate
          ; status =
              internalPending
          ; firstMissing =
              "internal GR finite-r Bianchi / metric-compatibility closure"
          ; nonPromotionBoundary =
              "GR route status is pending, not accepted closure"
              ∷ []
          }
    ; g6 =
        record
          { gate =
              G6Gate
          ; status =
              downstreamPending
          ; firstMissing =
              "downstream G6 commutativity after external and internal gates"
          ; nonPromotionBoundary =
              "G6 cannot be closed before its upstream lane receipts are closed"
              ∷ []
          }
    }

currentBoardHasExternalRequiredW2 :
  GateReport.status
    (W7ClaimGovernanceCurrentGateBoard.w2
      canonicalW7ClaimGovernanceCurrentGateBoard)
  ≡
  externalRequired
currentBoardHasExternalRequiredW2 =
  refl

currentBoardNotAllClosed :
  AllW7ClaimGovernanceGatesClosed
    canonicalW7ClaimGovernanceCurrentGateBoard →
  ⊥
currentBoardNotAllClosed allClosed =
  let open AllW7ClaimGovernanceGatesClosed allClosed in
  externalRequired≠closed w2Closed
  where
    externalRequired≠closed :
      externalRequired ≡ gateClosed →
      ⊥
    externalRequired≠closed ()

canonicalW7ClaimGovernanceReceiptRequest :
  W7ClaimGovernanceReceiptRequest
canonicalW7ClaimGovernanceReceiptRequest =
  record
    { status =
        blockedAwaitingGateClosure
    ; gateBoard =
        canonicalW7ClaimGovernanceCurrentGateBoard
    ; currentPaperAdmissibility =
        paperAdmissibilityBlocked W2Gate
    ; w7ReceiptConstructedHere =
        false
    ; w7ReceiptConstructedHereIsFalse =
        refl
    ; nonPromotionBoundary =
        "This module records a W7 request skeleton only"
        ∷ "It does not export paperAdmissible or an inhabited W7 claim-governance receipt"
        ∷ "Paper admissibility is available only through AllW7ClaimGovernanceGatesClosed"
        ∷ "Current board blocks at W2/W3/W4/W5 external gates, G2/G3/GR internal gates, and downstream G6"
        ∷ []
    ; allGatesClosedPrerequisite =
        "W9, W2, W3, W4, W5, G2, G3, GR, and G6 must all be gateClosed before W7 can promote"
    ; impossibleCurrentAllGatesClosed =
        currentBoardNotAllClosed
    }
