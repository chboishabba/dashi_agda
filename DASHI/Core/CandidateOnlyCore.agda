module DASHI.Core.CandidateOnlyCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable candidate-only core.
--
-- This core factors the common row shape for proposal, diagnostic, bridge,
-- role, vector, ranking, functional, and operator lanes.  A row in this core
-- is only a candidate surface.  It records that the surface is candidate-only,
-- not promoted, and carries no local truth, support, admissibility, trading,
-- runtime, or theorem authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Candidate-only vocabulary.

data CandidateOnlyKind : Set where
  rowCandidateKind :
    CandidateOnlyKind

  proposalCandidateKind :
    CandidateOnlyKind

  diagnosticCandidateKind :
    CandidateOnlyKind

  bridgeCandidateKind :
    CandidateOnlyKind

  roleCandidateKind :
    CandidateOnlyKind

  vectorCandidateKind :
    CandidateOnlyKind

  rankingCandidateKind :
    CandidateOnlyKind

  functionalCandidateKind :
    CandidateOnlyKind

  operatorCandidateKind :
    CandidateOnlyKind

  namedCandidateKind :
    String →
    CandidateOnlyKind

canonicalCandidateOnlyKinds : List CandidateOnlyKind
canonicalCandidateOnlyKinds =
  rowCandidateKind
  ∷ proposalCandidateKind
  ∷ diagnosticCandidateKind
  ∷ bridgeCandidateKind
  ∷ roleCandidateKind
  ∷ vectorCandidateKind
  ∷ rankingCandidateKind
  ∷ functionalCandidateKind
  ∷ operatorCandidateKind
  ∷ []

canonicalCandidateOnlyKindCount : Nat
canonicalCandidateOnlyKindCount =
  listCount canonicalCandidateOnlyKinds

data CandidateOnlyStatus : Set where
  rowCandidateOnlyStatus :
    CandidateOnlyStatus

  proposalCandidateOnlyStatus :
    CandidateOnlyStatus

  diagnosticCandidateOnlyStatus :
    CandidateOnlyStatus

  bridgeCandidateOnlyStatus :
    CandidateOnlyStatus

  roleCandidateOnlyStatus :
    CandidateOnlyStatus

  vectorCandidateOnlyStatus :
    CandidateOnlyStatus

  rankingCandidateOnlyStatus :
    CandidateOnlyStatus

  functionalCandidateOnlyStatus :
    CandidateOnlyStatus

  operatorCandidateOnlyStatus :
    CandidateOnlyStatus

  namedCandidateOnlyStatus :
    String →
    CandidateOnlyStatus

candidateStatusKind :
  CandidateOnlyStatus →
  CandidateOnlyKind
candidateStatusKind rowCandidateOnlyStatus =
  rowCandidateKind
candidateStatusKind proposalCandidateOnlyStatus =
  proposalCandidateKind
candidateStatusKind diagnosticCandidateOnlyStatus =
  diagnosticCandidateKind
candidateStatusKind bridgeCandidateOnlyStatus =
  bridgeCandidateKind
candidateStatusKind roleCandidateOnlyStatus =
  roleCandidateKind
candidateStatusKind vectorCandidateOnlyStatus =
  vectorCandidateKind
candidateStatusKind rankingCandidateOnlyStatus =
  rankingCandidateKind
candidateStatusKind functionalCandidateOnlyStatus =
  functionalCandidateKind
candidateStatusKind operatorCandidateOnlyStatus =
  operatorCandidateKind
candidateStatusKind (namedCandidateOnlyStatus label) =
  namedCandidateKind label

canonicalCandidateOnlyStatuses : List CandidateOnlyStatus
canonicalCandidateOnlyStatuses =
  rowCandidateOnlyStatus
  ∷ proposalCandidateOnlyStatus
  ∷ diagnosticCandidateOnlyStatus
  ∷ bridgeCandidateOnlyStatus
  ∷ roleCandidateOnlyStatus
  ∷ vectorCandidateOnlyStatus
  ∷ rankingCandidateOnlyStatus
  ∷ functionalCandidateOnlyStatus
  ∷ operatorCandidateOnlyStatus
  ∷ []

canonicalCandidateOnlyStatusCount : Nat
canonicalCandidateOnlyStatusCount =
  listCount canonicalCandidateOnlyStatuses

data CandidateAuthorityLane : Set where
  truthAuthorityLane :
    CandidateAuthorityLane

  supportAuthorityLane :
    CandidateAuthorityLane

  admissibilityAuthorityLane :
    CandidateAuthorityLane

  tradingAuthorityLane :
    CandidateAuthorityLane

  runtimeAuthorityLane :
    CandidateAuthorityLane

  theoremAuthorityLane :
    CandidateAuthorityLane

canonicalCandidateAuthorityLanes : List CandidateAuthorityLane
canonicalCandidateAuthorityLanes =
  truthAuthorityLane
  ∷ supportAuthorityLane
  ∷ admissibilityAuthorityLane
  ∷ tradingAuthorityLane
  ∷ runtimeAuthorityLane
  ∷ theoremAuthorityLane
  ∷ []

------------------------------------------------------------------------
-- Candidate-only rows and receipts.

record CandidateOnlyRow : Set where
  constructor candidateOnlyRow
  field
    candidateRowLabel :
      String

    candidateRowOwner :
      String

    candidateRowSurface :
      String

    candidateRowKind :
      CandidateOnlyKind

    candidateRowStatus :
      CandidateOnlyStatus

    candidateRowStatement :
      String

    candidateRowRemainingGap :
      String

    candidateOnly :
      Bool

    promoted :
      Bool

    carriesTruthAuthority :
      Bool

    carriesSupportAuthority :
      Bool

    carriesAdmissibilityAuthority :
      Bool

    carriesTradingAuthority :
      Bool

    carriesRuntimeAuthority :
      Bool

    carriesTheoremAuthority :
      Bool

open CandidateOnlyRow public

record CandidateOnlyReceipt
  (row : CandidateOnlyRow) :
  Set where
  constructor candidateOnlyReceipt
  field
    receiptCandidateOnlyIsTrue :
      candidateOnly row ≡ true

    receiptPromotedIsFalse :
      promoted row ≡ false

    receiptNoTruthAuthority :
      carriesTruthAuthority row ≡ false

    receiptNoSupportAuthority :
      carriesSupportAuthority row ≡ false

    receiptNoAdmissibilityAuthority :
      carriesAdmissibilityAuthority row ≡ false

    receiptNoTradingAuthority :
      carriesTradingAuthority row ≡ false

    receiptNoRuntimeAuthority :
      carriesRuntimeAuthority row ≡ false

    receiptNoTheoremAuthority :
      carriesTheoremAuthority row ≡ false

open CandidateOnlyReceipt public

mkCandidateOnlyRow :
  String →
  String →
  String →
  CandidateOnlyKind →
  CandidateOnlyStatus →
  String →
  String →
  CandidateOnlyRow
mkCandidateOnlyRow
  label
  owner
  surface
  kind
  status
  statement
  remainingGap =
  candidateOnlyRow
    label
    owner
    surface
    kind
    status
    statement
    remainingGap
    true
    false
    false
    false
    false
    false
    false
    false

mkCandidateOnlyReceipt :
  (row : CandidateOnlyRow) →
  candidateOnly row ≡ true →
  promoted row ≡ false →
  carriesTruthAuthority row ≡ false →
  carriesSupportAuthority row ≡ false →
  carriesAdmissibilityAuthority row ≡ false →
  carriesTradingAuthority row ≡ false →
  carriesRuntimeAuthority row ≡ false →
  carriesTheoremAuthority row ≡ false →
  CandidateOnlyReceipt row
mkCandidateOnlyReceipt
  row
  candidateProof
  promotedProof
  truthProof
  supportProof
  admissibilityProof
  tradingProof
  runtimeProof
  theoremProof =
  candidateOnlyReceipt
    candidateProof
    promotedProof
    truthProof
    supportProof
    admissibilityProof
    tradingProof
    runtimeProof
    theoremProof

canonicalCandidateOnlyReceipt :
  (row : CandidateOnlyRow) →
  candidateOnly row ≡ true →
  promoted row ≡ false →
  carriesTruthAuthority row ≡ false →
  carriesSupportAuthority row ≡ false →
  carriesAdmissibilityAuthority row ≡ false →
  carriesTradingAuthority row ≡ false →
  carriesRuntimeAuthority row ≡ false →
  carriesTheoremAuthority row ≡ false →
  CandidateOnlyReceipt row
canonicalCandidateOnlyReceipt =
  mkCandidateOnlyReceipt

------------------------------------------------------------------------
-- Projection lemmas.

candidateOnlyIsTrue :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  candidateOnly row ≡ true
candidateOnlyIsTrue receipt =
  receiptCandidateOnlyIsTrue receipt

candidatePromotedIsFalse :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  promoted row ≡ false
candidatePromotedIsFalse receipt =
  receiptPromotedIsFalse receipt

candidateNoTruthAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesTruthAuthority row ≡ false
candidateNoTruthAuthority receipt =
  receiptNoTruthAuthority receipt

candidateNoSupportAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesSupportAuthority row ≡ false
candidateNoSupportAuthority receipt =
  receiptNoSupportAuthority receipt

candidateNoAdmissibilityAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesAdmissibilityAuthority row ≡ false
candidateNoAdmissibilityAuthority receipt =
  receiptNoAdmissibilityAuthority receipt

candidateNoTradingAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesTradingAuthority row ≡ false
candidateNoTradingAuthority receipt =
  receiptNoTradingAuthority receipt

candidateNoRuntimeAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesRuntimeAuthority row ≡ false
candidateNoRuntimeAuthority receipt =
  receiptNoRuntimeAuthority receipt

candidateNoTheoremAuthority :
  {row : CandidateOnlyRow} →
  CandidateOnlyReceipt row →
  carriesTheoremAuthority row ≡ false
candidateNoTheoremAuthority receipt =
  receiptNoTheoremAuthority receipt

------------------------------------------------------------------------
-- List-level candidate-only and non-promotion proofs.

data AllRowsCandidateOnly : List CandidateOnlyRow → Set where
  allRowsCandidateOnlyNil :
    AllRowsCandidateOnly []

  allRowsCandidateOnlyCons :
    ∀ {row rows} →
    candidateOnly row ≡ true →
    AllRowsCandidateOnly rows →
    AllRowsCandidateOnly (row ∷ rows)

data AllRowsPromotedFalse : List CandidateOnlyRow → Set where
  allRowsPromotedFalseNil :
    AllRowsPromotedFalse []

  allRowsPromotedFalseCons :
    ∀ {row rows} →
    promoted row ≡ false →
    AllRowsPromotedFalse rows →
    AllRowsPromotedFalse (row ∷ rows)

data AllRowsAuthorityFalse : List CandidateOnlyRow → Set where
  allRowsAuthorityFalseNil :
    AllRowsAuthorityFalse []

  allRowsAuthorityFalseCons :
    ∀ {row rows} →
    carriesTruthAuthority row ≡ false →
    carriesSupportAuthority row ≡ false →
    carriesAdmissibilityAuthority row ≡ false →
    carriesTradingAuthority row ≡ false →
    carriesRuntimeAuthority row ≡ false →
    carriesTheoremAuthority row ≡ false →
    AllRowsAuthorityFalse rows →
    AllRowsAuthorityFalse (row ∷ rows)

proveAllRowsCandidateOnly :
  (rows : List CandidateOnlyRow) →
  ((row : CandidateOnlyRow) → candidateOnly row ≡ true) →
  AllRowsCandidateOnly rows
proveAllRowsCandidateOnly [] proof =
  allRowsCandidateOnlyNil
proveAllRowsCandidateOnly (row ∷ rows) proof =
  allRowsCandidateOnlyCons
    (proof row)
    (proveAllRowsCandidateOnly rows proof)

proveAllRowsPromotedFalse :
  (rows : List CandidateOnlyRow) →
  ((row : CandidateOnlyRow) → promoted row ≡ false) →
  AllRowsPromotedFalse rows
proveAllRowsPromotedFalse [] proof =
  allRowsPromotedFalseNil
proveAllRowsPromotedFalse (row ∷ rows) proof =
  allRowsPromotedFalseCons
    (proof row)
    (proveAllRowsPromotedFalse rows proof)

------------------------------------------------------------------------
-- Canonical rows and receipts.

canonicalRowCandidateOnlyRow : CandidateOnlyRow
canonicalRowCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only row"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalRowCandidateOnlyRow"
    rowCandidateKind
    rowCandidateOnlyStatus
    "generic rows are candidate-only surfaces"
    "downstream modules must still supply domain authority to promote a row"

canonicalProposalCandidateOnlyRow : CandidateOnlyRow
canonicalProposalCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only proposal"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalProposalCandidateOnlyRow"
    proposalCandidateKind
    proposalCandidateOnlyStatus
    "proposal rows describe candidate motion only"
    "proposal acceptance remains outside this core"

canonicalDiagnosticCandidateOnlyRow : CandidateOnlyRow
canonicalDiagnosticCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only diagnostic"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalDiagnosticCandidateOnlyRow"
    diagnosticCandidateKind
    diagnosticCandidateOnlyStatus
    "diagnostic rows report candidate observations only"
    "diagnostics do not authorize truth or admissibility"

canonicalBridgeCandidateOnlyRow : CandidateOnlyRow
canonicalBridgeCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only bridge"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalBridgeCandidateOnlyRow"
    bridgeCandidateKind
    bridgeCandidateOnlyStatus
    "bridge rows transport candidate metadata only"
    "bridge authority must be supplied by a separate receipt"

canonicalRoleCandidateOnlyRow : CandidateOnlyRow
canonicalRoleCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only role"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalRoleCandidateOnlyRow"
    roleCandidateKind
    roleCandidateOnlyStatus
    "role rows describe candidate role assignment only"
    "role commitment remains outside this candidate-only core"

canonicalVectorCandidateOnlyRow : CandidateOnlyRow
canonicalVectorCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only vector"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalVectorCandidateOnlyRow"
    vectorCandidateKind
    vectorCandidateOnlyStatus
    "vector rows describe candidate hits or coordinates only"
    "vector score or proximity does not become authority here"

canonicalRankingCandidateOnlyRow : CandidateOnlyRow
canonicalRankingCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only ranking"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalRankingCandidateOnlyRow"
    rankingCandidateKind
    rankingCandidateOnlyStatus
    "ranking rows order candidates only"
    "rank position does not authorize support or trading action"

canonicalFunctionalCandidateOnlyRow : CandidateOnlyRow
canonicalFunctionalCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only functional"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalFunctionalCandidateOnlyRow"
    functionalCandidateKind
    functionalCandidateOnlyStatus
    "functional rows describe candidate transformations only"
    "functional transport does not promote theorem or runtime authority"

canonicalOperatorCandidateOnlyRow : CandidateOnlyRow
canonicalOperatorCandidateOnlyRow =
  mkCandidateOnlyRow
    "candidate-only operator"
    "DASHI.Core.CandidateOnlyCore"
    "canonicalOperatorCandidateOnlyRow"
    operatorCandidateKind
    operatorCandidateOnlyStatus
    "operator rows describe candidate operators only"
    "operator notation does not authorize theorem or runtime claims"

canonicalCandidateOnlyRows : List CandidateOnlyRow
canonicalCandidateOnlyRows =
  canonicalRowCandidateOnlyRow
  ∷ canonicalProposalCandidateOnlyRow
  ∷ canonicalDiagnosticCandidateOnlyRow
  ∷ canonicalBridgeCandidateOnlyRow
  ∷ canonicalRoleCandidateOnlyRow
  ∷ canonicalVectorCandidateOnlyRow
  ∷ canonicalRankingCandidateOnlyRow
  ∷ canonicalFunctionalCandidateOnlyRow
  ∷ canonicalOperatorCandidateOnlyRow
  ∷ []

canonicalCandidateOnlyRowCount : Nat
canonicalCandidateOnlyRowCount =
  listCount canonicalCandidateOnlyRows

canonicalRowCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalRowCandidateOnlyRow
canonicalRowCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalProposalCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalProposalCandidateOnlyRow
canonicalProposalCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalDiagnosticCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalDiagnosticCandidateOnlyRow
canonicalDiagnosticCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalBridgeCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalBridgeCandidateOnlyRow
canonicalBridgeCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalRoleCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalRoleCandidateOnlyRow
canonicalRoleCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalVectorCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalVectorCandidateOnlyRow
canonicalVectorCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalRankingCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalRankingCandidateOnlyRow
canonicalRankingCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalFunctionalCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalFunctionalCandidateOnlyRow
canonicalFunctionalCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalOperatorCandidateOnlyReceipt :
  CandidateOnlyReceipt canonicalOperatorCandidateOnlyRow
canonicalOperatorCandidateOnlyReceipt =
  candidateOnlyReceipt refl refl refl refl refl refl refl refl

canonicalCandidateOnlyReceiptsCandidateTrue :
  AllRowsCandidateOnly canonicalCandidateOnlyRows
canonicalCandidateOnlyReceiptsCandidateTrue =
  allRowsCandidateOnlyCons
    refl
    (allRowsCandidateOnlyCons
      refl
      (allRowsCandidateOnlyCons
        refl
        (allRowsCandidateOnlyCons
          refl
          (allRowsCandidateOnlyCons
            refl
            (allRowsCandidateOnlyCons
              refl
              (allRowsCandidateOnlyCons
                refl
                (allRowsCandidateOnlyCons
                  refl
                  (allRowsCandidateOnlyCons
                    refl
                    allRowsCandidateOnlyNil))))))))

canonicalCandidateOnlyReceiptsPromotedFalse :
  AllRowsPromotedFalse canonicalCandidateOnlyRows
canonicalCandidateOnlyReceiptsPromotedFalse =
  allRowsPromotedFalseCons
    refl
    (allRowsPromotedFalseCons
      refl
      (allRowsPromotedFalseCons
        refl
        (allRowsPromotedFalseCons
          refl
          (allRowsPromotedFalseCons
            refl
            (allRowsPromotedFalseCons
              refl
              (allRowsPromotedFalseCons
                refl
                (allRowsPromotedFalseCons
                  refl
                  (allRowsPromotedFalseCons
                    refl
                    allRowsPromotedFalseNil))))))))

canonicalCandidateOnlyReceiptsAuthorityFalse :
  AllRowsAuthorityFalse canonicalCandidateOnlyRows
canonicalCandidateOnlyReceiptsAuthorityFalse =
  allRowsAuthorityFalseCons
    refl
    refl
    refl
    refl
    refl
    refl
    (allRowsAuthorityFalseCons
      refl
      refl
      refl
      refl
      refl
      refl
      (allRowsAuthorityFalseCons
        refl
        refl
        refl
        refl
        refl
        refl
        (allRowsAuthorityFalseCons
          refl
          refl
          refl
          refl
          refl
          refl
          (allRowsAuthorityFalseCons
            refl
            refl
            refl
            refl
            refl
            refl
            (allRowsAuthorityFalseCons
              refl
              refl
              refl
              refl
              refl
              refl
              (allRowsAuthorityFalseCons
                refl
                refl
                refl
                refl
                refl
                refl
                (allRowsAuthorityFalseCons
                  refl
                  refl
                  refl
                  refl
                  refl
                  refl
                  (allRowsAuthorityFalseCons
                    refl
                    refl
                    refl
                    refl
                    refl
                    refl
                    allRowsAuthorityFalseNil))))))))

canonicalRowCandidateOnlyIsTrue :
  candidateOnly canonicalRowCandidateOnlyRow ≡ true
canonicalRowCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalRowCandidateOnlyReceipt

canonicalRowPromotedIsFalse :
  promoted canonicalRowCandidateOnlyRow ≡ false
canonicalRowPromotedIsFalse =
  candidatePromotedIsFalse canonicalRowCandidateOnlyReceipt

canonicalProposalCandidateOnlyIsTrue :
  candidateOnly canonicalProposalCandidateOnlyRow ≡ true
canonicalProposalCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalProposalCandidateOnlyReceipt

canonicalProposalPromotedIsFalse :
  promoted canonicalProposalCandidateOnlyRow ≡ false
canonicalProposalPromotedIsFalse =
  candidatePromotedIsFalse canonicalProposalCandidateOnlyReceipt

canonicalDiagnosticCandidateOnlyIsTrue :
  candidateOnly canonicalDiagnosticCandidateOnlyRow ≡ true
canonicalDiagnosticCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalDiagnosticCandidateOnlyReceipt

canonicalDiagnosticPromotedIsFalse :
  promoted canonicalDiagnosticCandidateOnlyRow ≡ false
canonicalDiagnosticPromotedIsFalse =
  candidatePromotedIsFalse canonicalDiagnosticCandidateOnlyReceipt

canonicalBridgeCandidateOnlyIsTrue :
  candidateOnly canonicalBridgeCandidateOnlyRow ≡ true
canonicalBridgeCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalBridgeCandidateOnlyReceipt

canonicalBridgePromotedIsFalse :
  promoted canonicalBridgeCandidateOnlyRow ≡ false
canonicalBridgePromotedIsFalse =
  candidatePromotedIsFalse canonicalBridgeCandidateOnlyReceipt

canonicalRoleCandidateOnlyIsTrue :
  candidateOnly canonicalRoleCandidateOnlyRow ≡ true
canonicalRoleCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalRoleCandidateOnlyReceipt

canonicalRolePromotedIsFalse :
  promoted canonicalRoleCandidateOnlyRow ≡ false
canonicalRolePromotedIsFalse =
  candidatePromotedIsFalse canonicalRoleCandidateOnlyReceipt

canonicalVectorCandidateOnlyIsTrue :
  candidateOnly canonicalVectorCandidateOnlyRow ≡ true
canonicalVectorCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalVectorCandidateOnlyReceipt

canonicalVectorPromotedIsFalse :
  promoted canonicalVectorCandidateOnlyRow ≡ false
canonicalVectorPromotedIsFalse =
  candidatePromotedIsFalse canonicalVectorCandidateOnlyReceipt

canonicalRankingCandidateOnlyIsTrue :
  candidateOnly canonicalRankingCandidateOnlyRow ≡ true
canonicalRankingCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalRankingCandidateOnlyReceipt

canonicalRankingPromotedIsFalse :
  promoted canonicalRankingCandidateOnlyRow ≡ false
canonicalRankingPromotedIsFalse =
  candidatePromotedIsFalse canonicalRankingCandidateOnlyReceipt

canonicalFunctionalCandidateOnlyIsTrue :
  candidateOnly canonicalFunctionalCandidateOnlyRow ≡ true
canonicalFunctionalCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalFunctionalCandidateOnlyReceipt

canonicalFunctionalPromotedIsFalse :
  promoted canonicalFunctionalCandidateOnlyRow ≡ false
canonicalFunctionalPromotedIsFalse =
  candidatePromotedIsFalse canonicalFunctionalCandidateOnlyReceipt

canonicalOperatorCandidateOnlyIsTrue :
  candidateOnly canonicalOperatorCandidateOnlyRow ≡ true
canonicalOperatorCandidateOnlyIsTrue =
  candidateOnlyIsTrue canonicalOperatorCandidateOnlyReceipt

canonicalOperatorPromotedIsFalse :
  promoted canonicalOperatorCandidateOnlyRow ≡ false
canonicalOperatorPromotedIsFalse =
  candidatePromotedIsFalse canonicalOperatorCandidateOnlyReceipt

------------------------------------------------------------------------
-- Generic receipt adapter.

candidateOnlyGenericReceipt :
  CandidateOnlyRow →
  GenericReceipt.GenericReceipt
candidateOnlyGenericReceipt row =
  GenericReceipt.mkNonPromotingReceipt
    (candidateRowLabel row)
    (candidateRowOwner row)
    (candidateRowSurface row)
    (candidateRowStatement row)
    (candidateRowRemainingGap row)
    "agda -i . DASHI/Core/CandidateOnlyCore.agda"

canonicalCandidateOnlyGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalCandidateOnlyGenericReceipts =
  candidateOnlyGenericReceipt canonicalRowCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalProposalCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalDiagnosticCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalBridgeCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalRoleCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalVectorCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalRankingCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalFunctionalCandidateOnlyRow
  ∷ candidateOnlyGenericReceipt canonicalOperatorCandidateOnlyRow
  ∷ []

canonicalCandidateOnlyGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalCandidateOnlyGenericReceipts
canonicalCandidateOnlyGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalCandidateOnlyGenericReceipts
