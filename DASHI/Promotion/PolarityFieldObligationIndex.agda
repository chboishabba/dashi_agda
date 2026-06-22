module DASHI.Promotion.PolarityFieldObligationIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Culture.YinYangPolarityBoundary as YinYang
import DASHI.Core.FiniteReceiptList as FiniteReceiptList
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Interop.BettiQiAdapter as BettiQi
import DASHI.Interop.PolarityBettiSupportBoundary as Betti
import DASHI.Interop.PolarityPhaseFieldBridge as PhaseField
import DASHI.Interop.TaoYinYangAdapter as TaoYinYang
import DASHI.Interop.YinYangQiAdapter as YinYangQi

------------------------------------------------------------------------
-- Polarity / field obligation index for the yin/yang stack.
--
-- This module is candidate-only and authority-blocked.  It records the
-- canonical summary and governance rows that a future yin/yang and
-- polarity-phase-field stack must satisfy before any promotion claim can be
-- accepted.  No promotion is asserted here.

listCount : ∀ {a} {A : Set a} → List A → Nat
listCount = FiniteReceiptList.listCount

data StackLane : Set where
  yinLane : StackLane
  yangLane : StackLane
  polarityLane : StackLane
  phaseLane : StackLane
  bettiLane : StackLane
  fieldLane : StackLane
  governanceSurfaceLane : StackLane

data GovernanceGate : Set where
  candidateOnlyGate : GovernanceGate
  authorityBlockedGate : GovernanceGate
  canonicalReceiptGate : GovernanceGate
  countIntegrityGate : GovernanceGate
  nonPromotionGate : GovernanceGate

record SummaryRow : Set where
  constructor mkSummaryRow
  field
    summaryLabel : String
    summaryLane : StackLane
    summaryOwner : String
    summarySurface : String
    summaryCanonicalReceipts : List String
    summaryCandidateOnly : Bool
    summaryCandidateOnlyIsTrue :
      summaryCandidateOnly ≡ true
    summaryAuthorityBlocked : Bool
    summaryAuthorityBlockedIsTrue :
      summaryAuthorityBlocked ≡ true
    summaryPromoted : Bool
    summaryPromotedIsFalse :
      summaryPromoted ≡ false

open SummaryRow public

record GovernanceRow : Set where
  constructor mkGovernanceRow
  field
    governanceLabel : String
    governanceLane : StackLane
    governanceOwner : String
    governanceGate : GovernanceGate
    governanceReceiptNames : List String
    governanceBlockedAuthorities : List String
    governanceCandidateOnly : Bool
    governanceCandidateOnlyIsTrue :
      governanceCandidateOnly ≡ true
    governanceAuthorityBlocked : Bool
    governanceAuthorityBlockedIsTrue :
      governanceAuthorityBlocked ≡ true
    governancePromoted : Bool
    governancePromotedIsFalse :
      governancePromoted ≡ false

open GovernanceRow public

countSummaryRows : List SummaryRow → Nat
countSummaryRows = listCount

countGovernanceRows : List GovernanceRow → Nat
countGovernanceRows = listCount

canonicalStackLanes : List StackLane
canonicalStackLanes =
  yinLane
  ∷ yangLane
  ∷ polarityLane
  ∷ phaseLane
  ∷ bettiLane
  ∷ fieldLane
  ∷ governanceSurfaceLane
  ∷ []

canonicalStackLaneCount : Nat
canonicalStackLaneCount =
  listCount canonicalStackLanes

canonicalStackLaneCountIs7 :
  canonicalStackLaneCount ≡ 7
canonicalStackLaneCountIs7 = refl

canonicalBlockedAuthorities : List String
canonicalBlockedAuthorities =
  "truth authority"
  ∷ "support authority"
  ∷ "admissibility authority"
  ∷ "theorem authority"
  ∷ "runtime authority"
  ∷ "external authority"
  ∷ []

canonicalBlockedAuthorityCount : Nat
canonicalBlockedAuthorityCount =
  listCount canonicalBlockedAuthorities

canonicalReceiptReferenceNames : List String
canonicalReceiptReferenceNames =
  "DASHI.Culture.YinYangPolarityBoundary.canonicalYinYangPolarityBoundaryReceipt"
  ∷ "DASHI.Interop.TaoYinYangAdapter.canonicalTaoYinYangBridgeReceipt"
  ∷ "DASHI.Interop.YinYangQiAdapter.canonicalYinYangQiBridgeReceipt"
  ∷ "DASHI.Interop.PolarityPhaseFieldBridge.canonicalPolarityPhaseFieldBridge"
  ∷ "DASHI.Interop.PolarityBettiSupportBoundary.canonicalPolarityBettiSupportBoundaryReceipt"
  ∷ "DASHI.Interop.BettiQiAdapter.canonicalBettiQiBridgeReceipt"
  ∷ "DASHI.Promotion.PolarityFieldObligationIndex.canonicalPolarityFieldObligationIndexReceipt"
  ∷ []

canonicalReceiptReferenceNameCount : Nat
canonicalReceiptReferenceNameCount =
  listCount canonicalReceiptReferenceNames

canonicalSummaryRows : List SummaryRow
canonicalSummaryRows =
  mkSummaryRow
    "yin-yang boundary summary"
    yinLane
    "DASHI.Culture.YinYangPolarityBoundary"
    "candidate-only polarity boundary between Tao operator grammar and Qi formal-lens/operator grammar"
    ( "DASHI.Culture.YinYangPolarityBoundary.canonicalYinYangPolarityBoundaryReceipt"
      ∷ "DASHI.Interop.TaoYinYangAdapter.canonicalTaoYinYangBridgeReceipt"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "tao to yinyang summary"
    yangLane
    "DASHI.Interop.TaoYinYangAdapter"
    "tao motif extraction into candidate-only yin/yang polarity rows"
    ( "DASHI.Interop.TaoYinYangAdapter.canonicalTaoYinYangBridgeReceipt"
      ∷ "DASHI.Culture.YinYangPolarityBoundary.canonicalYinYangPolarityBoundaryReceipt"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "yinyang to qi summary"
    polarityLane
    "DASHI.Interop.YinYangQiAdapter"
    "yin/yang polarity rows carried into Qi carrier, role, and formal-lens surfaces"
    ( "DASHI.Interop.YinYangQiAdapter.canonicalYinYangQiBridgeReceipt"
      ∷ "DASHI.Culture.YinYangPolarityBoundary.canonicalYinYangPolarityBoundaryReceipt"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "phase field summary"
    phaseLane
    "DASHI.Interop.PolarityPhaseFieldBridge"
    "369 phase, voxel, supervoxel, wave, and superposition candidate bridge"
    ( "DASHI.Interop.PolarityPhaseFieldBridge.canonicalPolarityPhaseFieldBridge"
      ∷ "DASHI.Interop.YinYangQiAdapter.canonicalYinYangQiBridgeReceipt"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "betti support summary"
    bettiLane
    "DASHI.Interop.PolarityBettiSupportBoundary"
    "candidate-only Betti summaries over voxel, supervoxel, and boundary support geometry"
    ( "DASHI.Interop.PolarityBettiSupportBoundary.canonicalPolarityBettiSupportBoundaryReceipt"
      ∷ "DASHI.Interop.PolarityPhaseFieldBridge.canonicalPolarityPhaseFieldBridge"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "betti to qi summary"
    fieldLane
    "DASHI.Interop.BettiQiAdapter"
    "Betti topology summaries carried into Qi carrier, role, and formal-lens surfaces"
    ( "DASHI.Interop.BettiQiAdapter.canonicalBettiQiBridgeReceipt"
      ∷ "DASHI.Interop.PolarityBettiSupportBoundary.canonicalPolarityBettiSupportBoundaryReceipt"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkSummaryRow
    "governance summary"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    "obligation index for the polarity-to-field stack"
    ( "DASHI.Promotion.PolarityFieldObligationIndex.canonicalPolarityFieldObligationIndexReceipt"
      ∷ "DASHI.Interop.BettiQiAdapter.canonicalBettiQiBridgeReceipt"
      ∷ "DASHI.Interop.PolarityBettiSupportBoundary.canonicalPolarityBettiSupportBoundaryReceipt"
      ∷ "DASHI.Interop.PolarityPhaseFieldBridge.canonicalPolarityPhaseFieldBridge"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ []

canonicalSummaryRowCount : Nat
canonicalSummaryRowCount =
  countSummaryRows canonicalSummaryRows

canonicalGovernanceRows : List GovernanceRow
canonicalGovernanceRows =
  mkGovernanceRow
    "candidate-only governance"
    phaseLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    candidateOnlyGate
    ( "DASHI.Core.CandidateOnlyCore"
      ∷ "DASHI.Core.GenericReceipt"
      ∷ []
    )
    ( "candidate-only surface remains in force"
      ∷ "promotion remains absent"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkGovernanceRow
    "authority-blocked governance"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    authorityBlockedGate
    ( "DASHI.Core.AuthorityNonPromotionCore"
      ∷ "DASHI.Core.GenericReceipt"
      ∷ []
    )
    canonicalBlockedAuthorities
    true
    refl
    true
    refl
    false
    refl
  ∷ mkGovernanceRow
    "canonical receipt governance"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    canonicalReceiptGate
    canonicalReceiptReferenceNames
    ( "canonical receipt names are tracked explicitly"
      ∷ "future sibling modules may supply the referenced receipts"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkGovernanceRow
    "betti topology governance"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    authorityBlockedGate
    ( "DASHI.Interop.PolarityBettiSupportBoundary.canonicalPolarityBettiSupportBoundaryReceipt"
      ∷ "DASHI.Interop.BettiQiAdapter.canonicalBettiQiBridgeReceipt"
      ∷ []
    )
    ( "Betti support summaries remain candidate-only topology diagnostics"
      ∷ "Betti-to-Qi transport remains non-promoting and authority-blocked"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkGovernanceRow
    "count integrity governance"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    countIntegrityGate
    ( "summary row count"
      ∷ "governance row count"
      ∷ "canonical receipt name count"
      ∷ []
    )
    ( "the row counts are exact"
      ∷ "the receipt reference count is exact"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ mkGovernanceRow
    "non-promotion governance"
    governanceSurfaceLane
    "DASHI.Promotion.PolarityFieldObligationIndex"
    nonPromotionGate
    ( "DASHI.Core.GenericReceipt"
      ∷ "DASHI.Core.FiniteReceiptList"
      ∷ []
    )
    ( "non-promotion proofs are carried as equalities"
      ∷ "candidate-only and authority-blocked bits are kept closed"
      ∷ []
    )
    true
    refl
    true
    refl
    false
    refl
  ∷ []

canonicalGovernanceRowCount : Nat
canonicalGovernanceRowCount =
  countGovernanceRows canonicalGovernanceRows

canonicalTotalRowCount : Nat
canonicalTotalRowCount =
  canonicalSummaryRowCount + canonicalGovernanceRowCount

------------------------------------------------------------------------
-- List-level non-promotion proofs.

data AllSummaryRowsCandidateOnly : List SummaryRow → Set where
  allSummaryRowsCandidateOnlyNil :
    AllSummaryRowsCandidateOnly []

  allSummaryRowsCandidateOnlyCons :
    ∀ {row rows} →
    summaryCandidateOnly row ≡ true →
    AllSummaryRowsCandidateOnly rows →
    AllSummaryRowsCandidateOnly (row ∷ rows)

proveAllSummaryRowsCandidateOnly :
  (rows : List SummaryRow) →
  AllSummaryRowsCandidateOnly rows
proveAllSummaryRowsCandidateOnly [] =
  allSummaryRowsCandidateOnlyNil
proveAllSummaryRowsCandidateOnly (row ∷ rows) =
  allSummaryRowsCandidateOnlyCons
    (summaryCandidateOnlyIsTrue row)
    (proveAllSummaryRowsCandidateOnly rows)

data AllSummaryRowsAuthorityBlocked : List SummaryRow → Set where
  allSummaryRowsAuthorityBlockedNil :
    AllSummaryRowsAuthorityBlocked []

  allSummaryRowsAuthorityBlockedCons :
    ∀ {row rows} →
    summaryAuthorityBlocked row ≡ true →
    AllSummaryRowsAuthorityBlocked rows →
    AllSummaryRowsAuthorityBlocked (row ∷ rows)

proveAllSummaryRowsAuthorityBlocked :
  (rows : List SummaryRow) →
  AllSummaryRowsAuthorityBlocked rows
proveAllSummaryRowsAuthorityBlocked [] =
  allSummaryRowsAuthorityBlockedNil
proveAllSummaryRowsAuthorityBlocked (row ∷ rows) =
  allSummaryRowsAuthorityBlockedCons
    (summaryAuthorityBlockedIsTrue row)
    (proveAllSummaryRowsAuthorityBlocked rows)

data AllSummaryRowsNonPromoting : List SummaryRow → Set where
  allSummaryRowsNonPromotingNil :
    AllSummaryRowsNonPromoting []

  allSummaryRowsNonPromotingCons :
    ∀ {row rows} →
    summaryPromoted row ≡ false →
    AllSummaryRowsNonPromoting rows →
    AllSummaryRowsNonPromoting (row ∷ rows)

proveAllSummaryRowsNonPromoting :
  (rows : List SummaryRow) →
  AllSummaryRowsNonPromoting rows
proveAllSummaryRowsNonPromoting [] =
  allSummaryRowsNonPromotingNil
proveAllSummaryRowsNonPromoting (row ∷ rows) =
  allSummaryRowsNonPromotingCons
    (summaryPromotedIsFalse row)
    (proveAllSummaryRowsNonPromoting rows)

data AllGovernanceRowsCandidateOnly : List GovernanceRow → Set where
  allGovernanceRowsCandidateOnlyNil :
    AllGovernanceRowsCandidateOnly []

  allGovernanceRowsCandidateOnlyCons :
    ∀ {row rows} →
    governanceCandidateOnly row ≡ true →
    AllGovernanceRowsCandidateOnly rows →
    AllGovernanceRowsCandidateOnly (row ∷ rows)

proveAllGovernanceRowsCandidateOnly :
  (rows : List GovernanceRow) →
  AllGovernanceRowsCandidateOnly rows
proveAllGovernanceRowsCandidateOnly [] =
  allGovernanceRowsCandidateOnlyNil
proveAllGovernanceRowsCandidateOnly (row ∷ rows) =
  allGovernanceRowsCandidateOnlyCons
    (governanceCandidateOnlyIsTrue row)
    (proveAllGovernanceRowsCandidateOnly rows)

data AllGovernanceRowsAuthorityBlocked : List GovernanceRow → Set where
  allGovernanceRowsAuthorityBlockedNil :
    AllGovernanceRowsAuthorityBlocked []

  allGovernanceRowsAuthorityBlockedCons :
    ∀ {row rows} →
    governanceAuthorityBlocked row ≡ true →
    AllGovernanceRowsAuthorityBlocked rows →
    AllGovernanceRowsAuthorityBlocked (row ∷ rows)

proveAllGovernanceRowsAuthorityBlocked :
  (rows : List GovernanceRow) →
  AllGovernanceRowsAuthorityBlocked rows
proveAllGovernanceRowsAuthorityBlocked [] =
  allGovernanceRowsAuthorityBlockedNil
proveAllGovernanceRowsAuthorityBlocked (row ∷ rows) =
  allGovernanceRowsAuthorityBlockedCons
    (governanceAuthorityBlockedIsTrue row)
    (proveAllGovernanceRowsAuthorityBlocked rows)

data AllGovernanceRowsNonPromoting : List GovernanceRow → Set where
  allGovernanceRowsNonPromotingNil :
    AllGovernanceRowsNonPromoting []

  allGovernanceRowsNonPromotingCons :
    ∀ {row rows} →
    governancePromoted row ≡ false →
    AllGovernanceRowsNonPromoting rows →
    AllGovernanceRowsNonPromoting (row ∷ rows)

proveAllGovernanceRowsNonPromoting :
  (rows : List GovernanceRow) →
  AllGovernanceRowsNonPromoting rows
proveAllGovernanceRowsNonPromoting [] =
  allGovernanceRowsNonPromotingNil
proveAllGovernanceRowsNonPromoting (row ∷ rows) =
  allGovernanceRowsNonPromotingCons
    (governancePromotedIsFalse row)
    (proveAllGovernanceRowsNonPromoting rows)

------------------------------------------------------------------------
-- Canonical receipt surface.

record PolarityFieldObligationIndexReceipt : Set where
  constructor mkPolarityFieldObligationIndexReceipt
  field
    receiptLabel : String
    receiptSurface : String
    summaryRows : List SummaryRow
    summaryRowCount : Nat
    summaryRowCountMatches :
      summaryRowCount ≡ countSummaryRows summaryRows
    summaryRowsCandidateOnly :
      AllSummaryRowsCandidateOnly summaryRows
    summaryRowsAuthorityBlocked :
      AllSummaryRowsAuthorityBlocked summaryRows
    summaryRowsNonPromoting :
      AllSummaryRowsNonPromoting summaryRows
    governanceRows : List GovernanceRow
    governanceRowCount : Nat
    governanceRowCountMatches :
      governanceRowCount ≡ countGovernanceRows governanceRows
    governanceRowsCandidateOnly :
      AllGovernanceRowsCandidateOnly governanceRows
    governanceRowsAuthorityBlocked :
      AllGovernanceRowsAuthorityBlocked governanceRows
    governanceRowsNonPromoting :
      AllGovernanceRowsNonPromoting governanceRows
    canonicalReceiptNames : List String
    canonicalReceiptNameCount : Nat
    canonicalReceiptNameCountMatches :
      canonicalReceiptNameCount ≡ listCount canonicalReceiptNames
    totalRowCount : Nat
    totalRowCountMatches :
      totalRowCount ≡ summaryRowCount + governanceRowCount
    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    authorityBlocked : Bool
    authorityBlockedIsTrue :
      authorityBlocked ≡ true
    promoted : Bool
    promotedIsFalse :
      promoted ≡ false
    receipt : GenericReceipt.GenericReceipt
    receiptIsNonPromoting :
      GenericReceipt.promotesClaim receipt ≡ false
    receiptBoundary : List String

open PolarityFieldObligationIndexReceipt public

canonicalPolarityFieldObligationIndexReceipt :
  PolarityFieldObligationIndexReceipt
canonicalPolarityFieldObligationIndexReceipt =
  record
    { receiptLabel =
        "canonical polarity-field obligation index"
    ; receiptSurface =
        "DASHI.Promotion.PolarityFieldObligationIndex"
    ; summaryRows =
        canonicalSummaryRows
    ; summaryRowCount =
        canonicalSummaryRowCount
    ; summaryRowCountMatches =
        refl
    ; summaryRowsCandidateOnly =
        proveAllSummaryRowsCandidateOnly canonicalSummaryRows
    ; summaryRowsAuthorityBlocked =
        proveAllSummaryRowsAuthorityBlocked canonicalSummaryRows
    ; summaryRowsNonPromoting =
        proveAllSummaryRowsNonPromoting canonicalSummaryRows
    ; governanceRows =
        canonicalGovernanceRows
    ; governanceRowCount =
        canonicalGovernanceRowCount
    ; governanceRowCountMatches =
        refl
    ; governanceRowsCandidateOnly =
        proveAllGovernanceRowsCandidateOnly canonicalGovernanceRows
    ; governanceRowsAuthorityBlocked =
        proveAllGovernanceRowsAuthorityBlocked canonicalGovernanceRows
    ; governanceRowsNonPromoting =
        proveAllGovernanceRowsNonPromoting canonicalGovernanceRows
    ; canonicalReceiptNames =
        canonicalReceiptReferenceNames
    ; canonicalReceiptNameCount =
        canonicalReceiptReferenceNameCount
    ; canonicalReceiptNameCountMatches =
        refl
    ; totalRowCount =
        canonicalTotalRowCount
    ; totalRowCountMatches =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; authorityBlocked =
        true
    ; authorityBlockedIsTrue =
        refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; receipt =
        GenericReceipt.mkNonPromotingReceipt
          "polarity-field obligation index"
          "DASHI.Promotion.PolarityFieldObligationIndex"
          "canonicalPolarityFieldObligationIndexReceipt"
          "candidate-only summary rows, governance rows, counts, and blocked authority surfaces are recorded"
          "yin/yang and polarity-phase-field promotion remains blocked until sibling receipts exist and are accepted"
          "agda -i . DASHI/Promotion/PolarityFieldObligationIndex.agda"
    ; receiptIsNonPromoting =
        refl
    ; receiptBoundary =
        "candidate-only surface"
        ∷ "authority-blocked surface"
        ∷ "canonical receipt surface"
        ∷ "exact row counts"
        ∷ "non-promotion proofs"
        ∷ []
    }

canonicalSummaryRowCountIs7 :
  canonicalSummaryRowCount ≡ 7
canonicalSummaryRowCountIs7 = refl

canonicalGovernanceRowCountIs6 :
  canonicalGovernanceRowCount ≡ 6
canonicalGovernanceRowCountIs6 = refl

canonicalTotalRowCountIs13 :
  canonicalTotalRowCount ≡ 13
canonicalTotalRowCountIs13 = refl

canonicalReceiptReferenceNameCountIs7 :
  canonicalReceiptReferenceNameCount ≡ 7
canonicalReceiptReferenceNameCountIs7 = refl

canonicalSummaryRowsCandidateOnly :
  AllSummaryRowsCandidateOnly canonicalSummaryRows
canonicalSummaryRowsCandidateOnly =
  proveAllSummaryRowsCandidateOnly canonicalSummaryRows

canonicalSummaryRowsAuthorityBlocked :
  AllSummaryRowsAuthorityBlocked canonicalSummaryRows
canonicalSummaryRowsAuthorityBlocked =
  proveAllSummaryRowsAuthorityBlocked canonicalSummaryRows

canonicalSummaryRowsNonPromoting :
  AllSummaryRowsNonPromoting canonicalSummaryRows
canonicalSummaryRowsNonPromoting =
  proveAllSummaryRowsNonPromoting canonicalSummaryRows

canonicalGovernanceRowsCandidateOnly :
  AllGovernanceRowsCandidateOnly canonicalGovernanceRows
canonicalGovernanceRowsCandidateOnly =
  proveAllGovernanceRowsCandidateOnly canonicalGovernanceRows

canonicalGovernanceRowsAuthorityBlocked :
  AllGovernanceRowsAuthorityBlocked canonicalGovernanceRows
canonicalGovernanceRowsAuthorityBlocked =
  proveAllGovernanceRowsAuthorityBlocked canonicalGovernanceRows

canonicalGovernanceRowsNonPromoting :
  AllGovernanceRowsNonPromoting canonicalGovernanceRows
canonicalGovernanceRowsNonPromoting =
  proveAllGovernanceRowsNonPromoting canonicalGovernanceRows

canonicalReceiptIsNonPromoting :
  GenericReceipt.promotesClaim
    (receipt canonicalPolarityFieldObligationIndexReceipt)
  ≡ false
canonicalReceiptIsNonPromoting =
  receiptIsNonPromoting canonicalPolarityFieldObligationIndexReceipt
