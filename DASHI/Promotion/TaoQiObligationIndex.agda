module DASHI.Promotion.TaoQiObligationIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Culture.QiOperatorTheoryBoundary as QiTheory
import DASHI.Culture.TaoOperatorGrammar as TaoGrammar
import DASHI.Culture.TaoChapterReadingReceipt as Tao
import DASHI.Culture.YinYangPolarityBoundary as YinYang
import DASHI.Interop.BettiQiAdapter as BettiQi
import DASHI.Interop.PolarityBettiSupportBoundary as Betti
import DASHI.Interop.PolarityPhaseFieldBridge as PhaseField
import DASHI.Interop.QiCarrierFieldBridge as QiBridge
import DASHI.Interop.TaoMeditationQiAdapter as TaoMeditation
import DASHI.Interop.TaoQiReadingAdapter as TaoQi
import DASHI.Interop.TaoYinYangAdapter as TaoYinYang
import DASHI.Interop.YinYangQiAdapter as YinYangQi
import DASHI.Promotion.PolarityFieldObligationIndex as PolarityField

------------------------------------------------------------------------
-- Tao / Qi obligation index.
--
-- This module keeps the Tao and Qi surfaces candidate-only.  The Tao source
-- receipt is treated as translation-dependent reading material, the Qi
-- operator-theory receipt is treated as role grammar only, and the Qi
-- carrier-field bridge remains descriptive.  No doctrine, empirical, clinical,
-- mystical, metaphysical, or authority claim is promoted here.

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data TaoQiLane : Set where
  taoSourceLane : TaoQiLane
  taoReadingLane : TaoQiLane
  yinYangBoundaryLane : TaoQiLane
  bettiSupportLane : TaoQiLane
  qiRoleGrammarLane : TaoQiLane
  qiCarrierFieldLane : TaoQiLane
  taoQiBridgeLane : TaoQiLane
  governanceLane : TaoQiLane

record TaoQiSummaryRow : Set where
  constructor taoQiSummaryRow
  field
    lane : TaoQiLane
    ownerModule : String
    canonicalSurface : String
    candidateOnlyPayload : String
    openObligationCount : Nat
    nonPromotionNote : String
    blockedAuthorityNote : String
    validationCommand : String
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false

open TaoQiSummaryRow public

record TaoQiGovernanceRow : Set where
  constructor taoQiGovernanceRow
  field
    lane : TaoQiLane
    governanceModule : String
    taoSourceReceipt : Tao.TaoSourceReceipt
    taoBoundaryFailClosed : Tao.TaoBoundaryFailClosed
    taoChapterReceipt : Tao.TaoChapterReceipt
    taoOperatorGrammarReceipt :
      TaoGrammar.TaoOperatorGrammarReceipt
    yinYangBoundaryReceipt :
      YinYang.YinYangPolarityBoundaryReceipt
    taoYinYangBridgeReceipt :
      TaoYinYang.TaoYinYangBridgeReceipt
    yinYangQiBridgeReceipt :
      YinYangQi.YinYangQiBridgeReceipt
    polarityPhaseFieldBridgeReceipt :
      PhaseField.PolarityPhaseFieldBridge
    bettiSupportBoundaryModule : String
    bettiSupportBoundarySurface : String
    bettiQiAdapterModule : String
    bettiQiAdapterSurface : String
    qiOperatorReceipt : QiTheory.QiOperatorTheoryBoundaryReceipt
    qiCarrierBridgeReceipt : QiBridge.QiCarrierFieldBridgeReceipt
    taoQiBridgeReceipt :
      TaoQi.TaoQiBridgeReceipt
    taoMeditationBridgeReceipt :
      TaoMeditation.TaoMeditationQiBridgeReceipt
    polarityFieldObligationReceipt :
      PolarityField.PolarityFieldObligationIndexReceipt
    candidateOnlyPayload : Bool
    candidateOnlyPayloadIsTrue : candidateOnlyPayload ≡ true
    authorityBlocked : Bool
    authorityBlockedIsTrue : authorityBlocked ≡ true
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false
    governanceNote : String
    validationCommand : String

open TaoQiGovernanceRow public

record TaoQiObligationIndexReceipt : Set where
  constructor taoQiObligationIndexReceipt
  field
    taoSourceReceipt : Tao.TaoSourceReceipt
    taoBoundaryFailClosed : Tao.TaoBoundaryFailClosed
    taoChapterReceipt : Tao.TaoChapterReceipt
    taoOperatorGrammarReceipt :
      TaoGrammar.TaoOperatorGrammarReceipt
    yinYangBoundaryReceipt :
      YinYang.YinYangPolarityBoundaryReceipt
    taoYinYangBridgeReceipt :
      TaoYinYang.TaoYinYangBridgeReceipt
    yinYangQiBridgeReceipt :
      YinYangQi.YinYangQiBridgeReceipt
    polarityPhaseFieldBridgeReceipt :
      PhaseField.PolarityPhaseFieldBridge
    bettiSupportBoundaryModule : String
    bettiSupportBoundarySurface : String
    bettiQiAdapterModule : String
    bettiQiAdapterSurface : String
    qiOperatorReceipt : QiTheory.QiOperatorTheoryBoundaryReceipt
    qiCarrierBridgeReceipt : QiBridge.QiCarrierFieldBridgeReceipt
    taoQiBridgeReceipt :
      TaoQi.TaoQiBridgeReceipt
    taoMeditationBridgeReceipt :
      TaoMeditation.TaoMeditationQiBridgeReceipt
    polarityFieldObligationReceipt :
      PolarityField.PolarityFieldObligationIndexReceipt
    summaryRows : List TaoQiSummaryRow
    governanceRows : List TaoQiGovernanceRow
    indexCandidateOnlyPayload : Bool
    indexCandidateOnlyPayloadIsTrue : indexCandidateOnlyPayload ≡ true
    indexAuthorityBlocked : Bool
    indexAuthorityBlockedIsTrue : indexAuthorityBlocked ≡ true
    indexPromotesClaim : Bool
    indexPromotesClaimIsFalse : indexPromotesClaim ≡ false

open TaoQiObligationIndexReceipt public

mkTaoQiSummaryRow :
  TaoQiLane →
  String →
  String →
  String →
  Nat →
  String →
  String →
  String →
  TaoQiSummaryRow
mkTaoQiSummaryRow lane owner surface payload count nonPromotion blocked command =
  taoQiSummaryRow
    lane
    owner
    surface
    payload
    count
    nonPromotion
    blocked
    command
    false
    refl

mkTaoQiGovernanceRow :
  TaoQiLane →
  String →
  Tao.TaoSourceReceipt →
  Tao.TaoBoundaryFailClosed →
  Tao.TaoChapterReceipt →
  TaoGrammar.TaoOperatorGrammarReceipt →
  YinYang.YinYangPolarityBoundaryReceipt →
  TaoYinYang.TaoYinYangBridgeReceipt →
  YinYangQi.YinYangQiBridgeReceipt →
  PhaseField.PolarityPhaseFieldBridge →
  String →
  String →
  String →
  String →
  QiTheory.QiOperatorTheoryBoundaryReceipt →
  QiBridge.QiCarrierFieldBridgeReceipt →
  TaoQi.TaoQiBridgeReceipt →
  TaoMeditation.TaoMeditationQiBridgeReceipt →
  PolarityField.PolarityFieldObligationIndexReceipt →
  String →
  String →
  TaoQiGovernanceRow
mkTaoQiGovernanceRow lane moduleName taoSource taoFail taoChapter taoGrammar
  yinYang taoYinYang yinYangQi polarityPhaseField
  bettiBoundaryModule bettiBoundarySurface bettiAdapterModule
  bettiAdapterSurface qiOperator qiBridge taoQi taoMeditation polarityField
  note command =
  taoQiGovernanceRow
    lane
    moduleName
    taoSource
    taoFail
    taoChapter
    taoGrammar
    yinYang
    taoYinYang
    yinYangQi
    polarityPhaseField
    bettiBoundaryModule
    bettiBoundarySurface
    bettiAdapterModule
    bettiAdapterSurface
    qiOperator
    qiBridge
    taoQi
    taoMeditation
    polarityField
    true
    refl
    true
    refl
    false
    refl
    note
    command

canonicalBettiSupportBoundaryModuleName : String
canonicalBettiSupportBoundaryModuleName =
  "DASHI.Interop.PolarityBettiSupportBoundary"

canonicalBettiSupportBoundarySurfaceName : String
canonicalBettiSupportBoundarySurfaceName =
  "canonicalPolarityBettiSupportBoundary"

canonicalBettiQiAdapterModuleName : String
canonicalBettiQiAdapterModuleName =
  "DASHI.Interop.BettiQiAdapter"

canonicalBettiQiAdapterSurfaceName : String
canonicalBettiQiAdapterSurfaceName =
  "canonicalBettiQiBridgeReceipt"

canonicalTaoQiSummaryRows : List TaoQiSummaryRow
canonicalTaoQiSummaryRows =
  mkTaoQiSummaryRow
    taoSourceLane
    "DASHI.Culture.TaoChapterReadingReceipt"
    "canonicalTaoSourceReceipt"
    "TaoTeChing/Daodejing Book One chapters 1-37 are tracked as translation-dependent, metaphor-bound, candidate-only reading receipts."
    (listCount Tao.canonicalTaoChapterIds)
    "source coverage is descriptive only and does not promote doctrine"
    "empirical, spiritual, mystical, clinical, political, metaphysical, philological, and canonical-text authority stay blocked"
    "agda -i . DASHI/Culture/TaoChapterReadingReceipt.agda"
  ∷ mkTaoQiSummaryRow
    taoReadingLane
    "DASHI.Culture.TaoChapterReadingReceipt"
    "chapter1Receipt"
    "Chapter 1 keeps the Dao/named contrast as a candidate reading row with a translation-dependent qualifier and a negative-boundary reading kind."
    (listCount (Tao.rows Tao.chapter1Receipt))
    "chapter-local reading remains interpretive and non-promoting"
    "metaphysical and canonical authority stay blocked by the Tao boundary-fail-closed receipt"
    "agda -i . DASHI/Culture/TaoChapterReadingReceipt.agda"
  ∷ mkTaoQiSummaryRow
    taoReadingLane
    "DASHI.Culture.TaoOperatorGrammar"
    "canonicalTaoOperatorGrammarReceipt"
    "Apophatic-boundary, emptiness-use, non-action, soft-over-hard, return, anti-excess, anti-possession, and reversal operators are packaged as candidate-only Tao grammar."
    TaoGrammar.canonicalTaoOperatorReceiptCount
    "operator families remain interpretive grammar only"
    "doctrinal, empirical, political, clinical, and metaphysical authority stay blocked"
    "agda -i . DASHI/Culture/TaoOperatorGrammar.agda"
  ∷ mkTaoQiSummaryRow
    yinYangBoundaryLane
    "DASHI.Culture.YinYangPolarityBoundary"
    "canonicalYinYangPolarityBoundaryReceipt"
    "Yin/yang sits between Tao operator grammar and Qi formal-lens/operator grammar as a candidate-only polarity and transition boundary."
    YinYang.canonicalYinYangPolarityBoundaryRowCount
    "polarity rows remain interpretive grammar only"
    "empirical, clinical, spiritual, mystical, metaphysical, canonical-text, and reciprocal Tao/Qi promotion authority stay blocked"
    "agda -i . DASHI/Culture/YinYangPolarityBoundary.agda"
  ∷ mkTaoQiSummaryRow
    yinYangBoundaryLane
    "DASHI.Interop.TaoYinYangAdapter"
    "canonicalTaoYinYangBridgeReceipt"
    "Tao chapter motifs are re-read as candidate-only yin/yang polarity rows with fail-closed governance."
    (listCount TaoYinYang.canonicalTaoYinYangAdapterRows)
    "the Tao-to-yinyang bridge remains descriptive only"
    "no doctrine, empirical, clinical, spiritual, or metaphysical authority is promoted"
    "agda -i . DASHI/Interop/TaoYinYangAdapter.agda"
  ∷ mkTaoQiSummaryRow
    yinYangBoundaryLane
    "DASHI.Interop.YinYangQiAdapter"
    "canonicalYinYangQiBridgeReceipt"
    "Yin/yang polarity rows are carried into Qi carrier, role, and formal-lens surfaces as candidate-only bridges."
    (listCount YinYangQi.canonicalYinYangQiAdapterRows)
    "the yinyang-to-Qi bridge remains descriptive only"
    "truth, support, admissibility, runtime, theorem, clinical, and metaphysical authority remain false"
    "agda -i . DASHI/Interop/YinYangQiAdapter.agda"
  ∷ mkTaoQiSummaryRow
    yinYangBoundaryLane
    "DASHI.Interop.PolarityPhaseFieldBridge"
    "canonicalPolarityPhaseFieldBridge"
    "The polarity layer is extended into 369 phase rows, voxel/supervoxel support, Betti-ready field shape, wave mixtures, and superposition candidates under blocked authority governance."
    (listCount PhaseField.canonicalCarrierRows)
    "phase/field rows remain candidate-only interpretation surfaces"
    "no theorem, runtime, external, spiritual, metaphysical, or empirical authority is promoted"
    "agda -i . DASHI/Interop/PolarityPhaseFieldBridge.agda"
  ∷ mkTaoQiSummaryRow
    bettiSupportLane
    canonicalBettiSupportBoundaryModuleName
    canonicalBettiSupportBoundarySurfaceName
    "Betti support summaries sit over voxel/supervoxel support geometry as candidate-only topology diagnostics for connectedness, cycles, and void structure."
    Betti.canonicalBettiRowCount
    "Betti support remains a candidate-only topology summary surface"
    "no empirical, clinical, metaphysical, doctrinal, or theorem authority is promoted from topology diagnostics"
    "agda -i . DASHI/Interop/PolarityBettiSupportBoundary.agda"
  ∷ mkTaoQiSummaryRow
    bettiSupportLane
    canonicalBettiQiAdapterModuleName
    canonicalBettiQiAdapterSurfaceName
    "Betti support summaries are carried into Qi role, carrier, and formal-lens surfaces as candidate-only topology-to-Qi adapter rows."
    (listCount BettiQi.canonicalBettiQiAdapterRows)
    "the Betti-to-Qi bridge remains descriptive only"
    "truth, support, admissibility, runtime, theorem, clinical, and metaphysical authority remain false"
    "agda -i . DASHI/Interop/BettiQiAdapter.agda"
  ∷ mkTaoQiSummaryRow
    qiRoleGrammarLane
    "DASHI.Culture.QiOperatorTheoryBoundary"
    "canonicalQiOperatorTheoryBoundaryReceipt"
    "Qi operator theory supplies candidate-only role grammar for state-space, operator, observable, spectrum-tool, boundary-gate, obstruction, algebra, proof-obligation, and decomposition rows."
    (listCount QiTheory.canonicalQiRoleCoreAlignmentRows)
    "role grammar is descriptive and stays below promotion"
    "empirical, spiritual, mystical, clinical, environmental, legal, and scientific authority remain false"
    "agda -i . DASHI/Culture/QiOperatorTheoryBoundary.agda"
  ∷ mkTaoQiSummaryRow
    qiCarrierFieldLane
    "DASHI.Interop.QiCarrierFieldBridge"
    "canonicalQiCarrierFieldBridgeReceipt"
    "Feng Shui, Tai Chi, and Meditation are carried as three candidate-only Qi carrier domains with truth, support, admissibility, clinical, and metaphysical flags closed."
    (listCount QiBridge.canonicalQiCarrierFieldRows)
    "carrier taxonomy is descriptive and remains candidate-only"
    "truth, support, admissibility, clinical, and metaphysical authority stay false"
    "agda -i . DASHI/Interop/QiCarrierFieldBridge.agda"
  ∷ mkTaoQiSummaryRow
    taoQiBridgeLane
    "DASHI.Promotion.TaoQiObligationIndex"
    "canonicalTaoQiObligationIndexReceipt"
    "Tao reading receipts and Qi role grammar are linked as a cross-surface interpretive bridge only; the bridge carries candidate payload, not doctrine."
    (listCount TaoQi.canonicalTaoQiAdapterRows)
    "the Tao/Qi bridge is kept descriptive and non-promoting"
    "no doctrine, empirical, clinical, mystical, metaphysical, or authority claim is promoted"
    "agda -i . DASHI/Promotion/TaoQiObligationIndex.agda"
  ∷ mkTaoQiSummaryRow
    taoQiBridgeLane
    "DASHI.Interop.TaoMeditationQiAdapter"
    "canonicalTaoMeditationQiBridgeReceipt"
    "Breath, stillness, desire-reduction, muddy-settling, infant, spontaneity, and anti-excess motifs are mapped to meditation-state, operator, flow, boundary, and safety-route surfaces."
    7
    "the Tao/meditation bridge is interpretive only and not an instruction surface"
    "instruction, clinical, spiritual, and metaphysical authority remain false"
    "agda -i . DASHI/Interop/TaoMeditationQiAdapter.agda"
  ∷ []

canonicalTaoQiGovernanceRows : List TaoQiGovernanceRow
canonicalTaoQiGovernanceRows =
  mkTaoQiGovernanceRow
    governanceLane
    "DASHI.Culture.TaoChapterReadingReceipt"
    Tao.canonicalTaoSourceReceipt
    Tao.canonicalTaoBoundaryFailClosed
    Tao.chapter1Receipt
    TaoGrammar.canonicalTaoOperatorGrammarReceipt
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    TaoYinYang.canonicalTaoYinYangBridgeReceipt
    YinYangQi.canonicalYinYangQiBridgeReceipt
    PhaseField.canonicalPolarityPhaseFieldBridge
    canonicalBettiSupportBoundaryModuleName
    canonicalBettiSupportBoundarySurfaceName
    canonicalBettiQiAdapterModuleName
    canonicalBettiQiAdapterSurfaceName
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    TaoQi.canonicalTaoQiBridgeReceipt
    TaoMeditation.canonicalTaoMeditationQiBridgeReceipt
    PolarityField.canonicalPolarityFieldObligationIndexReceipt
    "Tao authority is fail-closed: empirical, spiritual, mystical, clinical, political, metaphysical, philological, canonical-text, and promoted-doctrine bits stay false while interpretiveCandidate and poeticFormalPayload remain true."
    "agda -i . DASHI/Culture/TaoChapterReadingReceipt.agda && agda -i . DASHI/Culture/QiOperatorTheoryBoundary.agda"
  ∷ mkTaoQiGovernanceRow
    governanceLane
    "DASHI.Culture.QiOperatorTheoryBoundary"
    Tao.canonicalTaoSourceReceipt
    Tao.canonicalTaoBoundaryFailClosed
    Tao.chapter1Receipt
    TaoGrammar.canonicalTaoOperatorGrammarReceipt
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    TaoYinYang.canonicalTaoYinYangBridgeReceipt
    YinYangQi.canonicalYinYangQiBridgeReceipt
    PhaseField.canonicalPolarityPhaseFieldBridge
    canonicalBettiSupportBoundaryModuleName
    canonicalBettiSupportBoundarySurfaceName
    canonicalBettiQiAdapterModuleName
    canonicalBettiQiAdapterSurfaceName
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    TaoQi.canonicalTaoQiBridgeReceipt
    TaoMeditation.canonicalTaoMeditationQiBridgeReceipt
    PolarityField.canonicalPolarityFieldObligationIndexReceipt
    "Qi authority is fail-closed: the operator-theory receipt remains candidate-only role grammar, and the core role family carries no external authority."
    "agda -i . DASHI/Culture/QiOperatorTheoryBoundary.agda && agda -i . DASHI/Interop/QiCarrierFieldBridge.agda"
  ∷ mkTaoQiGovernanceRow
    governanceLane
    "DASHI.Promotion.TaoQiObligationIndex"
    Tao.canonicalTaoSourceReceipt
    Tao.canonicalTaoBoundaryFailClosed
    Tao.chapter1Receipt
    TaoGrammar.canonicalTaoOperatorGrammarReceipt
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    TaoYinYang.canonicalTaoYinYangBridgeReceipt
    YinYangQi.canonicalYinYangQiBridgeReceipt
    PhaseField.canonicalPolarityPhaseFieldBridge
    canonicalBettiSupportBoundaryModuleName
    canonicalBettiSupportBoundarySurfaceName
    canonicalBettiQiAdapterModuleName
    canonicalBettiQiAdapterSurfaceName
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    TaoQi.canonicalTaoQiBridgeReceipt
    TaoMeditation.canonicalTaoMeditationQiBridgeReceipt
    PolarityField.canonicalPolarityFieldObligationIndexReceipt
    "The bridge surface stays candidate-only: Tao, yin/yang, Betti support, Qi, and the 369/voxel/wave field grammar are joined as receipts and role grammar, not as promoted doctrine, empirical validity, clinical instruction, or metaphysical authority."
    "agda -i . DASHI/Promotion/TaoQiObligationIndex.agda"
  ∷ []

canonicalTaoQiObligationIndexReceipt : TaoQiObligationIndexReceipt
canonicalTaoQiObligationIndexReceipt =
  taoQiObligationIndexReceipt
    Tao.canonicalTaoSourceReceipt
    Tao.canonicalTaoBoundaryFailClosed
    Tao.chapter1Receipt
    TaoGrammar.canonicalTaoOperatorGrammarReceipt
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    TaoYinYang.canonicalTaoYinYangBridgeReceipt
    YinYangQi.canonicalYinYangQiBridgeReceipt
    PhaseField.canonicalPolarityPhaseFieldBridge
    canonicalBettiSupportBoundaryModuleName
    canonicalBettiSupportBoundarySurfaceName
    canonicalBettiQiAdapterModuleName
    canonicalBettiQiAdapterSurfaceName
    QiTheory.canonicalQiOperatorTheoryBoundaryReceipt
    QiBridge.canonicalQiCarrierFieldBridgeReceipt
    TaoQi.canonicalTaoQiBridgeReceipt
    TaoMeditation.canonicalTaoMeditationQiBridgeReceipt
    PolarityField.canonicalPolarityFieldObligationIndexReceipt
    canonicalTaoQiSummaryRows
    canonicalTaoQiGovernanceRows
    true
    refl
    true
    refl
    false
    refl

canonicalTaoQiSummaryRowCount : Nat
canonicalTaoQiSummaryRowCount =
  listCount canonicalTaoQiSummaryRows

canonicalTaoQiGovernanceRowCount : Nat
canonicalTaoQiGovernanceRowCount =
  listCount canonicalTaoQiGovernanceRows

canonicalTaoQiIndexCandidateOnlyPayloadIsTrue :
  indexCandidateOnlyPayload canonicalTaoQiObligationIndexReceipt ≡ true
canonicalTaoQiIndexCandidateOnlyPayloadIsTrue =
  refl

canonicalTaoQiIndexAuthorityBlockedIsTrue :
  indexAuthorityBlocked canonicalTaoQiObligationIndexReceipt ≡ true
canonicalTaoQiIndexAuthorityBlockedIsTrue =
  refl

canonicalTaoQiIndexPromotesClaimIsFalse :
  indexPromotesClaim canonicalTaoQiObligationIndexReceipt ≡ false
canonicalTaoQiIndexPromotesClaimIsFalse =
  refl
