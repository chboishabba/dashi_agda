module DASHI.Interop.TaoYinYangAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.TaoChapterReadingReceipt as Tao
import DASHI.Culture.YinYangPolarityBoundary as YinYang

------------------------------------------------------------------------
-- Tao -> yin/yang polarity adapter.
--
-- This module is deliberately candidate-only.  It re-reads Tao motifs and
-- reading kinds as polarity rows that land in either yin or yang, but it does
-- not promote doctrinal, empirical, clinical, spiritual, mystical,
-- metaphysical, political, or philological authority.  The bridge is useful
-- as a routing ledger only: it records how a Tao motif is being reinterpreted
-- while failing closed on promotion.

data TaoYinYangPolarity : Set where
  yin : TaoYinYangPolarity
  yang : TaoYinYangPolarity

data TaoYinYangAdapterStrength : Set where
  ApophaticBoundaryAlignment : TaoYinYangAdapterStrength
  ComplementarityAlignment : TaoYinYangAdapterStrength
  ValleyMetaphorAlignment : TaoYinYangAdapterStrength
  WaterFlowAlignment : TaoYinYangAdapterStrength
  RootReturnAlignment : TaoYinYangAdapterStrength
  StillnessAlignment : TaoYinYangAdapterStrength
  DesireReductionAlignment : TaoYinYangAdapterStrength
  SoftnessReversalAlignment : TaoYinYangAdapterStrength
  MinimalGovernanceAlignment : TaoYinYangAdapterStrength
  CandidateOnlyAlignment : TaoYinYangAdapterStrength

record TaoYinYangAuthorityBits : Set where
  constructor taoYinYangAuthorityBits
  field
    taoPromotesYinYang : Bool
    yinYangPromotesTao : Bool
    empiricalAuthority : Bool
    clinicalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    metaphysicalAuthority : Bool
    politicalAuthority : Bool
    philologicalAuthority : Bool
    practiceInstruction : Bool
    candidateInteropOnly : Bool

open TaoYinYangAuthorityBits public

canonicalTaoYinYangAuthorityBits : TaoYinYangAuthorityBits
canonicalTaoYinYangAuthorityBits =
  taoYinYangAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    true

record TaoYinYangFailClosed : Set where
  constructor taoYinYangFailClosed
  field
    taoPromotesYinYangFalse :
      taoPromotesYinYang canonicalTaoYinYangAuthorityBits ≡ false
    yinYangPromotesTaoFalse :
      yinYangPromotesTao canonicalTaoYinYangAuthorityBits ≡ false
    empiricalAuthorityFalse :
      empiricalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    clinicalAuthorityFalse :
      clinicalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    spiritualAuthorityFalse :
      spiritualAuthority canonicalTaoYinYangAuthorityBits ≡ false
    mysticalAuthorityFalse :
      mysticalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    metaphysicalAuthorityFalse :
      metaphysicalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    politicalAuthorityFalse :
      politicalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    philologicalAuthorityFalse :
      philologicalAuthority canonicalTaoYinYangAuthorityBits ≡ false
    practiceInstructionFalse :
      practiceInstruction canonicalTaoYinYangAuthorityBits ≡ false
    candidateInteropOnlyTrue :
      candidateInteropOnly canonicalTaoYinYangAuthorityBits ≡ true

canonicalTaoYinYangFailClosed : TaoYinYangFailClosed
canonicalTaoYinYangFailClosed =
  taoYinYangFailClosed
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

data TaoYinYangPromotion : Set where

taoYinYangPromotionImpossible :
  TaoYinYangPromotion →
  ⊥
taoYinYangPromotionImpossible ()

record TaoYinYangGovernance : Set where
  constructor taoYinYangGovernance
  field
    governanceLabel : String
    governanceScope : String
    authorityBits : TaoYinYangAuthorityBits
    authorityBitsIsCanonical :
      authorityBits ≡ canonicalTaoYinYangAuthorityBits
    failClosed : TaoYinYangFailClosed
    failClosedIsCanonical :
      failClosed ≡ canonicalTaoYinYangFailClosed
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    promoted : Bool
    promotedIsFalse : promoted ≡ false
    promotionImpossible : TaoYinYangPromotion → ⊥

open TaoYinYangGovernance public

canonicalTaoYinYangPromotionImpossible :
  TaoYinYangPromotion → ⊥
canonicalTaoYinYangPromotionImpossible ()

canonicalTaoYinYangGovernance : TaoYinYangGovernance
canonicalTaoYinYangGovernance =
  taoYinYangGovernance
    "tao-yinyang-candidate-governance"
    "chapter-local polarity rereading"
    canonicalTaoYinYangAuthorityBits
    refl
    canonicalTaoYinYangFailClosed
    refl
    true
    refl
    false
    refl
    canonicalTaoYinYangPromotionImpossible

record TaoYinYangAdapterRow : Set where
  constructor taoYinYangAdapterRow
  field
    rowId : Nat
    chapterId : Tao.TaoChapterId
    sourceMotif : Tao.TaoMotif
    sourceReadingKind : Tao.TaoReadingKind
    sourceQualifier : Tao.TaoQualifier
    polarity : TaoYinYangPolarity
    adapterStrength : TaoYinYangAdapterStrength
    receiptTag : String
    rowStatement : String
    candidateOnly : Bool
    authorityAllowed : Bool

open TaoYinYangAdapterRow public

record TaoYinYangAdapterRowReceipt (row : TaoYinYangAdapterRow) : Set where
  constructor taoYinYangAdapterRowReceipt
  field
    candidateOnlyTrue :
      candidateOnly row ≡ true
    authorityAllowedFalse :
      authorityAllowed row ≡ false

open TaoYinYangAdapterRowReceipt public

chapter1YinBoundaryRow : TaoYinYangAdapterRow
chapter1YinBoundaryRow =
  taoYinYangAdapterRow
    zero
    Tao.chapter1
    Tao.dao
    Tao.ApophaticBoundary
    Tao.translationDependentQualifier
    yin
    ApophaticBoundaryAlignment
    "yin-apophatic-boundary"
    "Chapter 1 is read as yin because the named Tao is treated as a boundary of absence rather than a promotable ontology."
    true
    false

chapter2YangComplementarityRow : TaoYinYangAdapterRow
chapter2YangComplementarityRow =
  taoYinYangAdapterRow
    (suc zero)
    Tao.chapter2
    Tao.complementarity
    Tao.ComplementarityGrammar
    Tao.translationDependentQualifier
    yang
    ComplementarityAlignment
    "yang-complementarity"
    "Chapter 2 is read as yang because the paired emergence of naming and contrast is treated as an active polarity articulation."
    true
    false

chapter6YinValleyRow : TaoYinYangAdapterRow
chapter6YinValleyRow =
  taoYinYangAdapterRow
    (suc (suc zero))
    Tao.chapter6
    Tao.valley
    Tao.OriginMetaphor
    Tao.translationDependentQualifier
    yin
    ValleyMetaphorAlignment
    "yin-valley-metaphor"
    "Chapter 6 is read as yin because the valley image anchors receptive depth, hidden source, and non-assertive continuity."
    true
    false

chapter8YinWaterRow : TaoYinYangAdapterRow
chapter8YinWaterRow =
  taoYinYangAdapterRow
    (suc (suc (suc zero)))
    Tao.chapter8
    Tao.water
    Tao.SoftOverHardOperator
    Tao.translationDependentQualifier
    yin
    WaterFlowAlignment
    "yin-water-flow"
    "Chapter 8 is read as yin because water is interpreted as yielding transport rather than coercive force."
    true
    false

chapter10YinRootReturnRow : TaoYinYangAdapterRow
chapter10YinRootReturnRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc zero))))
    Tao.chapter10
    Tao.returnToRoot
    Tao.ReturnToRootGrammar
    Tao.translationDependentQualifier
    yin
    RootReturnAlignment
    "yin-return-to-root"
    "Chapter 10 is read as yin because returning to the root is treated as inward settling rather than outward expansion."
    true
    false

chapter16YinStillnessRow : TaoYinYangAdapterRow
chapter16YinStillnessRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc (suc zero)))))
    Tao.chapter16
    Tao.stillness
    Tao.StillnessGrammar
    Tao.translationDependentQualifier
    yin
    StillnessAlignment
    "yin-stillness"
    "Chapter 16 is read as yin because stillness is treated as the polarity of deep receptivity and non-grasping return."
    true
    false

chapter17YangMinimalGovernanceRow : TaoYinYangAdapterRow
chapter17YangMinimalGovernanceRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc (suc (suc zero))))))
    Tao.chapter17
    Tao.rulerBarelyKnown
    Tao.RulerTaxonomy
    Tao.translationDependentQualifier
    yang
    MinimalGovernanceAlignment
    "yang-minimal-governance"
    "Chapter 17 is read as yang because minimal governance is treated as an enacted ordering principle rather than passive withdrawal."
    true
    false

chapter19YinDesireReductionRow : TaoYinYangAdapterRow
chapter19YinDesireReductionRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    Tao.chapter19
    Tao.desireReduction
    Tao.DesireReductionGrammar
    Tao.translationDependentQualifier
    yin
    DesireReductionAlignment
    "yin-desire-reduction"
    "Chapter 19 is read as yin because desire reduction is interpreted as a constraining of demand and a lowering of friction."
    true
    false

chapter36YinSoftnessRow : TaoYinYangAdapterRow
chapter36YinSoftnessRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    Tao.chapter36
    Tao.softness
    Tao.ReversalGrammar
    Tao.translationDependentQualifier
    yin
    SoftnessReversalAlignment
    "yin-softness-reversal"
    "Chapter 36 is read as yin because softness and reversal are treated as collapse of rigid assertion into receptive correction."
    true
    false

chapter37YangSpontaneityRow : TaoYinYangAdapterRow
chapter37YangSpontaneityRow =
  taoYinYangAdapterRow
    (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    Tao.chapter37
    Tao.spontaneousOrdering
    Tao.NonActionGovernance
    Tao.translationDependentQualifier
    yang
    CandidateOnlyAlignment
    "yang-spontaneity"
    "Chapter 37 is read as yang because spontaneous ordering is treated as the active stabilization of non-forcing governance."
    true
    false

canonicalTaoYinYangAdapterRows : List TaoYinYangAdapterRow
canonicalTaoYinYangAdapterRows =
  chapter1YinBoundaryRow
  ∷ chapter2YangComplementarityRow
  ∷ chapter6YinValleyRow
  ∷ chapter8YinWaterRow
  ∷ chapter10YinRootReturnRow
  ∷ chapter16YinStillnessRow
  ∷ chapter17YangMinimalGovernanceRow
  ∷ chapter19YinDesireReductionRow
  ∷ chapter36YinSoftnessRow
  ∷ chapter37YangSpontaneityRow
  ∷ []

chapter1YinBoundaryRowReceipt :
  TaoYinYangAdapterRowReceipt chapter1YinBoundaryRow
chapter1YinBoundaryRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter2YangComplementarityRowReceipt :
  TaoYinYangAdapterRowReceipt chapter2YangComplementarityRow
chapter2YangComplementarityRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter6YinValleyRowReceipt :
  TaoYinYangAdapterRowReceipt chapter6YinValleyRow
chapter6YinValleyRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter8YinWaterRowReceipt :
  TaoYinYangAdapterRowReceipt chapter8YinWaterRow
chapter8YinWaterRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter10YinRootReturnRowReceipt :
  TaoYinYangAdapterRowReceipt chapter10YinRootReturnRow
chapter10YinRootReturnRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter16YinStillnessRowReceipt :
  TaoYinYangAdapterRowReceipt chapter16YinStillnessRow
chapter16YinStillnessRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter17YangMinimalGovernanceRowReceipt :
  TaoYinYangAdapterRowReceipt chapter17YangMinimalGovernanceRow
chapter17YangMinimalGovernanceRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter19YinDesireReductionRowReceipt :
  TaoYinYangAdapterRowReceipt chapter19YinDesireReductionRow
chapter19YinDesireReductionRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter36YinSoftnessRowReceipt :
  TaoYinYangAdapterRowReceipt chapter36YinSoftnessRow
chapter36YinSoftnessRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

chapter37YangSpontaneityRowReceipt :
  TaoYinYangAdapterRowReceipt chapter37YangSpontaneityRow
chapter37YangSpontaneityRowReceipt =
  taoYinYangAdapterRowReceipt refl refl

record TaoYinYangBridgeReceipt : Set where
  constructor taoYinYangBridgeReceipt
  field
    taoSource : Tao.TaoSourceReceipt
    taoSourceIsCanonical :
      taoSource ≡ Tao.canonicalTaoSourceReceipt
    polarityBoundary :
      YinYang.YinYangPolarityBoundaryReceipt
    polarityBoundaryIsCanonical :
      polarityBoundary ≡ YinYang.canonicalYinYangPolarityBoundaryReceipt
    governance : TaoYinYangGovernance
    governanceIsCanonical :
      governance ≡ canonicalTaoYinYangGovernance
    adapterRows : List TaoYinYangAdapterRow
    adapterRowsAreCanonical :
      adapterRows ≡ canonicalTaoYinYangAdapterRows
    bridgeStatement : String

open TaoYinYangBridgeReceipt public

canonicalTaoYinYangBridgeReceipt : TaoYinYangBridgeReceipt
canonicalTaoYinYangBridgeReceipt =
  taoYinYangBridgeReceipt
    Tao.canonicalTaoSourceReceipt
    refl
    YinYang.canonicalYinYangPolarityBoundaryReceipt
    refl
    canonicalTaoYinYangGovernance
    refl
    canonicalTaoYinYangAdapterRows
    refl
    "Tao motifs are re-read as candidate-only yin/yang polarity rows with explicit fail-closed governance and no authority promotion."

canonicalTaoYinYangBridgeReceiptCandidateOnly :
  candidateOnly (governance canonicalTaoYinYangBridgeReceipt) ≡ true
canonicalTaoYinYangBridgeReceiptCandidateOnly =
  candidateOnlyIsTrue (governance canonicalTaoYinYangBridgeReceipt)

canonicalTaoYinYangBridgeReceiptPromotedFalse :
  promoted (governance canonicalTaoYinYangBridgeReceipt) ≡ false
canonicalTaoYinYangBridgeReceiptPromotedFalse =
  promotedIsFalse (governance canonicalTaoYinYangBridgeReceipt)

canonicalTaoYinYangBridgeReceiptNoPromotion :
  TaoYinYangPromotion →
  ⊥
canonicalTaoYinYangBridgeReceiptNoPromotion =
  promotionImpossible (governance canonicalTaoYinYangBridgeReceipt)
