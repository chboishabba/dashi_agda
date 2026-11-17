module DASHI.Interop.TaoMeditationQiAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Culture.TaoChapterReadingReceipt as Tao
import DASHI.Interop.MeditationQiBridge as Meditation

------------------------------------------------------------------------
-- Tao -> Meditation-Qi adapter.
--
-- This module is a candidate-only bridge surface.  It maps Tao motifs such as
-- breath, stillness, desire reduction, muddy settling, infant, non-action,
-- spontaneity, and anti-excess into meditation-state facets, operators, flow
-- dimensions, boundary gates, and safety routes.
--
-- The adapter fails closed on instruction, clinical, spiritual, and
-- metaphysical authority.  It does not promote practice, truth, or doctrine;
-- it only records a reusable interpretive receipt.

data TaoMeditationQiBridgeStatus : Set where
  taoMeditationQiBridge_candidateOnly :
    TaoMeditationQiBridgeStatus

data TaoMeditationQiPromotion : Set where

taoMeditationQiPromotionImpossible :
  TaoMeditationQiPromotion →
  ⊥
taoMeditationQiPromotionImpossible ()

data TaoMeditationQiTargetFacet : Set where
  breathFieldTarget :
    Meditation.BreathField →
    TaoMeditationQiTargetFacet

  attentionFieldTarget :
    Meditation.AttentionField →
    TaoMeditationQiTargetFacet

  bodySensationFieldTarget :
    Meditation.BodySensationField →
    TaoMeditationQiTargetFacet

  residualFieldTarget :
    Meditation.ResidualField →
    TaoMeditationQiTargetFacet

  intentionYiTarget :
    Meditation.IntentionYi →
    TaoMeditationQiTargetFacet

  meditationOperatorTarget :
    Meditation.MeditationOperator →
    TaoMeditationQiTargetFacet

  flowDimensionTarget :
    Meditation.FlowStateDimension →
    TaoMeditationQiTargetFacet

  boundaryGateTarget :
    Meditation.MeditationBoundaryGate →
    TaoMeditationQiTargetFacet

  safetyRouteTarget :
    Meditation.MeditationSafetyRoute →
    TaoMeditationQiTargetFacet

record TaoMeditationQiAdapterRow : Set where
  constructor taoMeditationQiAdapterRow
  field
    rowId :
      Nat

    sourceMotif :
      Tao.TaoMotif

    sourceReadingKind :
      Tao.TaoReadingKind

    sourceQualifier :
      Tao.TaoQualifier

    targetFacet :
      TaoMeditationQiTargetFacet

    rowProfile :
      String

    rowStatement :
      String

    candidateOnly :
      Bool

    noInstructionAuthority :
      Bool

    noClinicalAuthority :
      Bool

    noSpiritualAuthority :
      Bool

    noMetaphysicalAuthority :
      Bool

open TaoMeditationQiAdapterRow public

record TaoMeditationQiAdapterRowReceipt
  (row : TaoMeditationQiAdapterRow) :
  Set where
  constructor taoMeditationQiAdapterRowReceipt
  field
    rowCandidateOnly :
      candidateOnly row ≡ true

    rowNoInstructionAuthority :
      noInstructionAuthority row ≡ false

    rowNoClinicalAuthority :
      noClinicalAuthority row ≡ false

    rowNoSpiritualAuthority :
      noSpiritualAuthority row ≡ false

    rowNoMetaphysicalAuthority :
      noMetaphysicalAuthority row ≡ false

open TaoMeditationQiAdapterRowReceipt public

breathRow : TaoMeditationQiAdapterRow
breathRow =
  taoMeditationQiAdapterRow
    zero
    Tao.breath
    Tao.PracticeAphorism
    Tao.translationDependentQualifier
    (breathFieldTarget Meditation.breathRhythmField)
    "breath-to-breath-field"
    "Breath is read as a candidate cue for rhythmic attention and renewed settling."
    true
    false
    false
    false
    false

stillnessRow : TaoMeditationQiAdapterRow
stillnessRow =
  taoMeditationQiAdapterRow
    (suc zero)
    Tao.stillness
    Tao.StillnessGrammar
    Tao.translationDependentQualifier
    (meditationOperatorTarget Meditation.equanimityOperator)
    "stillness-to-equanimity-operator"
    "Stillness is read as a candidate cue for equanimity and non-grasping."
    true
    false
    false
    false
    false

desireReductionRow : TaoMeditationQiAdapterRow
desireReductionRow =
  taoMeditationQiAdapterRow
    (suc (suc zero))
    Tao.desireReduction
    Tao.DesireReductionGrammar
    Tao.translationDependentQualifier
    (flowDimensionTarget Meditation.coherenceDimension)
    "desire-reduction-to-coherence-dimension"
    "Desire reduction is read as a candidate cue for coherence and reduced stickiness."
    true
    false
    false
    false
    false

muddySettlingRow : TaoMeditationQiAdapterRow
muddySettlingRow =
  taoMeditationQiAdapterRow
    (suc (suc (suc zero)))
    Tao.muddySettling
    Tao.ReturnToRootGrammar
    Tao.translationDependentQualifier
    (bodySensationFieldTarget Meditation.embodiedSensationField)
    "muddy-settling-to-embodied-sensation"
    "Muddy settling is read as a candidate cue for embodiment and grounded somatic contact."
    true
    false
    false
    false
    false

infantRow : TaoMeditationQiAdapterRow
infantRow =
  taoMeditationQiAdapterRow
    (suc (suc (suc (suc zero))))
    Tao.infant
    Tao.PracticeAphorism
    Tao.translationDependentQualifier
    (intentionYiTarget Meditation.nonForcingIntentionYi)
    "infant-to-non-forcing-intention"
    "Infant imagery is read as a candidate cue for non-forcing intention and basic trust."
    true
    false
    false
    false
    false

spontaneityRow : TaoMeditationQiAdapterRow
spontaneityRow =
  taoMeditationQiAdapterRow
    (suc (suc (suc (suc (suc zero)))))
    Tao.spontaneousOrdering
    Tao.NonActionGovernance
    Tao.translationDependentQualifier
    (safetyRouteTarget Meditation.observeLabelMetaboliseRoute)
    "spontaneity-to-observe-label-metabolise-route"
    "Spontaneity and non-action are read as a candidate cue for observing and metabolising without forcing."
    true
    false
    false
    false
    false

antiExcessRow : TaoMeditationQiAdapterRow
antiExcessRow =
  taoMeditationQiAdapterRow
    (suc (suc (suc (suc (suc (suc zero))))))
    Tao.antiExcess
    Tao.AntiExcessGrammar
    Tao.translationDependentQualifier
    (boundaryGateTarget Meditation.groundingGate)
    "anti-excess-to-grounding-gate"
    "Anti-excess is read as a candidate cue for grounding boundaries and restraint."
    true
    false
    false
    false
    false

canonicalTaoMeditationQiAdapterRows :
  List TaoMeditationQiAdapterRow
canonicalTaoMeditationQiAdapterRows =
  breathRow
  ∷ stillnessRow
  ∷ desireReductionRow
  ∷ muddySettlingRow
  ∷ infantRow
  ∷ spontaneityRow
  ∷ antiExcessRow
  ∷ []

breathRowReceipt : TaoMeditationQiAdapterRowReceipt breathRow
breathRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

stillnessRowReceipt : TaoMeditationQiAdapterRowReceipt stillnessRow
stillnessRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

desireReductionRowReceipt :
  TaoMeditationQiAdapterRowReceipt desireReductionRow
desireReductionRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

muddySettlingRowReceipt :
  TaoMeditationQiAdapterRowReceipt muddySettlingRow
muddySettlingRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

infantRowReceipt : TaoMeditationQiAdapterRowReceipt infantRow
infantRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

spontaneityRowReceipt : TaoMeditationQiAdapterRowReceipt spontaneityRow
spontaneityRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

antiExcessRowReceipt : TaoMeditationQiAdapterRowReceipt antiExcessRow
antiExcessRowReceipt =
  taoMeditationQiAdapterRowReceipt
    refl
    refl
    refl
    refl
    refl

record TaoMeditationQiAuthorityClosure : Set where
  constructor taoMeditationQiAuthorityClosure
  field
    noInstructionAuthority :
      Bool

    noInstructionAuthorityIsFalse :
      noInstructionAuthority ≡ false

    noClinicalAuthority :
      Bool

    noClinicalAuthorityIsFalse :
      noClinicalAuthority ≡ false

    noSpiritualAuthority :
      Bool

    noSpiritualAuthorityIsFalse :
      noSpiritualAuthority ≡ false

    noMetaphysicalAuthority :
      Bool

    noMetaphysicalAuthorityIsFalse :
      noMetaphysicalAuthority ≡ false

open TaoMeditationQiAuthorityClosure public

canonicalTaoMeditationQiAuthorityClosure :
  TaoMeditationQiAuthorityClosure
canonicalTaoMeditationQiAuthorityClosure =
  taoMeditationQiAuthorityClosure
    false
    refl
    false
    refl
    false
    refl
    false
    refl

taoMeditationQiCandidateOnlyRow :
  CandidateOnly.CandidateOnlyRow
taoMeditationQiCandidateOnlyRow =
  CandidateOnly.candidateOnlyRow
    "tao-meditation-qi-adapter candidate-only bridge"
    "DASHI.Interop.TaoMeditationQiAdapter"
    "TaoMeditationQiBridge"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Tao motifs are carried into meditation-qi facets as candidate-only interpretive rows."
    "No instruction, clinical, spiritual, metaphysical, or promotional authority is supplied."
    true
    false
    false
    false
    false
    false
    false
    false

taoMeditationQiCandidateOnlyReceipt :
  CandidateOnly.CandidateOnlyReceipt
    taoMeditationQiCandidateOnlyRow
taoMeditationQiCandidateOnlyReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record TaoMeditationQiBridgeReceipt : Set where
  constructor taoMeditationQiBridgeReceipt
  field
    sourceReceipt :
      Tao.TaoSourceReceipt

    sourceReceiptIsCanonical :
      sourceReceipt ≡ Tao.canonicalTaoSourceReceipt

    meditationQiBridgeReceipt :
      Meditation.MeditationQiBridgeReceipt

    meditationQiBridgeReceiptIsCanonical :
      meditationQiBridgeReceipt ≡ Meditation.canonicalMeditationQiBridgeReceipt

    candidateOnlyCoreAdapter :
      CandidateOnly.CandidateOnlyReceipt
        taoMeditationQiCandidateOnlyRow

    candidateOnlyCoreAdapterIsCanonical :
      candidateOnlyCoreAdapter ≡ taoMeditationQiCandidateOnlyReceipt

    bridgeStatus :
      TaoMeditationQiBridgeStatus

    bridgeStatusIsCanonical :
      bridgeStatus ≡ taoMeditationQiBridge_candidateOnly

    authorityClosure :
      TaoMeditationQiAuthorityClosure

    authorityClosureIsCanonical :
      authorityClosure ≡ canonicalTaoMeditationQiAuthorityClosure

    bridgeRows :
      List TaoMeditationQiAdapterRow

    bridgeRowsAreCanonical :
      bridgeRows ≡ canonicalTaoMeditationQiAdapterRows

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    promotionImpossible :
      TaoMeditationQiPromotion →
      ⊥

open TaoMeditationQiBridgeReceipt public

canonicalTaoMeditationQiBridgeReceipt :
  TaoMeditationQiBridgeReceipt
canonicalTaoMeditationQiBridgeReceipt =
  taoMeditationQiBridgeReceipt
    Tao.canonicalTaoSourceReceipt
    refl
    Meditation.canonicalMeditationQiBridgeReceipt
    refl
    taoMeditationQiCandidateOnlyReceipt
    refl
    taoMeditationQiBridge_candidateOnly
    refl
    canonicalTaoMeditationQiAuthorityClosure
    refl
    canonicalTaoMeditationQiAdapterRows
    refl
    true
    refl
    false
    refl
    taoMeditationQiPromotionImpossible

canonicalTaoMeditationQiBridgeCandidateOnly :
  candidateOnly canonicalTaoMeditationQiBridgeReceipt ≡ true
canonicalTaoMeditationQiBridgeCandidateOnly =
  refl

canonicalTaoMeditationQiBridgePromotedFalse :
  promoted canonicalTaoMeditationQiBridgeReceipt ≡ false
canonicalTaoMeditationQiBridgePromotedFalse =
  refl

canonicalTaoMeditationQiBridgeNoInstructionFalse :
  noInstructionAuthority
    (authorityClosure canonicalTaoMeditationQiBridgeReceipt)
  ≡
  false
canonicalTaoMeditationQiBridgeNoInstructionFalse =
  refl

canonicalTaoMeditationQiBridgeNoClinicalFalse :
  noClinicalAuthority
    (authorityClosure canonicalTaoMeditationQiBridgeReceipt)
  ≡
  false
canonicalTaoMeditationQiBridgeNoClinicalFalse =
  refl

canonicalTaoMeditationQiBridgeNoSpiritualFalse :
  noSpiritualAuthority
    (authorityClosure canonicalTaoMeditationQiBridgeReceipt)
  ≡
  false
canonicalTaoMeditationQiBridgeNoSpiritualFalse =
  refl

canonicalTaoMeditationQiBridgeNoMetaphysicalFalse :
  noMetaphysicalAuthority
    (authorityClosure canonicalTaoMeditationQiBridgeReceipt)
  ≡
  false
canonicalTaoMeditationQiBridgeNoMetaphysicalFalse =
  refl
