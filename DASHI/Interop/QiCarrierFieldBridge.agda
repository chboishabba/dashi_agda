module DASHI.Interop.QiCarrierFieldBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.InterMediaCarrierBridge as IM

------------------------------------------------------------------------
-- Qi carrier-field taxonomy.
--
-- This module records Feng Shui, Tai Chi, and Meditation as three carrier
-- domains over a shared non-promoting bridge vocabulary.  The classifier is a
-- descriptive candidate surface only.

data QiDomain : Set where
  fengShuiQiDomain :
    QiDomain

  taiChiQiDomain :
    QiDomain

  meditationQiDomain :
    QiDomain

canonicalQiDomains : List QiDomain
canonicalQiDomains =
  fengShuiQiDomain
  ∷ taiChiQiDomain
  ∷ meditationQiDomain
  ∷ []

data QiCarrier : Set where
  roomQiCarrier :
    QiCarrier

  landscapeQiCarrier :
    QiCarrier

  thresholdQiCarrier :
    QiCarrier

  relationQiCarrier :
    QiCarrier

  bodyQiCarrier :
    QiCarrier

  breathQiCarrier :
    QiCarrier

  postureQiCarrier :
    QiCarrier

  forceQiCarrier :
    QiCarrier

  movementQiCarrier :
    QiCarrier

  attentionQiCarrier :
    QiCarrier

  perceptionQiCarrier :
    QiCarrier

  affectQiCarrier :
    QiCarrier

  memoryQiCarrier :
    QiCarrier

  selfModelQiCarrier :
    QiCarrier

  residualMindNoiseQiCarrier :
    QiCarrier

  namedQiCarrier :
    String →
    QiCarrier

fengShuiQiCarriers : List QiCarrier
fengShuiQiCarriers =
  roomQiCarrier
  ∷ landscapeQiCarrier
  ∷ thresholdQiCarrier
  ∷ relationQiCarrier
  ∷ []

taiChiQiCarriers : List QiCarrier
taiChiQiCarriers =
  bodyQiCarrier
  ∷ breathQiCarrier
  ∷ postureQiCarrier
  ∷ forceQiCarrier
  ∷ movementQiCarrier
  ∷ []

meditationQiCarriers : List QiCarrier
meditationQiCarriers =
  attentionQiCarrier
  ∷ breathQiCarrier
  ∷ perceptionQiCarrier
  ∷ affectQiCarrier
  ∷ memoryQiCarrier
  ∷ selfModelQiCarrier
  ∷ residualMindNoiseQiCarrier
  ∷ []

data QiClassifier : Set where
  shengQi :
    QiClassifier

  siQi :
    QiClassifier

  shaQi :
    QiClassifier

  shengMindQi :
    QiClassifier

  siMindQi :
    QiClassifier

  shaMindQi :
    QiClassifier

canonicalQiClassifiers : List QiClassifier
canonicalQiClassifiers =
  shengQi
  ∷ siQi
  ∷ shaQi
  ∷ shengMindQi
  ∷ siMindQi
  ∷ shaMindQi
  ∷ []

data MindQiDescriptor : Set where
  clearMindQi :
    MindQiDescriptor

  spaciousMindQi :
    MindQiDescriptor

  coherentMindQi :
    MindQiDescriptor

  embodiedMindQi :
    MindQiDescriptor

  steadyMindQi :
    MindQiDescriptor

  renewingMindQi :
    MindQiDescriptor

  dullMindQi :
    MindQiDescriptor

  collapsedMindQi :
    MindQiDescriptor

  dissociatedMindQi :
    MindQiDescriptor

  sleepyMindQi :
    MindQiDescriptor

  foggyMindQi :
    MindQiDescriptor

  intrusiveMindQi :
    MindQiDescriptor

  racingMindQi :
    MindQiDescriptor

  agitatedMindQi :
    MindQiDescriptor

  compulsiveMindQi :
    MindQiDescriptor

  selfAttackingMindQi :
    MindQiDescriptor

canonicalShengMindDescriptors : List MindQiDescriptor
canonicalShengMindDescriptors =
  clearMindQi
  ∷ spaciousMindQi
  ∷ coherentMindQi
  ∷ embodiedMindQi
  ∷ steadyMindQi
  ∷ renewingMindQi
  ∷ []

canonicalSiMindDescriptors : List MindQiDescriptor
canonicalSiMindDescriptors =
  dullMindQi
  ∷ collapsedMindQi
  ∷ dissociatedMindQi
  ∷ sleepyMindQi
  ∷ foggyMindQi
  ∷ []

canonicalShaMindDescriptors : List MindQiDescriptor
canonicalShaMindDescriptors =
  intrusiveMindQi
  ∷ racingMindQi
  ∷ agitatedMindQi
  ∷ compulsiveMindQi
  ∷ selfAttackingMindQi
  ∷ []

data QiCarrierFieldPromotion : Set where

qiCarrierFieldPromotionImpossible :
  QiCarrierFieldPromotion →
  ⊥
qiCarrierFieldPromotionImpossible ()

record QiCarrierFieldRow : Set where
  constructor qiCarrierFieldRow
  field
    qiDomain :
      QiDomain

    qiCarrier :
      QiCarrier

    qiClassifier :
      QiClassifier

    qiRowIndex :
      Nat

    qiProfile :
      String

    qiStatement :
      String

    qiCandidateOnly :
      Bool

    qiTruthAuthority :
      Bool

    qiSupportAuthority :
      Bool

    qiAdmissibilityAuthority :
      Bool

    qiClinicalAuthority :
      Bool

    qiMetaphysicalAuthority :
      Bool

open QiCarrierFieldRow public

record QiCarrierFieldRowReceipt
  (row : QiCarrierFieldRow) :
  Set where
  constructor qiCarrierFieldRowReceipt
  field
    qiRowCandidateOnly :
      qiCandidateOnly row ≡ true

    qiRowTruthFalse :
      qiTruthAuthority row ≡ false

    qiRowSupportFalse :
      qiSupportAuthority row ≡ false

    qiRowAdmissibilityFalse :
      qiAdmissibilityAuthority row ≡ false

    qiRowClinicalFalse :
      qiClinicalAuthority row ≡ false

    qiRowMetaphysicalFalse :
      qiMetaphysicalAuthority row ≡ false

open QiCarrierFieldRowReceipt public

fengShuiQiRow : QiCarrierFieldRow
fengShuiQiRow =
  qiCarrierFieldRow
    fengShuiQiDomain
    roomQiCarrier
    shengQi
    zero
    "feng-shui-space-carrier"
    "Feng Shui reads Qi through room, landscape, threshold, and relation carriers."
    true
    false
    false
    false
    false
    false

taiChiQiRow : QiCarrierFieldRow
taiChiQiRow =
  qiCarrierFieldRow
    taiChiQiDomain
    movementQiCarrier
    shengQi
    zero
    "tai-chi-moving-body-force-carrier"
    "Tai Chi reads Qi through body, breath, posture, force, and movement carriers."
    true
    false
    false
    false
    false
    false

meditationQiRow : QiCarrierFieldRow
meditationQiRow =
  qiCarrierFieldRow
    meditationQiDomain
    attentionQiCarrier
    shengMindQi
    zero
    "meditation-attention-carrier"
    "Meditation reads Qi through attention, breath, awareness, and residual mind-noise."
    true
    false
    false
    false
    false
    false

fengShuiQiRowReceipt : QiCarrierFieldRowReceipt fengShuiQiRow
fengShuiQiRowReceipt =
  qiCarrierFieldRowReceipt refl refl refl refl refl refl

taiChiQiRowReceipt : QiCarrierFieldRowReceipt taiChiQiRow
taiChiQiRowReceipt =
  qiCarrierFieldRowReceipt refl refl refl refl refl refl

meditationQiRowReceipt : QiCarrierFieldRowReceipt meditationQiRow
meditationQiRowReceipt =
  qiCarrierFieldRowReceipt refl refl refl refl refl refl

canonicalQiCarrierFieldRows : List QiCarrierFieldRow
canonicalQiCarrierFieldRows =
  fengShuiQiRow
  ∷ taiChiQiRow
  ∷ meditationQiRow
  ∷ []

record QiCarrierFieldBridgeReceipt : Set where
  constructor qiCarrierFieldBridgeReceipt
  field
    interMediaAdapter :
      IM.InterMediaCarrierBridgeReceipt

    interMediaAdapterIsCanonical :
      interMediaAdapter ≡ IM.canonicalInterMediaCarrierBridgeReceipt

    qiDomains :
      List QiDomain

    qiDomainsAreCanonical :
      qiDomains ≡ canonicalQiDomains

    qiRows :
      List QiCarrierFieldRow

    qiRowsAreCanonical :
      qiRows ≡ canonicalQiCarrierFieldRows

    fengShuiRowReceipt :
      QiCarrierFieldRowReceipt fengShuiQiRow

    taiChiRowReceipt :
      QiCarrierFieldRowReceipt taiChiQiRow

    meditationRowReceipt :
      QiCarrierFieldRowReceipt meditationQiRow

    qiTruthAuthorityPromoted :
      Bool

    qiTruthAuthorityPromotedIsFalse :
      qiTruthAuthorityPromoted ≡ false

    qiClinicalAuthorityPromoted :
      Bool

    qiClinicalAuthorityPromotedIsFalse :
      qiClinicalAuthorityPromoted ≡ false

    qiMetaphysicalAuthorityPromoted :
      Bool

    qiMetaphysicalAuthorityPromotedIsFalse :
      qiMetaphysicalAuthorityPromoted ≡ false

    qiPromotions :
      List QiCarrierFieldPromotion

    qiPromotionsEmpty :
      qiPromotions ≡ []

    qiPromotionImpossible :
      QiCarrierFieldPromotion →
      ⊥

open QiCarrierFieldBridgeReceipt public

canonicalQiCarrierFieldBridgeReceipt :
  QiCarrierFieldBridgeReceipt
canonicalQiCarrierFieldBridgeReceipt =
  qiCarrierFieldBridgeReceipt
    IM.canonicalInterMediaCarrierBridgeReceipt
    refl
    canonicalQiDomains
    refl
    canonicalQiCarrierFieldRows
    refl
    fengShuiQiRowReceipt
    taiChiQiRowReceipt
    meditationQiRowReceipt
    false
    refl
    false
    refl
    false
    refl
    []
    refl
    qiCarrierFieldPromotionImpossible

canonicalQiInterMediaAdapterCanonical :
  interMediaAdapter canonicalQiCarrierFieldBridgeReceipt
  ≡
  IM.canonicalInterMediaCarrierBridgeReceipt
canonicalQiInterMediaAdapterCanonical =
  refl

canonicalMeditationQiTruthFalse :
  qiTruthAuthority meditationQiRow ≡ false
canonicalMeditationQiTruthFalse =
  refl

canonicalQiClinicalAuthorityFalse :
  qiClinicalAuthorityPromoted canonicalQiCarrierFieldBridgeReceipt ≡ false
canonicalQiClinicalAuthorityFalse =
  refl
