module DASHI.Interop.InterMediaBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.InterMediaCarrierBridge as IM
import DASHI.Interop.MeditationQiBridge as Med
import DASHI.Interop.QiCarrierFieldBridge as Qi

------------------------------------------------------------------------
-- Focused aggregation checks for the inter-media bridge tranche.

interMediaTruthAuthorityFalse :
  IM.truthAuthorityPromoted IM.canonicalInterMediaCarrierBridgeReceipt
  ≡
  false
interMediaTruthAuthorityFalse =
  refl

interMediaClinicalAuthorityFalse :
  IM.clinicalAuthorityPromoted IM.canonicalInterMediaCarrierBridgeReceipt
  ≡
  false
interMediaClinicalAuthorityFalse =
  refl

qiTruthAuthorityFalse :
  Qi.qiTruthAuthorityPromoted Qi.canonicalQiCarrierFieldBridgeReceipt
  ≡
  false
qiTruthAuthorityFalse =
  refl

qiClinicalAuthorityFalse :
  Qi.qiClinicalAuthorityPromoted Qi.canonicalQiCarrierFieldBridgeReceipt
  ≡
  false
qiClinicalAuthorityFalse =
  refl

meditationClinicalAuthorityFalse :
  Med.clinicalAuthorityPromoted Med.canonicalMeditationQiBridgeReceipt
  ≡
  false
meditationClinicalAuthorityFalse =
  refl

meditationTruthAuthorityFalse :
  Med.truthAuthorityPromoted Med.canonicalMeditationQiBridgeReceipt
  ≡
  false
meditationTruthAuthorityFalse =
  refl

meditationFullAdmissionFalse :
  Med.fullAdmission
    (Med.sweetgrassGate Med.canonicalMeditationQiBridgeReceipt)
  ≡
  false
meditationFullAdmissionFalse =
  refl
