module DASHI.Physics.Closure.CarrierRGTrajectoryYMReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BetaCriticalReceipt as Beta

data CarrierRGTrajectoryIssue : Set where
  alphaOneIsMassRatioBookkeeping :
    CarrierRGTrajectoryIssue

  qcdRunningNeedsSeparateCoupling :
    CarrierRGTrajectoryIssue

  carrierScaleInGeVOpen :
    CarrierRGTrajectoryIssue

  betaToInfinityTrajectoryMissing :
    CarrierRGTrajectoryIssue

canonicalCarrierRGTrajectoryIssues :
  List CarrierRGTrajectoryIssue
canonicalCarrierRGTrajectoryIssues =
  alphaOneIsMassRatioBookkeeping
  ∷ qcdRunningNeedsSeparateCoupling
  ∷ carrierScaleInGeVOpen
  ∷ betaToInfinityTrajectoryMissing
  ∷ []

data CarrierRGTrajectoryOption : Set where
  separateGaugeRunningCoupling :
    CarrierRGTrajectoryOption

  alphaOneAsCarrierScaleBoundaryValue :
    CarrierRGTrajectoryOption

  externalScaleAnchoringRequired :
    CarrierRGTrajectoryOption

canonicalCarrierRGTrajectoryOptions :
  List CarrierRGTrajectoryOption
canonicalCarrierRGTrajectoryOptions =
  separateGaugeRunningCoupling
  ∷ alphaOneAsCarrierScaleBoundaryValue
  ∷ externalScaleAnchoringRequired
  ∷ []

data CarrierRGTrajectoryPromotion : Set where

carrierRGTrajectoryPromotionImpossibleHere :
  CarrierRGTrajectoryPromotion →
  ⊥
carrierRGTrajectoryPromotionImpossibleHere ()

alphaOneFixedLabel : String
alphaOneFixedLabel =
  "alpha1 = sqrt(m_u/m_c) is a fixed DASHI hierarchy parameter, not the running QCD gauge coupling"

qcdRunningLabel : String
qcdRunningLabel =
  "continuum Yang-Mills requires g^2(Lambda) ~ 1/log(Lambda/Lambda_QCD), hence a separate running gauge coupling or scale anchor"

record CarrierRGTrajectoryYMReceipt : Setω where
  field
    betaCriticalReceipt :
      Beta.BetaCriticalReceipt

    carrierBetaProblemRecorded :
      Beta.carrierBetaNotOnRGTrajectory betaCriticalReceipt ≡ true

    betaCriticalKeepsClayFalse :
      Beta.clayYangMillsPromoted betaCriticalReceipt ≡ false

    alphaOneFixedStatement :
      String

    alphaOneFixedStatementIsCanonical :
      alphaOneFixedStatement ≡ alphaOneFixedLabel

    qcdRunningStatement :
      String

    qcdRunningStatementIsCanonical :
      qcdRunningStatement ≡ qcdRunningLabel

    carrierAlpha1Fixed :
      Bool

    carrierAlpha1FixedIsTrue :
      carrierAlpha1Fixed ≡ true

    qcdRunningRequiresSeparateCoupling :
      Bool

    qcdRunningRequiresSeparateCouplingIsTrue :
      qcdRunningRequiresSeparateCoupling ≡ true

    carrierScaleIdentificationOpen :
      Bool

    carrierScaleIdentificationOpenIsTrue :
      carrierScaleIdentificationOpen ≡ true

    carrierRGTrajectoryConstructed :
      Bool

    carrierRGTrajectoryConstructedIsFalse :
      carrierRGTrajectoryConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    issues :
      List CarrierRGTrajectoryIssue

    issuesAreCanonical :
      issues ≡ canonicalCarrierRGTrajectoryIssues

    options :
      List CarrierRGTrajectoryOption

    optionsAreCanonical :
      options ≡ canonicalCarrierRGTrajectoryOptions

    promotionFlags :
      List CarrierRGTrajectoryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open CarrierRGTrajectoryYMReceipt public

canonicalCarrierRGTrajectoryYMReceipt :
  CarrierRGTrajectoryYMReceipt
canonicalCarrierRGTrajectoryYMReceipt =
  record
    { betaCriticalReceipt =
        Beta.canonicalBetaCriticalReceipt
    ; carrierBetaProblemRecorded =
        refl
    ; betaCriticalKeepsClayFalse =
        refl
    ; alphaOneFixedStatement =
        alphaOneFixedLabel
    ; alphaOneFixedStatementIsCanonical =
        refl
    ; qcdRunningStatement =
        qcdRunningLabel
    ; qcdRunningStatementIsCanonical =
        refl
    ; carrierAlpha1Fixed =
        true
    ; carrierAlpha1FixedIsTrue =
        refl
    ; qcdRunningRequiresSeparateCoupling =
        true
    ; qcdRunningRequiresSeparateCouplingIsTrue =
        refl
    ; carrierScaleIdentificationOpen =
        true
    ; carrierScaleIdentificationOpenIsTrue =
        refl
    ; carrierRGTrajectoryConstructed =
        false
    ; carrierRGTrajectoryConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; issues =
        canonicalCarrierRGTrajectoryIssues
    ; issuesAreCanonical =
        refl
    ; options =
        canonicalCarrierRGTrajectoryOptions
    ; optionsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

carrierRGTrajectoryYMKeepsClayFalse :
  clayYangMillsPromoted canonicalCarrierRGTrajectoryYMReceipt ≡ false
carrierRGTrajectoryYMKeepsClayFalse =
  refl
