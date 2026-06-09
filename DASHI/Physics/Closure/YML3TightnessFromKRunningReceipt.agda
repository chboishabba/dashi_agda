module DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML2CorrectedStatusReceipt as L2C

------------------------------------------------------------------------
-- YM L3 tightness audit for k-running proposals.

data YML3TightnessFromKRunningStatus : Set where
  tightnessFromKRunningAuditedButBlocked :
    YML3TightnessFromKRunningStatus

data YML3TightnessRequirement : Set where
  scaleDependentKRunning :
    YML3TightnessRequirement

  wilsonBetaRunningTrajectory :
    YML3TightnessRequirement

  uniformMeasureBoundsInDepth :
    YML3TightnessRequirement

  prokhorovTightnessCriterion :
    YML3TightnessRequirement

  continuumWilsonMeasureLimit :
    YML3TightnessRequirement

canonicalYML3TightnessRequirements :
  List YML3TightnessRequirement
canonicalYML3TightnessRequirements =
  scaleDependentKRunning
  ∷ wilsonBetaRunningTrajectory
  ∷ uniformMeasureBoundsInDepth
  ∷ prokhorovTightnessCriterion
  ∷ continuumWilsonMeasureLimit
  ∷ []

data YML3TightnessPromotion : Set where

yml3TightnessPromotionImpossibleHere :
  YML3TightnessPromotion →
  ⊥
yml3TightnessPromotionImpossibleHere ()

yml3TightnessStatement : String
yml3TightnessStatement =
  "YML3 tightness cannot be promoted from fixed CS-level k bookkeeping: k-running, Wilson beta running, uniform depth bounds, and a continuum Wilson measure limit remain open."

record YML3TightnessFromKRunningReceipt : Setω where
  field
    status :
      YML3TightnessFromKRunningStatus

    correctedL2Receipt :
      L2C.YML2CorrectedStatusReceipt

    correctedL2KeepsTightnessFalse :
      L2C.correctedYML3TightnessConstructed correctedL2Receipt ≡ false

    kRunningRequirementRecorded :
      Bool

    kRunningRequirementRecordedIsTrue :
      kRunningRequirementRecorded ≡ true

    scaleDependentKRunningConstructed :
      Bool

    scaleDependentKRunningConstructedIsFalse :
      scaleDependentKRunningConstructed ≡ false

    wilsonBetaRunningTrajectoryConstructed :
      Bool

    wilsonBetaRunningTrajectoryConstructedIsFalse :
      wilsonBetaRunningTrajectoryConstructed ≡ false

    uniformDepthBoundsConstructed :
      Bool

    uniformDepthBoundsConstructedIsFalse :
      uniformDepthBoundsConstructed ≡ false

    prokhorovTightnessConstructed :
      Bool

    prokhorovTightnessConstructedIsFalse :
      prokhorovTightnessConstructed ≡ false

    continuumWilsonMeasureConstructed :
      Bool

    continuumWilsonMeasureConstructedIsFalse :
      continuumWilsonMeasureConstructed ≡ false

    ymL3TightnessConstructed :
      Bool

    ymL3TightnessConstructedIsFalse :
      ymL3TightnessConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    requirements :
      List YML3TightnessRequirement

    requirementsAreCanonical :
      requirements ≡ canonicalYML3TightnessRequirements

    statement :
      String

    statementIsCanonical :
      statement ≡ yml3TightnessStatement

    promotionFlags :
      List YML3TightnessPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML3TightnessFromKRunningReceipt public

canonicalYML3TightnessFromKRunningReceipt :
  YML3TightnessFromKRunningReceipt
canonicalYML3TightnessFromKRunningReceipt =
  record
    { status =
        tightnessFromKRunningAuditedButBlocked
    ; correctedL2Receipt =
        L2C.canonicalYML2CorrectedStatusReceipt
    ; correctedL2KeepsTightnessFalse =
        refl
    ; kRunningRequirementRecorded =
        true
    ; kRunningRequirementRecordedIsTrue =
        refl
    ; scaleDependentKRunningConstructed =
        false
    ; scaleDependentKRunningConstructedIsFalse =
        refl
    ; wilsonBetaRunningTrajectoryConstructed =
        false
    ; wilsonBetaRunningTrajectoryConstructedIsFalse =
        refl
    ; uniformDepthBoundsConstructed =
        false
    ; uniformDepthBoundsConstructedIsFalse =
        refl
    ; prokhorovTightnessConstructed =
        false
    ; prokhorovTightnessConstructedIsFalse =
        refl
    ; continuumWilsonMeasureConstructed =
        false
    ; continuumWilsonMeasureConstructedIsFalse =
        refl
    ; ymL3TightnessConstructed =
        false
    ; ymL3TightnessConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
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
    ; requirements =
        canonicalYML3TightnessRequirements
    ; requirementsAreCanonical =
        refl
    ; statement =
        yml3TightnessStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The k-running proposal is recorded only as a candidate audit target"
        ∷ "No Wilson beta-running trajectory is constructed from k-running"
        ∷ "No cutoff-measure tightness or continuum compactness theorem is proved"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

yml3TightnessFromKRunningKeepsClayFalse :
  clayYangMillsPromoted canonicalYML3TightnessFromKRunningReceipt ≡ false
yml3TightnessFromKRunningKeepsClayFalse =
  refl

yml3TightnessFromKRunningKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML3TightnessFromKRunningReceipt ≡ false
yml3TightnessFromKRunningKeepsTerminalFalse =
  refl
