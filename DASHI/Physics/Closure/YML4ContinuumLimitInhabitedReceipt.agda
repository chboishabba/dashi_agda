module DASHI.Physics.Closure.YML4ContinuumLimitInhabitedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3
import DASHI.Physics.Closure.YML4ContinuumLimitReceipt as L4

------------------------------------------------------------------------
-- YM L4 continuum-limit dependency receipt.
--
-- This receipt no longer promotes an inhabited L4 package.  It records the
-- L4 target as conditional on L3 while explicitly consuming the corrected L3
-- receipt, which marks tightness uninhabited.

data YML4ContinuumLimitInhabitationStatus : Set where
  conditionalOnL3 :
    YML4ContinuumLimitInhabitationStatus

data YML4LimitMeasureUniqueness : Set where
  candidateBalabanWeakCouplingUniqueness :
    YML4LimitMeasureUniqueness

data YML4ContinuumLimitInhabitedStep : Set where
  consumeL3ConditionalTightness :
    YML4ContinuumLimitInhabitedStep

  applyProkhorovToWilsonMeasureFamily :
    YML4ContinuumLimitInhabitedStep

  selectCandidateWeakLimitMeasure :
    YML4ContinuumLimitInhabitedStep

  recordBalabanWeakCouplingUniqueness :
    YML4ContinuumLimitInhabitedStep

  retainNoClayOrTerminalPromotion :
    YML4ContinuumLimitInhabitedStep

canonicalYML4ContinuumLimitInhabitedSteps :
  List YML4ContinuumLimitInhabitedStep
canonicalYML4ContinuumLimitInhabitedSteps =
  consumeL3ConditionalTightness
  ∷ applyProkhorovToWilsonMeasureFamily
  ∷ selectCandidateWeakLimitMeasure
  ∷ recordBalabanWeakCouplingUniqueness
  ∷ retainNoClayOrTerminalPromotion
  ∷ []

data YML4ContinuumLimitInhabitedPromotion : Set where

yml4ContinuumLimitInhabitedPromotionImpossibleHere :
  YML4ContinuumLimitInhabitedPromotion →
  ⊥
yml4ContinuumLimitInhabitedPromotionImpossibleHere ()

limitMeasureUniqueLabel : String
limitMeasureUniqueLabel =
  "candidate/Balaban weak-coupling uniqueness"

yml4ContinuumLimitInhabitedStatement : String
yml4ContinuumLimitInhabitedStatement =
  "YML4 continuum-limit target is recorded conditional on an L3 tightness input; the local L3 receipt still marks tightness uninhabited, so this is a dependency receipt, not a completed L4 proof."

record YML4ContinuumLimitInhabitedReceipt : Setω where
  field
    l3Receipt :
      L3.YML3TightnessFromKRunningReceipt

    l3CurrentlyUninhabited :
      L3.ymL3TightnessConstructed l3Receipt
        ≡ false

    l3KeepsClayFalse :
      L3.clayYangMillsPromoted l3Receipt ≡ false

    l3KeepsTerminalFalse :
      L3.terminalClayClaimPromoted l3Receipt ≡ false

    l4ContinuumLimitReceipt :
      L4.YML4ContinuumLimitReceipt

    l4ProkhorovProofComplete :
      L4.prokhorovTightnessProofComplete l4ContinuumLimitReceipt
        ≡ true

    l4CandidateWeakLimitConstructed :
      L4.candidateWeakLimitConstructed l4ContinuumLimitReceipt ≡ true

    l4WeakLimitUniquenessProved :
      L4.weakLimitUniquenessProved l4ContinuumLimitReceipt ≡ true

    l4KeepsClayFalse :
      L4.clayYangMillsPromoted l4ContinuumLimitReceipt ≡ false

    l4KeepsTerminalFalse :
      L4.terminalClayClaimPromoted l4ContinuumLimitReceipt ≡ false

    ymL4ContinuumLimitInhabited :
      YML4ContinuumLimitInhabitationStatus

    ymL4ContinuumLimitInhabitedIsConditionalOnL3 :
      ymL4ContinuumLimitInhabited ≡ conditionalOnL3

    conditionalOnL3Tightness :
      Bool

    conditionalOnL3TightnessIsTrue :
      conditionalOnL3Tightness ≡ true

    prokhorovApplied :
      Bool

    prokhorovAppliedIsTrue :
      prokhorovApplied ≡ true

    limitMeasureUnique :
      YML4LimitMeasureUniqueness

    limitMeasureUniqueIsCandidateBalabanWeakCoupling :
      limitMeasureUnique ≡ candidateBalabanWeakCouplingUniqueness

    limitMeasureUniqueStatement :
      String

    limitMeasureUniqueStatementIsCanonical :
      limitMeasureUniqueStatement ≡ limitMeasureUniqueLabel

    candidateWeakLimitMeasureRecorded :
      Bool

    candidateWeakLimitMeasureRecordedIsTrue :
      candidateWeakLimitMeasureRecorded ≡ true

    unconditionalContinuumYMPromoted :
      Bool

    unconditionalContinuumYMPromotedIsFalse :
      unconditionalContinuumYMPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    steps :
      List YML4ContinuumLimitInhabitedStep

    stepsAreCanonical :
      steps ≡ canonicalYML4ContinuumLimitInhabitedSteps

    statement :
      String

    statementIsCanonical :
      statement ≡ yml4ContinuumLimitInhabitedStatement

    promotionFlags :
      List YML4ContinuumLimitInhabitedPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML4ContinuumLimitInhabitedReceipt public

canonicalYML4ContinuumLimitInhabitedReceipt :
  YML4ContinuumLimitInhabitedReceipt
canonicalYML4ContinuumLimitInhabitedReceipt =
  record
    { l3Receipt =
        L3.canonicalYML3TightnessFromKRunningReceipt
    ; l3CurrentlyUninhabited =
        refl
    ; l3KeepsClayFalse =
        refl
    ; l3KeepsTerminalFalse =
        refl
    ; l4ContinuumLimitReceipt =
        L4.canonicalYML4ContinuumLimitReceipt
    ; l4ProkhorovProofComplete =
        refl
    ; l4CandidateWeakLimitConstructed =
        refl
    ; l4WeakLimitUniquenessProved =
        refl
    ; l4KeepsClayFalse =
        refl
    ; l4KeepsTerminalFalse =
        refl
    ; ymL4ContinuumLimitInhabited =
        conditionalOnL3
    ; ymL4ContinuumLimitInhabitedIsConditionalOnL3 =
        refl
    ; conditionalOnL3Tightness =
        true
    ; conditionalOnL3TightnessIsTrue =
        refl
    ; prokhorovApplied =
        true
    ; prokhorovAppliedIsTrue =
        refl
    ; limitMeasureUnique =
        candidateBalabanWeakCouplingUniqueness
    ; limitMeasureUniqueIsCandidateBalabanWeakCoupling =
        refl
    ; limitMeasureUniqueStatement =
        limitMeasureUniqueLabel
    ; limitMeasureUniqueStatementIsCanonical =
        refl
    ; candidateWeakLimitMeasureRecorded =
        true
    ; candidateWeakLimitMeasureRecordedIsTrue =
        refl
    ; unconditionalContinuumYMPromoted =
        false
    ; unconditionalContinuumYMPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; steps =
        canonicalYML4ContinuumLimitInhabitedSteps
    ; stepsAreCanonical =
        refl
    ; statement =
        yml4ContinuumLimitInhabitedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "ymL4ContinuumLimitInhabited is conditionalOnL3 as a target dependency"
        ∷ "The local L3 receipt still marks tightness uninhabited; Prokhorov is not promoted unconditionally"
        ∷ "The limit measure uniqueness record is candidate/Balaban weak-coupling uniqueness"
        ∷ "No unconditional continuum YM, Clay YM, or terminal Clay promotion follows"
        ∷ []
    }

yml4ContinuumLimitInhabitedIsConditionalOnL3 :
  ymL4ContinuumLimitInhabited
    canonicalYML4ContinuumLimitInhabitedReceipt
  ≡ conditionalOnL3
yml4ContinuumLimitInhabitedIsConditionalOnL3 =
  refl

yml4ContinuumLimitInhabitedProkhorovApplied :
  prokhorovApplied canonicalYML4ContinuumLimitInhabitedReceipt
  ≡ true
yml4ContinuumLimitInhabitedProkhorovApplied =
  refl

yml4ContinuumLimitInhabitedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML4ContinuumLimitInhabitedReceipt
  ≡ false
yml4ContinuumLimitInhabitedKeepsClayFalse =
  refl

yml4ContinuumLimitInhabitedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML4ContinuumLimitInhabitedReceipt
  ≡ false
yml4ContinuumLimitInhabitedKeepsTerminalFalse =
  refl
