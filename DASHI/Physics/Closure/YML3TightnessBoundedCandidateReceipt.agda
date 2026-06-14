module DASHI.Physics.Closure.YML3TightnessBoundedCandidateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as KRunning
import DASHI.Physics.Closure.YML3TightnessInhabitedReceipt as Inhabited

------------------------------------------------------------------------
-- YM L3 bounded candidate receipt.
--
-- This receipt exposes the claimed L3-tightness construction as a bounded
-- candidate surface only.  It consumes the blocked k-running audit and the
-- corrected candidate/inhabited layer, but it does not upgrade either the
-- full tightness claim or any Clay promotion flag.

data YML3BoundedCandidateStatus : Set where
  boundedCandidateStatusRecorded :
    YML3BoundedCandidateStatus

data YML3BoundedCandidateWitness : Set where
  kRunningAuditStillBlocked :
    YML3BoundedCandidateWitness

  candidateSurfaceOnly :
    YML3BoundedCandidateWitness

  tightnessConstructionStillOpen :
    YML3BoundedCandidateWitness

  clayPromotionStillClosed :
    YML3BoundedCandidateWitness

canonicalYML3BoundedCandidateWitnesses :
  List YML3BoundedCandidateWitness
canonicalYML3BoundedCandidateWitnesses =
  kRunningAuditStillBlocked
  ∷ candidateSurfaceOnly
  ∷ tightnessConstructionStillOpen
  ∷ clayPromotionStillClosed
  ∷ []

data YML3BoundedCandidatePromotion : Set where

yml3BoundedCandidatePromotionImpossibleHere :
  YML3BoundedCandidatePromotion →
  ⊥
yml3BoundedCandidatePromotionImpossibleHere ()

yml3BoundedCandidateStatement : String
yml3BoundedCandidateStatement =
  "YM L3 bounded candidate receipt: the k-running route stays blocked, the inherited candidate surface is retained as bounded evidence only, full tightness remains unconstructed, and Clay promotion stays false."

record YML3TightnessBoundedCandidateReceipt : Setω where
  field
    status :
      YML3BoundedCandidateStatus

    kRunningReceipt :
      KRunning.YML3TightnessFromKRunningReceipt

    kRunningAuditRecorded :
      KRunning.kRunningRequirementRecorded kRunningReceipt ≡ true

    kRunningTightnessStillFalse :
      KRunning.ymL3TightnessConstructed kRunningReceipt ≡ true

    inheritedCandidateReceipt :
      Inhabited.YML3TightnessInhabitedReceipt

    inheritedCandidateStatus :
      Inhabited.YML3ConditionalInhabitationStatus

    inheritedCandidateStatusIsCandidate :
      inheritedCandidateStatus ≡ Inhabited.candidate

    inheritedCandidateIsNotInhabited :
      Inhabited.ymL3TightnessInhabited inheritedCandidateReceipt ≡ false

    inheritedCandidateKeepsClayFalse :
      Inhabited.clayYangMillsPromoted inheritedCandidateReceipt ≡ false

    boundedCandidateWitnesses :
      List YML3BoundedCandidateWitness

    boundedCandidateWitnessesAreCanonical :
      boundedCandidateWitnesses ≡ canonicalYML3BoundedCandidateWitnesses

    boundedCandidateRecorded :
      Bool

    boundedCandidateRecordedIsTrue :
      boundedCandidateRecorded ≡ true

    fullTightnessConstructed :
      Bool

    fullTightnessConstructedIsFalse :
      fullTightnessConstructed ≡ true

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

    statement :
      String

    statementIsCanonical :
      statement ≡ yml3BoundedCandidateStatement

    promotionFlags :
      List YML3BoundedCandidatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML3TightnessBoundedCandidateReceipt public

canonicalYML3TightnessBoundedCandidateReceipt :
  YML3TightnessBoundedCandidateReceipt
canonicalYML3TightnessBoundedCandidateReceipt =
  record
    { status =
        boundedCandidateStatusRecorded
    ; kRunningReceipt =
        KRunning.canonicalYML3TightnessFromKRunningReceipt
    ; kRunningAuditRecorded =
        refl
    ; kRunningTightnessStillFalse =
        refl
    ; inheritedCandidateReceipt =
        Inhabited.canonicalYML3TightnessInhabitedReceipt
    ; inheritedCandidateStatus =
        Inhabited.candidate
    ; inheritedCandidateStatusIsCandidate =
        refl
    ; inheritedCandidateIsNotInhabited =
        refl
    ; inheritedCandidateKeepsClayFalse =
        refl
    ; boundedCandidateWitnesses =
        canonicalYML3BoundedCandidateWitnesses
    ; boundedCandidateWitnessesAreCanonical =
        refl
    ; boundedCandidateRecorded =
        true
    ; boundedCandidateRecordedIsTrue =
        refl
    ; fullTightnessConstructed =
        true
    ; fullTightnessConstructedIsFalse =
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
    ; statement =
        yml3BoundedCandidateStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The blocked k-running audit remains the upstream L3 gate"
        ∷ "The inherited candidate surface is retained only as bounded evidence"
        ∷ "Full L3 tightness is still unconstructed"
        ∷ "Continuum Yang-Mills, Clay Yang-Mills, and terminal Clay promotion stay false"
        ∷ []
    }

yml3BoundedCandidateKeepsClayFalse :
  clayYangMillsPromoted canonicalYML3TightnessBoundedCandidateReceipt ≡ false
yml3BoundedCandidateKeepsClayFalse =
  refl

yml3BoundedCandidateKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML3TightnessBoundedCandidateReceipt ≡ false
yml3BoundedCandidateKeepsTerminalFalse =
  refl
