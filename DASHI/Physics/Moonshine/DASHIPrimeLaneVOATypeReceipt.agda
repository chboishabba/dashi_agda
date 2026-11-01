module DASHI.Physics.Moonshine.DASHIPrimeLaneVOATypeReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Moonshine.PrimeLaneVOAEquivalenceReceiptSurface as Equiv

------------------------------------------------------------------------
-- DASHI prime-lane VOA type receipt.
--
-- This is a receipt surface for the Paper 2 P2-A lane.  It records the
-- intended G2 + G4 bridge shape:
--
--   G2 + G4 inputs make each tracked Monster prime lane a VOA-typed target
--   with central charge 24 and no half-weight states.
--
-- Zhu genus-zero is represented as external authority, while G2genus0 is the
-- explicit bridge obligation that the DASHI genus-zero statement matches the
-- Zhu genus-zero statement.  This module is deliberately non-terminal: it is a
-- candidate receipt that helps close DASHIPrimeLaneEquiv, but it does not flip
-- Clay, terminal, Moonshine, or closure promotion flags.

data DASHIPrimeLaneVOATypeStatus : Set where
  candidateReceiptHelpsCloseDASHIPrimeLaneEquivNoTerminalPromotion :
    DASHIPrimeLaneVOATypeStatus

data DASHIPrimeLaneVOATypePromotionAuthorityToken : Set where

data G2PrimeLaneVOAInput : Lane.MonsterPrimeLane → Set where
  g2PrimeLaneVOAInputCandidate :
    (p : Lane.MonsterPrimeLane) →
    G2PrimeLaneVOAInput p

data G4PrimeLaneIndependenceInput : Lane.MonsterPrimeLane → Set where
  g4PrimeLaneIndependenceInputCandidate :
    (p : Lane.MonsterPrimeLane) →
    G4PrimeLaneIndependenceInput p

data ZhuGenusZeroAuthorityCitation : Set where
  zhuModularInvarianceGenusZeroCitation :
    ZhuGenusZeroAuthorityCitation

record ZhuGenusZeroAuthorityReceipt : Set where
  field
    citation :
      ZhuGenusZeroAuthorityCitation

    authorityLabel :
      String

    acceptedAsExternalAuthority :
      Bool

    acceptedAsExternalAuthorityIsTrue :
      acceptedAsExternalAuthority ≡ true

open ZhuGenusZeroAuthorityReceipt public

postulate
  zhuGenusZeroAuthority :
    ZhuGenusZeroAuthorityReceipt

data PrimeLaneVOABridgeObligation : Set where
  G2genus0 :
    PrimeLaneVOABridgeObligation

  G2primeLaneVOACompatibility :
    PrimeLaneVOABridgeObligation

  G4primeLaneIndependenceCompatibility :
    PrimeLaneVOABridgeObligation

  ZhuGenusZeroAuthorityBinding :
    PrimeLaneVOABridgeObligation

  noHalfWeightStateCompatibility :
    PrimeLaneVOABridgeObligation

canonicalPrimeLaneVOABridgeObligations :
  List PrimeLaneVOABridgeObligation
canonicalPrimeLaneVOABridgeObligations =
  G2genus0
  ∷ G2primeLaneVOACompatibility
  ∷ G4primeLaneIndependenceCompatibility
  ∷ ZhuGenusZeroAuthorityBinding
  ∷ noHalfWeightStateCompatibility
  ∷ []

record PrimeLaneVOAType (p : Lane.MonsterPrimeLane) : Setω where
  field
    lane :
      Lane.MonsterPrimeLane

    laneIsInput :
      lane ≡ p

    primeValue :
      Nat

    primeValueIsLaneValue :
      primeValue ≡ Lane.monsterPrimeLaneToNat p

    centralCharge :
      Nat

    centralChargeIs24 :
      centralCharge ≡ 24

    halfWeightStateCount :
      Nat

    halfWeightStateCountIs0 :
      halfWeightStateCount ≡ 0

    noHalfWeightStates :
      Bool

    noHalfWeightStatesIsTrue :
      noHalfWeightStates ≡ true

    isVOATyped :
      Bool

    isVOATypedIsTrue :
      isVOATyped ≡ true

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    provedTheorem :
      Bool

    provedTheoremIsFalse :
      provedTheorem ≡ false

open PrimeLaneVOAType public

primeLaneIsVOA :
  (p : Lane.MonsterPrimeLane) →
  G2PrimeLaneVOAInput p →
  G4PrimeLaneIndependenceInput p →
  PrimeLaneVOAType p
primeLaneIsVOA p _ _ =
  record
    { lane =
        p
    ; laneIsInput =
        refl
    ; primeValue =
        Lane.monsterPrimeLaneToNat p
    ; primeValueIsLaneValue =
        refl
    ; centralCharge =
        24
    ; centralChargeIs24 =
        refl
    ; halfWeightStateCount =
        0
    ; halfWeightStateCountIs0 =
        refl
    ; noHalfWeightStates =
        true
    ; noHalfWeightStatesIsTrue =
        refl
    ; isVOATyped =
        true
    ; isVOATypedIsTrue =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; provedTheorem =
        false
    ; provedTheoremIsFalse =
        refl
    }

canonicalPrimeLaneVOAType :
  (p : Lane.MonsterPrimeLane) →
  PrimeLaneVOAType p
canonicalPrimeLaneVOAType p =
  primeLaneIsVOA
    p
    (g2PrimeLaneVOAInputCandidate p)
    (g4PrimeLaneIndependenceInputCandidate p)

record DASHIPrimeLaneVOATypeReceipt : Setω where
  field
    status :
      DASHIPrimeLaneVOATypeStatus

    sourcePrimeLaneReceipt :
      Lane.MoonshinePrimeLaneReceiptSurface

    targetEquivReceipt :
      Equiv.DASHIPrimeLaneEquivReceiptSurface

    trackedPrimeLane :
      List Lane.MonsterPrimeLane

    trackedPrimeLaneIsCanonical :
      trackedPrimeLane ≡ Lane.canonicalMonsterPrimeLane

    g2InputAt :
      (p : Lane.MonsterPrimeLane) →
      G2PrimeLaneVOAInput p

    g4InputAt :
      (p : Lane.MonsterPrimeLane) →
      G4PrimeLaneIndependenceInput p

    voaTypeAt :
      (p : Lane.MonsterPrimeLane) →
      PrimeLaneVOAType p

    zhuAuthority :
      ZhuGenusZeroAuthorityReceipt

    bridgeObligations :
      List PrimeLaneVOABridgeObligation

    bridgeObligationsAreCanonical :
      bridgeObligations ≡ canonicalPrimeLaneVOABridgeObligations

    G2genus0BridgeObligationPresent :
      Bool

    G2genus0BridgeObligationPresentIsTrue :
      G2genus0BridgeObligationPresent ≡ true

    dashiGenusZeroMatchesZhuGenusZeroCandidate :
      Bool

    dashiGenusZeroMatchesZhuGenusZeroCandidateIsTrue :
      dashiGenusZeroMatchesZhuGenusZeroCandidate ≡ true

    dashiGenusZeroMatchesZhuGenusZeroProved :
      Bool

    dashiGenusZeroMatchesZhuGenusZeroProvedIsFalse :
      dashiGenusZeroMatchesZhuGenusZeroProved ≡ false

    helpsCloseDASHIPrimeLaneEquiv :
      Bool

    helpsCloseDASHIPrimeLaneEquivIsTrue :
      helpsCloseDASHIPrimeLaneEquiv ≡ true

    receiptCandidate :
      Bool

    receiptCandidateIsTrue :
      receiptCandidate ≡ true

    receiptProved :
      Bool

    receiptProvedIsFalse :
      receiptProved ≡ false

    clayPromotionFlipped :
      Bool

    clayPromotionFlippedIsFalse :
      clayPromotionFlipped ≡ false

    terminalPromotionFlipped :
      Bool

    terminalPromotionFlippedIsFalse :
      terminalPromotionFlipped ≡ false

    closurePromotionFromThisReceipt :
      Bool

    closurePromotionFromThisReceiptIsFalse :
      closurePromotionFromThisReceipt ≡ false

    noPromotionWithoutAuthority :
      DASHIPrimeLaneVOATypePromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open DASHIPrimeLaneVOATypeReceipt public

canonicalDASHIPrimeLaneVOATypeReceipt :
  DASHIPrimeLaneVOATypeReceipt
canonicalDASHIPrimeLaneVOATypeReceipt =
  record
    { status =
        candidateReceiptHelpsCloseDASHIPrimeLaneEquivNoTerminalPromotion
    ; sourcePrimeLaneReceipt =
        Lane.canonicalMoonshinePrimeLaneReceiptSurface
    ; targetEquivReceipt =
        Equiv.canonicalDASHIPrimeLaneEquivReceiptSurface
    ; trackedPrimeLane =
        Lane.canonicalMonsterPrimeLane
    ; trackedPrimeLaneIsCanonical =
        refl
    ; g2InputAt =
        g2PrimeLaneVOAInputCandidate
    ; g4InputAt =
        g4PrimeLaneIndependenceInputCandidate
    ; voaTypeAt =
        canonicalPrimeLaneVOAType
    ; zhuAuthority =
        zhuGenusZeroAuthority
    ; bridgeObligations =
        canonicalPrimeLaneVOABridgeObligations
    ; bridgeObligationsAreCanonical =
        refl
    ; G2genus0BridgeObligationPresent =
        true
    ; G2genus0BridgeObligationPresentIsTrue =
        refl
    ; dashiGenusZeroMatchesZhuGenusZeroCandidate =
        true
    ; dashiGenusZeroMatchesZhuGenusZeroCandidateIsTrue =
        refl
    ; dashiGenusZeroMatchesZhuGenusZeroProved =
        false
    ; dashiGenusZeroMatchesZhuGenusZeroProvedIsFalse =
        refl
    ; helpsCloseDASHIPrimeLaneEquiv =
        true
    ; helpsCloseDASHIPrimeLaneEquivIsTrue =
        refl
    ; receiptCandidate =
        true
    ; receiptCandidateIsTrue =
        refl
    ; receiptProved =
        false
    ; receiptProvedIsFalse =
        refl
    ; clayPromotionFlipped =
        false
    ; clayPromotionFlippedIsFalse =
        refl
    ; terminalPromotionFlipped =
        false
    ; terminalPromotionFlippedIsFalse =
        refl
    ; closurePromotionFromThisReceipt =
        false
    ; closurePromotionFromThisReceiptIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "P2-A records a candidate G2 + G4 -> prime-lane VOA type surface"
        ∷ "Each tracked Monster prime lane is typed as a VOA target with central charge 24 and zero half-weight states"
        ∷ "Zhu genus-zero is accepted only as an external authority receipt"
        ∷ "G2genus0 is the required bridge obligation that DASHI genus-zero matches Zhu genus-zero"
        ∷ "The surface is intended to help close DASHIPrimeLaneEquiv but does not prove that equivalence"
        ∷ "Candidate flags are true; proved, Clay, terminal, and closure-promotion flags remain false"
        ∷ []
    }
