module DASHI.Physics.Moonshine.MonsterOrderDepthBoundReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.CarrierYukawaRatioTargetReceipt as Ratios
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Monster order depth-bound receipt.
--
-- This module records the external Monster-order exponent table as a
-- conjectural depth-bound surface for the tracked Moonshine prime lanes.
-- It is deliberately fail-closed: the bound is marked conjectured, not
-- proved; the prime set is not forced from first principles; and no
-- promotion token is inhabited.

data MonsterOrderDepthBoundStatus : Set where
  conjecturalDepthBoundReceiptNoFirstPrinciplesPromotion :
    MonsterOrderDepthBoundStatus

data MonsterOrderDepthBoundCitation : Set where
  atlasMonsterOrderCitation :
    MonsterOrderDepthBoundCitation

  conwayNortonMonstrousMoonshineCitation :
    MonsterOrderDepthBoundCitation

data MonsterOrderDepthBoundBoundary : Set where
  boundaryMonsterOrderExponentTableExternal :
    MonsterOrderDepthBoundBoundary

  boundaryDepthBoundConjecturalOnly :
    MonsterOrderDepthBoundBoundary

  boundaryDepthBoundNotProved :
    MonsterOrderDepthBoundBoundary

  boundaryPrimeSetNotForcedFromFirstPrinciples :
    MonsterOrderDepthBoundBoundary

  boundaryNoClosurePromotion :
    MonsterOrderDepthBoundBoundary

  boundaryNoTerminalPromotion :
    MonsterOrderDepthBoundBoundary

canonicalMonsterOrderDepthBoundBoundaries :
  List MonsterOrderDepthBoundBoundary
canonicalMonsterOrderDepthBoundBoundaries =
  boundaryMonsterOrderExponentTableExternal
  ∷ boundaryDepthBoundConjecturalOnly
  ∷ boundaryDepthBoundNotProved
  ∷ boundaryPrimeSetNotForcedFromFirstPrinciples
  ∷ boundaryNoClosurePromotion
  ∷ boundaryNoTerminalPromotion
  ∷ []

data MonsterOrderDepthBoundPromotionAuthorityToken : Set where

monsterOrderCitationAuthority :
  Authority.CitationAuthorityBoundary
monsterOrderCitationAuthority =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Monster group order prime-exponent table"
    "Atlas/Conway-Norton Monster order and monstrous moonshine authority for the prime-exponent table"
    true
    false
    false
    ( "CitationAuthority only: no machine-readable depth-bound artifact is claimed"
      ∷ "The exponent table is used as a conjectural carrier-depth target, not as a proof"
      ∷ []
    )

monsterOrderCitationNoArtifact :
  Authority.CitationAuthorityNoArtifact
monsterOrderCitationNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    monsterOrderCitationAuthority
    refl
    refl
    refl

monsterOrderDepthExponent :
  Lane.MonsterPrimeLane →
  Nat
monsterOrderDepthExponent Lane.p2 =
  46
monsterOrderDepthExponent Lane.p3 =
  20
monsterOrderDepthExponent Lane.p5 =
  9
monsterOrderDepthExponent Lane.p7 =
  6
monsterOrderDepthExponent Lane.p11 =
  2
monsterOrderDepthExponent Lane.p13 =
  2
monsterOrderDepthExponent Lane.p17 =
  2
monsterOrderDepthExponent Lane.p19 =
  2
monsterOrderDepthExponent Lane.p23 =
  2
monsterOrderDepthExponent Lane.p29 =
  1
monsterOrderDepthExponent Lane.p31 =
  1
monsterOrderDepthExponent Lane.p41 =
  1
monsterOrderDepthExponent Lane.p47 =
  1
monsterOrderDepthExponent Lane.p59 =
  1
monsterOrderDepthExponent Lane.p71 =
  1

monsterOrderDepthExponentVector15 :
  List Nat
monsterOrderDepthExponentVector15 =
  46
  ∷ 20
  ∷ 9
  ∷ 6
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 2
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ []

monsterOrderGlobalDepthBound :
  Nat
monsterOrderGlobalDepthBound =
  46

currentCarrierDepthReadback :
  Lane.MonsterPrimeLane →
  Nat
currentCarrierDepthReadback Lane.p2 =
  Ratios.p2Depth Ratios.canonicalPrimeLaneDepthSeparationReceipt
currentCarrierDepthReadback Lane.p3 =
  Ratios.p3Depth Ratios.canonicalPrimeLaneDepthSeparationReceipt
currentCarrierDepthReadback Lane.p5 =
  Ratios.p5Depth Ratios.canonicalPrimeLaneDepthSeparationReceipt
currentCarrierDepthReadback Lane.p7 =
  1
currentCarrierDepthReadback Lane.p11 =
  1
currentCarrierDepthReadback Lane.p13 =
  1
currentCarrierDepthReadback Lane.p17 =
  1
currentCarrierDepthReadback Lane.p19 =
  1
currentCarrierDepthReadback Lane.p23 =
  1
currentCarrierDepthReadback Lane.p29 =
  1
currentCarrierDepthReadback Lane.p31 =
  1
currentCarrierDepthReadback Lane.p41 =
  1
currentCarrierDepthReadback Lane.p47 =
  1
currentCarrierDepthReadback Lane.p59 =
  1
currentCarrierDepthReadback Lane.p71 =
  1

currentCarrierDepthReadbackVector15 :
  List Nat
currentCarrierDepthReadbackVector15 =
  1
  ∷ 2
  ∷ 3
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ 1
  ∷ []

currentCarrierDepthRespectsMonsterOrderBound :
  Lane.MonsterPrimeLane →
  Bool
currentCarrierDepthRespectsMonsterOrderBound Lane.p2 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p3 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p5 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p7 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p11 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p13 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p17 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p19 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p23 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p29 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p31 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p41 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p47 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p59 =
  true
currentCarrierDepthRespectsMonsterOrderBound Lane.p71 =
  true

currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt :
  (p : Lane.MonsterPrimeLane) →
  currentCarrierDepthRespectsMonsterOrderBound p ≡ true
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p2 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p3 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p5 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p7 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p11 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p13 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p17 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p19 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p23 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p29 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p31 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p41 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p47 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p59 =
  refl
currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt Lane.p71 =
  refl

record MonsterOrderLaneDepthBound
  (p : Lane.MonsterPrimeLane) : Set where
  field
    lane :
      Lane.MonsterPrimeLane

    laneIsInput :
      lane ≡ p

    primeValue :
      Nat

    primeValueIsLaneValue :
      primeValue ≡ Lane.monsterPrimeLaneToNat p

    depthExponent :
      Nat

    depthExponentIsMonsterOrderExponent :
      depthExponent ≡ monsterOrderDepthExponent p

    globalDepthBound :
      Nat

    globalDepthBoundIs46 :
      globalDepthBound ≡ monsterOrderGlobalDepthBound

    currentCarrierDepth :
      Nat

    currentCarrierDepthIsReadback :
      currentCarrierDepth ≡ currentCarrierDepthReadback p

    currentCarrierDepthRespectsBound :
      Bool

    currentCarrierDepthRespectsBoundIsTrue :
      currentCarrierDepthRespectsBound ≡ true

    depthBoundConjectured :
      Bool

    depthBoundConjecturedIsTrue :
      depthBoundConjectured ≡ true

    depthBoundProved :
      Bool

    depthBoundProvedIsFalse :
      depthBoundProved ≡ false

open MonsterOrderLaneDepthBound public

canonicalMonsterOrderLaneDepthBound :
  (p : Lane.MonsterPrimeLane) →
  MonsterOrderLaneDepthBound p
canonicalMonsterOrderLaneDepthBound p =
  record
    { lane =
        p
    ; laneIsInput =
        refl
    ; primeValue =
        Lane.monsterPrimeLaneToNat p
    ; primeValueIsLaneValue =
        refl
    ; depthExponent =
        monsterOrderDepthExponent p
    ; depthExponentIsMonsterOrderExponent =
        refl
    ; globalDepthBound =
        monsterOrderGlobalDepthBound
    ; globalDepthBoundIs46 =
        refl
    ; currentCarrierDepth =
        currentCarrierDepthReadback p
    ; currentCarrierDepthIsReadback =
        refl
    ; currentCarrierDepthRespectsBound =
        currentCarrierDepthRespectsMonsterOrderBound p
    ; currentCarrierDepthRespectsBoundIsTrue =
        currentCarrierDepthRespectsMonsterOrderBoundIsTrueAt p
    ; depthBoundConjectured =
        true
    ; depthBoundConjecturedIsTrue =
        refl
    ; depthBoundProved =
        false
    ; depthBoundProvedIsFalse =
        refl
    }

record MonsterOrderDepthBoundReceipt : Setω where
  field
    status :
      MonsterOrderDepthBoundStatus

    trackedPrimeLane :
      List Lane.MonsterPrimeLane

    trackedPrimeLaneIsCanonical :
      trackedPrimeLane ≡ Lane.canonicalMonsterPrimeLane

    trackedPrimeLaneNats :
      List Nat

    trackedPrimeLaneNatsAreCanonical :
      trackedPrimeLaneNats ≡ Lane.canonicalMonsterPrimeLaneNats

    citationTokens :
      List MonsterOrderDepthBoundCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      (atlasMonsterOrderCitation
       ∷ conwayNortonMonstrousMoonshineCitation
       ∷ [])

    citationAuthority :
      Authority.CitationAuthorityBoundary

    citationAuthorityIsCanonical :
      citationAuthority ≡ monsterOrderCitationAuthority

    citationAuthorityHasNoArtifact :
      Authority.CitationAuthorityNoArtifact

    depthExponentAt :
      Lane.MonsterPrimeLane →
      Nat

    depthExponentAtIsMonsterOrderExponent :
      depthExponentAt ≡ monsterOrderDepthExponent

    depthExponentVector :
      List Nat

    depthExponentVectorIsCanonical :
      depthExponentVector ≡ monsterOrderDepthExponentVector15

    currentCarrierDepthVector :
      List Nat

    currentCarrierDepthVectorIsReadback :
      currentCarrierDepthVector ≡ currentCarrierDepthReadbackVector15

    currentCarrierDepthAt :
      Lane.MonsterPrimeLane →
      Nat

    currentCarrierDepthAtIsReadback :
      currentCarrierDepthAt ≡ currentCarrierDepthReadback

    allDiscoverableCurrentDepthsRespectMonsterOrderBound :
      Bool

    allDiscoverableCurrentDepthsRespectMonsterOrderBoundIsTrue :
      allDiscoverableCurrentDepthsRespectMonsterOrderBound ≡ true

    globalDepthBound :
      Nat

    globalDepthBoundIs46 :
      globalDepthBound ≡ monsterOrderGlobalDepthBound

    laneDepthBoundAt :
      (p : Lane.MonsterPrimeLane) →
      MonsterOrderLaneDepthBound p

    depthBoundConjectured :
      Bool

    depthBoundConjecturedIsTrue :
      depthBoundConjectured ≡ true

    depthBoundProved :
      Bool

    depthBoundProvedIsFalse :
      depthBoundProved ≡ false

    primeSetForcedFromFirstPrinciples :
      Bool

    primeSetForcedFromFirstPrinciplesIsFalse :
      primeSetForcedFromFirstPrinciples ≡ false

    closurePromotionFromThisReceipt :
      Bool

    closurePromotionFromThisReceiptIsFalse :
      closurePromotionFromThisReceipt ≡ false

    terminalPromotionFromThisReceipt :
      Bool

    terminalPromotionFromThisReceiptIsFalse :
      terminalPromotionFromThisReceipt ≡ false

    boundaries :
      List MonsterOrderDepthBoundBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalMonsterOrderDepthBoundBoundaries

    noPromotionWithoutAuthority :
      MonsterOrderDepthBoundPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open MonsterOrderDepthBoundReceipt public

canonicalMonsterOrderDepthBoundReceipt :
  MonsterOrderDepthBoundReceipt
canonicalMonsterOrderDepthBoundReceipt =
  record
    { status =
        conjecturalDepthBoundReceiptNoFirstPrinciplesPromotion
    ; trackedPrimeLane =
        Lane.canonicalMonsterPrimeLane
    ; trackedPrimeLaneIsCanonical =
        refl
    ; trackedPrimeLaneNats =
        Lane.canonicalMonsterPrimeLaneNats
    ; trackedPrimeLaneNatsAreCanonical =
        refl
    ; citationTokens =
        atlasMonsterOrderCitation
        ∷ conwayNortonMonstrousMoonshineCitation
        ∷ []
    ; citationTokensAreCanonical =
        refl
    ; citationAuthority =
        monsterOrderCitationAuthority
    ; citationAuthorityIsCanonical =
        refl
    ; citationAuthorityHasNoArtifact =
        monsterOrderCitationNoArtifact
    ; depthExponentAt =
        monsterOrderDepthExponent
    ; depthExponentAtIsMonsterOrderExponent =
        refl
    ; depthExponentVector =
        monsterOrderDepthExponentVector15
    ; depthExponentVectorIsCanonical =
        refl
    ; currentCarrierDepthVector =
        currentCarrierDepthReadbackVector15
    ; currentCarrierDepthVectorIsReadback =
        refl
    ; currentCarrierDepthAt =
        currentCarrierDepthReadback
    ; currentCarrierDepthAtIsReadback =
        refl
    ; allDiscoverableCurrentDepthsRespectMonsterOrderBound =
        true
    ; allDiscoverableCurrentDepthsRespectMonsterOrderBoundIsTrue =
        refl
    ; globalDepthBound =
        monsterOrderGlobalDepthBound
    ; globalDepthBoundIs46 =
        refl
    ; laneDepthBoundAt =
        canonicalMonsterOrderLaneDepthBound
    ; depthBoundConjectured =
        true
    ; depthBoundConjecturedIsTrue =
        refl
    ; depthBoundProved =
        false
    ; depthBoundProvedIsFalse =
        refl
    ; primeSetForcedFromFirstPrinciples =
        false
    ; primeSetForcedFromFirstPrinciplesIsFalse =
        refl
    ; closurePromotionFromThisReceipt =
        false
    ; closurePromotionFromThisReceiptIsFalse =
        refl
    ; terminalPromotionFromThisReceipt =
        false
    ; terminalPromotionFromThisReceiptIsFalse =
        refl
    ; boundaries =
        canonicalMonsterOrderDepthBoundBoundaries
    ; boundariesAreCanonical =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "The Monster order exponent table is recorded as an external depth-bound receipt over the tracked Moonshine prime lanes"
        ∷ "The global depth bound is recorded as 46 because the p=2 Monster-order exponent is 46"
        ∷ "Current discoverable carrier-depth readback records p2,p3,p5 as 1,2,3 from the DHR/SM carrier-dimension surface and the remaining tracked Moonshine lanes at depth 1 from the supersingular local-geometry surface"
        ∷ "Those current readback depths are within the corresponding Monster-order exponent targets 46,20,9,6,2,2,2,2,2,1,1,1,1,1,1"
        ∷ "depthBoundConjectured is true while depthBoundProved remains false"
        ∷ "primeSetForcedFromFirstPrinciples remains false"
        ∷ "No closure or terminal promotion is exported by this receipt"
        ∷ []
    }

monsterOrderDepthBoundConjectured :
  Bool
monsterOrderDepthBoundConjectured =
  depthBoundConjectured canonicalMonsterOrderDepthBoundReceipt

monsterOrderDepthBoundConjecturedIsTrue :
  monsterOrderDepthBoundConjectured ≡ true
monsterOrderDepthBoundConjecturedIsTrue =
  refl

monsterOrderDepthBoundProved :
  Bool
monsterOrderDepthBoundProved =
  depthBoundProved canonicalMonsterOrderDepthBoundReceipt

monsterOrderDepthBoundProvedIsFalse :
  monsterOrderDepthBoundProved ≡ false
monsterOrderDepthBoundProvedIsFalse =
  refl

monsterOrderPrimeSetForcedFromFirstPrinciples :
  Bool
monsterOrderPrimeSetForcedFromFirstPrinciples =
  primeSetForcedFromFirstPrinciples canonicalMonsterOrderDepthBoundReceipt

monsterOrderPrimeSetForcedFromFirstPrinciplesIsFalse :
  monsterOrderPrimeSetForcedFromFirstPrinciples ≡ false
monsterOrderPrimeSetForcedFromFirstPrinciplesIsFalse =
  refl
