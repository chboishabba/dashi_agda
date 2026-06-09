module DASHI.Physics.Closure.SupersingularPrimeLaneBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine

data SupersingularPrimeLaneBridgeStatus : Set where
  supersingularPrimeLaneBridgeRecordedNoFirstPrinciplesForce :
    SupersingularPrimeLaneBridgeStatus

data SupersingularPrimeLaneAuthorityCitation : Set where
  ogg1975SupersingularPrimesCitation :
    SupersingularPrimeLaneAuthorityCitation
  borcherds1992MonstrousMoonshineCitation :
    SupersingularPrimeLaneAuthorityCitation

canonicalSupersingularPrimeLaneAuthorityCitations :
  List SupersingularPrimeLaneAuthorityCitation
canonicalSupersingularPrimeLaneAuthorityCitations =
  ogg1975SupersingularPrimesCitation ∷
  borcherds1992MonstrousMoonshineCitation ∷
  []

canonicalSupersingularPrimeLaneNats : List Nat
canonicalSupersingularPrimeLaneNats =
  2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ 17 ∷ 19 ∷ 23 ∷ 29 ∷
  31 ∷ 41 ∷ 47 ∷ 59 ∷ 71 ∷ []

canonicalSupersingularPrimeLanes : List Moonshine.MonsterPrimeLane
canonicalSupersingularPrimeLanes = Moonshine.canonicalMonsterPrimeLane

record Depth1SupersingularFieldCompletion
  (p : Moonshine.MonsterPrimeLane) : Set where
  field
    primeLane : Moonshine.MonsterPrimeLane
    primeLaneIsRequested : primeLane ≡ p
    primeNat : Nat
    primeNatIsLaneNat : primeNat ≡ Moonshine.monsterPrimeLaneToNat p
    uniqueSupersingularJInvariant : Bool
    uniqueSupersingularJInvariantIsTrue :
      uniqueSupersingularJInvariant ≡ true
    splitsOverFp : Bool
    splitsOverFpIsTrue : splitsOverFp ≡ true
    depth1FieldComplete : Bool
    depth1FieldCompleteIsTrue : depth1FieldComplete ≡ true
    completionBoundary : List String

open Depth1SupersingularFieldCompletion public

p2Depth1SupersingularFieldCompletion :
  Depth1SupersingularFieldCompletion Moonshine.p2
p2Depth1SupersingularFieldCompletion = record
  { primeLane = Moonshine.p2
  ; primeLaneIsRequested = refl
  ; primeNat = 2
  ; primeNatIsLaneNat = refl
  ; uniqueSupersingularJInvariant = true
  ; uniqueSupersingularJInvariantIsTrue = refl
  ; splitsOverFp = true
  ; splitsOverFpIsTrue = refl
  ; depth1FieldComplete = true
  ; depth1FieldCompleteIsTrue = refl
  ; completionBoundary =
      "p=2 depth-1 field lane records the unique supersingular j-invariant." ∷
      "The depth-1 j-invariant is split over F_p for this finite receipt." ∷
      []
  }

p3Depth1SupersingularFieldCompletion :
  Depth1SupersingularFieldCompletion Moonshine.p3
p3Depth1SupersingularFieldCompletion = record
  { primeLane = Moonshine.p3
  ; primeLaneIsRequested = refl
  ; primeNat = 3
  ; primeNatIsLaneNat = refl
  ; uniqueSupersingularJInvariant = true
  ; uniqueSupersingularJInvariantIsTrue = refl
  ; splitsOverFp = true
  ; splitsOverFpIsTrue = refl
  ; depth1FieldComplete = true
  ; depth1FieldCompleteIsTrue = refl
  ; completionBoundary =
      "p=3 depth-1 field lane records the unique supersingular j-invariant." ∷
      "The depth-1 j-invariant is split over F_p for this finite receipt." ∷
      []
  }

p5Depth1SupersingularFieldCompletion :
  Depth1SupersingularFieldCompletion Moonshine.p5
p5Depth1SupersingularFieldCompletion = record
  { primeLane = Moonshine.p5
  ; primeLaneIsRequested = refl
  ; primeNat = 5
  ; primeNatIsLaneNat = refl
  ; uniqueSupersingularJInvariant = true
  ; uniqueSupersingularJInvariantIsTrue = refl
  ; splitsOverFp = true
  ; splitsOverFpIsTrue = refl
  ; depth1FieldComplete = true
  ; depth1FieldCompleteIsTrue = refl
  ; completionBoundary =
      "p=5 depth-1 field lane records the unique supersingular j-invariant." ∷
      "The depth-1 j-invariant is split over F_p for this finite receipt." ∷
      []
  }

p7Depth1SupersingularFieldCompletion :
  Depth1SupersingularFieldCompletion Moonshine.p7
p7Depth1SupersingularFieldCompletion = record
  { primeLane = Moonshine.p7
  ; primeLaneIsRequested = refl
  ; primeNat = 7
  ; primeNatIsLaneNat = refl
  ; uniqueSupersingularJInvariant = true
  ; uniqueSupersingularJInvariantIsTrue = refl
  ; splitsOverFp = true
  ; splitsOverFpIsTrue = refl
  ; depth1FieldComplete = true
  ; depth1FieldCompleteIsTrue = refl
  ; completionBoundary =
      "p=7 depth-1 field lane records the unique supersingular j-invariant." ∷
      "The depth-1 j-invariant is split over F_p for this finite receipt." ∷
      []
  }

record SupersingularPrimeLaneBridgeReceipt : Setω where
  field
    status : SupersingularPrimeLaneBridgeStatus
    DASHIPrimeSetIsP_SS : Bool
    DASHIPrimeSetIsP_SS-is-true : DASHIPrimeSetIsP_SS ≡ true
    primeSetForcedFromFirstPrinciples : Bool
    primeSetForcedFromFirstPrinciples-is-false :
      primeSetForcedFromFirstPrinciples ≡ false
    oggOriginalQuestionResolved : Bool
    oggOriginalQuestionResolved-is-false :
      oggOriginalQuestionResolved ≡ false
    dashiPrimeSet : List Moonshine.MonsterPrimeLane
    dashiPrimeSetIsCanonical :
      dashiPrimeSet ≡ Moonshine.canonicalMonsterPrimeLane
    supersingularPrimeSetNats : List Nat
    supersingularPrimeSetNatsAreCanonical :
      supersingularPrimeSetNats ≡ canonicalSupersingularPrimeLaneNats
    citationAuthorityTokens : List SupersingularPrimeLaneAuthorityCitation
    citationAuthorityTokensAreCanonical :
      citationAuthorityTokens ≡
      canonicalSupersingularPrimeLaneAuthorityCitations
    ogg1975AuthorityToken : SupersingularPrimeLaneAuthorityCitation
    ogg1975AuthorityTokenIsCanonical :
      ogg1975AuthorityToken ≡ ogg1975SupersingularPrimesCitation
    borcherds1992AuthorityToken : SupersingularPrimeLaneAuthorityCitation
    borcherds1992AuthorityTokenIsCanonical :
      borcherds1992AuthorityToken ≡
      borcherds1992MonstrousMoonshineCitation
    p2Depth1FieldComplete :
      Depth1SupersingularFieldCompletion Moonshine.p2
    p3Depth1FieldComplete :
      Depth1SupersingularFieldCompletion Moonshine.p3
    p5Depth1FieldComplete :
      Depth1SupersingularFieldCompletion Moonshine.p5
    p7Depth1FieldComplete :
      Depth1SupersingularFieldCompletion Moonshine.p7
    bridgeBoundary : List String

open SupersingularPrimeLaneBridgeReceipt public

canonicalSupersingularPrimeLaneBridgeReceipt :
  SupersingularPrimeLaneBridgeReceipt
canonicalSupersingularPrimeLaneBridgeReceipt = record
  { status =
      supersingularPrimeLaneBridgeRecordedNoFirstPrinciplesForce
  ; DASHIPrimeSetIsP_SS = true
  ; DASHIPrimeSetIsP_SS-is-true = refl
  ; primeSetForcedFromFirstPrinciples = false
  ; primeSetForcedFromFirstPrinciples-is-false = refl
  ; oggOriginalQuestionResolved = false
  ; oggOriginalQuestionResolved-is-false = refl
  ; dashiPrimeSet = Moonshine.canonicalMonsterPrimeLane
  ; dashiPrimeSetIsCanonical = refl
  ; supersingularPrimeSetNats = canonicalSupersingularPrimeLaneNats
  ; supersingularPrimeSetNatsAreCanonical = refl
  ; citationAuthorityTokens =
      canonicalSupersingularPrimeLaneAuthorityCitations
  ; citationAuthorityTokensAreCanonical = refl
  ; ogg1975AuthorityToken = ogg1975SupersingularPrimesCitation
  ; ogg1975AuthorityTokenIsCanonical = refl
  ; borcherds1992AuthorityToken =
      borcherds1992MonstrousMoonshineCitation
  ; borcherds1992AuthorityTokenIsCanonical = refl
  ; p2Depth1FieldComplete = p2Depth1SupersingularFieldCompletion
  ; p3Depth1FieldComplete = p3Depth1SupersingularFieldCompletion
  ; p5Depth1FieldComplete = p5Depth1SupersingularFieldCompletion
  ; p7Depth1FieldComplete = p7Depth1SupersingularFieldCompletion
  ; bridgeBoundary =
      "DASHIPrimeSetIsP_SS records the DASHI prime set as the 15 Ogg supersingular primes." ∷
      "This bridge is authority-bound by Ogg 1975 and Borcherds 1992 tokens only." ∷
      "primeSetForcedFromFirstPrinciples remains false." ∷
      "oggOriginalQuestionResolved remains false." ∷
      "Depth-1 finite-field completion is recorded only for p in {2,3,5,7}." ∷
      []
  }

supersingularPrimeLaneBridgeDASHIPrimeSetIsPSS :
  DASHIPrimeSetIsP_SS canonicalSupersingularPrimeLaneBridgeReceipt ≡ true
supersingularPrimeLaneBridgeDASHIPrimeSetIsPSS = refl

supersingularPrimeLaneBridgeNotForcedFromFirstPrinciples :
  primeSetForcedFromFirstPrinciples
    canonicalSupersingularPrimeLaneBridgeReceipt ≡ false
supersingularPrimeLaneBridgeNotForcedFromFirstPrinciples = refl

supersingularPrimeLaneBridgeOggQuestionStillOpen :
  oggOriginalQuestionResolved
    canonicalSupersingularPrimeLaneBridgeReceipt ≡ false
supersingularPrimeLaneBridgeOggQuestionStillOpen = refl

p2Depth1FieldCompletionIsTrue :
  depth1FieldComplete p2Depth1SupersingularFieldCompletion ≡ true
p2Depth1FieldCompletionIsTrue = refl

p3Depth1FieldCompletionIsTrue :
  depth1FieldComplete p3Depth1SupersingularFieldCompletion ≡ true
p3Depth1FieldCompletionIsTrue = refl

p5Depth1FieldCompletionIsTrue :
  depth1FieldComplete p5Depth1SupersingularFieldCompletion ≡ true
p5Depth1FieldCompletionIsTrue = refl

p7Depth1FieldCompletionIsTrue :
  depth1FieldComplete p7Depth1SupersingularFieldCompletion ≡ true
p7Depth1FieldCompletionIsTrue = refl
