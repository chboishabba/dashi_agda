module DASHI.Physics.Closure.YMOnlyRemainingAuthorityBlockersBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data YMRemainingAuthorityBlocker : Set where
  rpTheoremAuthorityOpen : YMRemainingAuthorityBlocker
  osWightmanAuthorityOpen : YMRemainingAuthorityBlocker
  externalAcceptanceOpen : YMRemainingAuthorityBlocker
  finalPackagingAuthorityOpen : YMRemainingAuthorityBlocker
  clayPromotionForbidden : YMRemainingAuthorityBlocker

canonicalYMRemainingAuthorityBlockers : List YMRemainingAuthorityBlocker
canonicalYMRemainingAuthorityBlockers =
  rpTheoremAuthorityOpen
  ∷ osWightmanAuthorityOpen
  ∷ externalAcceptanceOpen
  ∷ finalPackagingAuthorityOpen
  ∷ clayPromotionForbidden
  ∷ []

ymRemainingAuthorityBlockerCount : Nat
ymRemainingAuthorityBlockerCount =
  listLength canonicalYMRemainingAuthorityBlockers

ymRemainingAuthorityBlockerCountIs5 : ymRemainingAuthorityBlockerCount ≡ 5
ymRemainingAuthorityBlockerCountIs5 = refl

YMOnlyRemainingAuthorityBlockersRecorded : Bool
YMOnlyRemainingAuthorityBlockersRecorded = true

YMOnlyRemainingAuthorityBlockersDischarged : Bool
YMOnlyRemainingAuthorityBlockersDischarged = false

record YMOnlyRemainingAuthorityBlockersBoundary : Set where
  field
    blockers : List YMRemainingAuthorityBlocker
    blockersCanonical : blockers ≡ canonicalYMRemainingAuthorityBlockers
    blockerCountIs5 : ymRemainingAuthorityBlockerCount ≡ 5
    dischargedStillFalse : YMOnlyRemainingAuthorityBlockersDischarged ≡ false

canonicalYMOnlyRemainingAuthorityBlockersBoundary :
  YMOnlyRemainingAuthorityBlockersBoundary
canonicalYMOnlyRemainingAuthorityBlockersBoundary =
  record
    { blockers = canonicalYMRemainingAuthorityBlockers
    ; blockersCanonical = refl
    ; blockerCountIs5 = refl
    ; dischargedStillFalse = refl
    }

YMOnlyRemainingAuthorityBlockersRecordedIsTrue :
  YMOnlyRemainingAuthorityBlockersRecorded ≡ true
YMOnlyRemainingAuthorityBlockersRecordedIsTrue = refl
