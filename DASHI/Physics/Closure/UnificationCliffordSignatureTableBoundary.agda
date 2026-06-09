module DASHI.Physics.Closure.UnificationCliffordSignatureTableBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data CliffordSignatureRow : Set where
  cl13-to-m4r-dirac : CliffordSignatureRow
  cl40-to-m2h-euclidean : CliffordSignatureRow
  cl31-to-m4r-majorana : CliffordSignatureRow

canonicalCliffordSignatureRows : List CliffordSignatureRow
canonicalCliffordSignatureRows =
  cl13-to-m4r-dirac
  ∷ cl40-to-m2h-euclidean
  ∷ cl31-to-m4r-majorana
  ∷ []

cliffordSignatureRowCount : Nat
cliffordSignatureRowCount = listLength canonicalCliffordSignatureRows

cliffordSignatureRowCountIs3 : cliffordSignatureRowCount ≡ 3
cliffordSignatureRowCountIs3 = refl

cl13Text : String
cl13Text = "Cl(1,3) = M4(R) [Dirac]"

cl40Text : String
cl40Text = "Cl(4,0) = M2(H)"

cl31Text : String
cl31Text = "Cl(3,1) = M4(R) [Majorana]"

data CliffordSignatureBlocker : Set where
  blocker-signatureConsumerWriteupStillOpen : CliffordSignatureBlocker
  blocker-physicsLaneAdapterStillOpen : CliffordSignatureBlocker
  blocker-terminalPromotionForbidden : CliffordSignatureBlocker

canonicalCliffordSignatureBlockers : List CliffordSignatureBlocker
canonicalCliffordSignatureBlockers =
  blocker-signatureConsumerWriteupStillOpen
  ∷ blocker-physicsLaneAdapterStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationCliffordSignatureTableRecorded : Bool
UnificationCliffordSignatureTableRecorded = true

UnificationCliffordSignatureTableProved : Bool
UnificationCliffordSignatureTableProved = false

record UnificationCliffordSignatureTableBoundary : Set where
  field
    rows : List CliffordSignatureRow
    rowsCanonical : rows ≡ canonicalCliffordSignatureRows
    blockers : List CliffordSignatureBlocker
    blockersCanonical : blockers ≡ canonicalCliffordSignatureBlockers
    rowCountIs3 : cliffordSignatureRowCount ≡ 3
    theoremStillFalse : UnificationCliffordSignatureTableProved ≡ false

canonicalUnificationCliffordSignatureTableBoundary :
  UnificationCliffordSignatureTableBoundary
canonicalUnificationCliffordSignatureTableBoundary =
  record
    { rows = canonicalCliffordSignatureRows
    ; rowsCanonical = refl
    ; blockers = canonicalCliffordSignatureBlockers
    ; blockersCanonical = refl
    ; rowCountIs3 = refl
    ; theoremStillFalse = refl
    }

UnificationCliffordSignatureTableRecordedIsTrue :
  UnificationCliffordSignatureTableRecorded ≡ true
UnificationCliffordSignatureTableRecordedIsTrue = refl
