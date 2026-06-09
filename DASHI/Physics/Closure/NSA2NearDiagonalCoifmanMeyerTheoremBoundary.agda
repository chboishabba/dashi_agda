module DASHI.Physics.Closure.NSA2NearDiagonalCoifmanMeyerTheoremBoundary where

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

routeBoundaryReference : String
routeBoundaryReference =
  "DASHI.Physics.Closure.NSA2NearDiagonalCoifmanMeyerRouteBoundary"

tightEstimateText : String
tightEstimateText =
  "||T(ω_j,ω_k)||_L2 <= C * 2^min(j,k) * ||ω_j|| * ||ω_k|| for |j-k| <= C0"

data A2TheoremClause : Set where
  nearDiagonalShellInteractionDominates : A2TheoremClause
  coifmanMeyerMultiplierBound : A2TheoremClause
  triadicCouplingMostlyNearDiagonal : A2TheoremClause
  abelTelescopeDefectBound : A2TheoremClause
  cauchySchwarzWeakensToRootN : A2TheoremClause
  stationarityDefectDeltaR : A2TheoremClause
  epsilon0CompatibilityTable : A2TheoremClause

canonicalA2TheoremClauses : List A2TheoremClause
canonicalA2TheoremClauses =
  nearDiagonalShellInteractionDominates
  ∷ coifmanMeyerMultiplierBound
  ∷ triadicCouplingMostlyNearDiagonal
  ∷ abelTelescopeDefectBound
  ∷ cauchySchwarzWeakensToRootN
  ∷ stationarityDefectDeltaR
  ∷ epsilon0CompatibilityTable
  ∷ []

a2TheoremClauseCount : Nat
a2TheoremClauseCount = listLength canonicalA2TheoremClauses

a2TheoremClauseCountIs7 : a2TheoremClauseCount ≡ 7
a2TheoremClauseCountIs7 = refl

data A2DefectRateClause : Set where
  deltaRIsLogWindowRootRate : A2DefectRateClause
  nearDiagonalShareRecorded : A2DefectRateClause
  wMinusOneOneNormTarget : A2DefectRateClause
  commonR0CompatibilityRecorded : A2DefectRateClause

canonicalA2DefectRateClauses : List A2DefectRateClause
canonicalA2DefectRateClauses =
  deltaRIsLogWindowRootRate
  ∷ nearDiagonalShareRecorded
  ∷ wMinusOneOneNormTarget
  ∷ commonR0CompatibilityRecorded
  ∷ []

a2DefectRateClauseCount : Nat
a2DefectRateClauseCount = listLength canonicalA2DefectRateClauses

a2DefectRateClauseCountIs4 : a2DefectRateClauseCount ≡ 4
a2DefectRateClauseCountIs4 = refl

data A2TheoremBlocker : Set where
  blocker-truePDECoifmanMeyerWriteupOpen : A2TheoremBlocker
  blocker-wMinusOneOneStationarityProofOpen : A2TheoremBlocker
  blocker-epsilon0CompatibilityProofOpen : A2TheoremBlocker
  blocker-a5TransferStillOpen : A2TheoremBlocker
  blocker-clayPromotionForbidden : A2TheoremBlocker

canonicalA2TheoremBlockers : List A2TheoremBlocker
canonicalA2TheoremBlockers =
  blocker-truePDECoifmanMeyerWriteupOpen
  ∷ blocker-wMinusOneOneStationarityProofOpen
  ∷ blocker-epsilon0CompatibilityProofOpen
  ∷ blocker-a5TransferStillOpen
  ∷ blocker-clayPromotionForbidden
  ∷ []

a2TheoremRecorded : Bool
a2TheoremRecorded = true

A2NearDiagonalCoifmanMeyerTheoremProved : Bool
A2NearDiagonalCoifmanMeyerTheoremProved = false

NSClayPromotedFromA2Theorem : Bool
NSClayPromotedFromA2Theorem = false

record NSA2NearDiagonalCoifmanMeyerTheoremBoundary : Set where
  field
    theoremClauses : List A2TheoremClause
    theoremClausesCanonical : theoremClauses ≡ canonicalA2TheoremClauses
    defectRateClauses : List A2DefectRateClause
    defectRateClausesCanonical :
      defectRateClauses ≡ canonicalA2DefectRateClauses
    blockers : List A2TheoremBlocker
    blockersCanonical : blockers ≡ canonicalA2TheoremBlockers
    theoremClauseCountIs7 : a2TheoremClauseCount ≡ 7
    defectRateClauseCountIs4 : a2DefectRateClauseCount ≡ 4
    theoremStillFalse : A2NearDiagonalCoifmanMeyerTheoremProved ≡ false
    nsClayStillFalse : NSClayPromotedFromA2Theorem ≡ false

canonicalNSA2NearDiagonalCoifmanMeyerTheoremBoundary :
  NSA2NearDiagonalCoifmanMeyerTheoremBoundary
canonicalNSA2NearDiagonalCoifmanMeyerTheoremBoundary =
  record
    { theoremClauses = canonicalA2TheoremClauses
    ; theoremClausesCanonical = refl
    ; defectRateClauses = canonicalA2DefectRateClauses
    ; defectRateClausesCanonical = refl
    ; blockers = canonicalA2TheoremBlockers
    ; blockersCanonical = refl
    ; theoremClauseCountIs7 = refl
    ; defectRateClauseCountIs4 = refl
    ; theoremStillFalse = refl
    ; nsClayStillFalse = refl
    }

a2TheoremRecordedIsTrue : a2TheoremRecorded ≡ true
a2TheoremRecordedIsTrue = refl
