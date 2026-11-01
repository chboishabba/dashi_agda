module DASHI.Physics.Closure.UnificationHierarchyConsistencyKillsFourPointDefectBoundary where

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

hypothesisReference : String
hypothesisReference =
  "DASHI.Physics.Closure.UnificationScaleInvariantCrossTermHypothesisBoundary"

u1aReference : String
u1aReference =
  "DASHI.Physics.Closure.UnificationCrossTermNullityLightweightBoundary"

hcFormulaText : String
hcFormulaText =
  "G(s1+lambda*s2)=G(s1)+lambda^2*G(s2)+2*lambda*B(s1,s2)"

fourPointFormulaText : String
fourPointFormulaText =
  "G(s1+s2)+G(s1-s2)-2G(s1)-2G(s2)=0"

data UHierarchyConsistencyClause : Set where
  h1PlusU1aHDetermineHC : UHierarchyConsistencyClause
  lambdaScaledCrossTermFormulaRecorded : UHierarchyConsistencyClause
  bilinearScalingInLambdaRecorded : UHierarchyConsistencyClause
  plusMinusOneSummationKillsCrossTerm : UHierarchyConsistencyClause
  nullClassStabilityFromBdotnZero : UHierarchyConsistencyClause
  quotientRepresentativeIndependenceRecorded : UHierarchyConsistencyClause
  fourPointDefectKilledRecorded : UHierarchyConsistencyClause

canonicalUHierarchyConsistencyClauses : List UHierarchyConsistencyClause
canonicalUHierarchyConsistencyClauses =
  h1PlusU1aHDetermineHC
  ∷ lambdaScaledCrossTermFormulaRecorded
  ∷ bilinearScalingInLambdaRecorded
  ∷ plusMinusOneSummationKillsCrossTerm
  ∷ nullClassStabilityFromBdotnZero
  ∷ quotientRepresentativeIndependenceRecorded
  ∷ fourPointDefectKilledRecorded
  ∷ []

uHierarchyConsistencyClauseCount : Nat
uHierarchyConsistencyClauseCount =
  listLength canonicalUHierarchyConsistencyClauses

uHierarchyConsistencyClauseCountIs7 :
  uHierarchyConsistencyClauseCount ≡ 7
uHierarchyConsistencyClauseCountIs7 = refl

data UHierarchyConsistencyBlocker : Set where
  blocker-bilinearWitnessStillOpen : UHierarchyConsistencyBlocker
  blocker-h1ToScalingRouteStillOpen : UHierarchyConsistencyBlocker
  blocker-fourPointTheoremStillOpen : UHierarchyConsistencyBlocker
  blocker-parallelogramStillOpen : UHierarchyConsistencyBlocker
  blocker-terminalPromotionForbidden : UHierarchyConsistencyBlocker

canonicalUHierarchyConsistencyBlockers : List UHierarchyConsistencyBlocker
canonicalUHierarchyConsistencyBlockers =
  blocker-bilinearWitnessStillOpen
  ∷ blocker-h1ToScalingRouteStillOpen
  ∷ blocker-fourPointTheoremStillOpen
  ∷ blocker-parallelogramStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationHierarchyConsistencyKillsFourPointDefectRecorded : Bool
UnificationHierarchyConsistencyKillsFourPointDefectRecorded = true

UnificationHierarchyConsistencyKillsFourPointDefectProved : Bool
UnificationHierarchyConsistencyKillsFourPointDefectProved = false

FourPointPromotionFromHierarchyConsistency : Bool
FourPointPromotionFromHierarchyConsistency = false

record UnificationHierarchyConsistencyKillsFourPointDefectBoundary : Set where
  field
    clauses : List UHierarchyConsistencyClause
    clausesCanonical : clauses ≡ canonicalUHierarchyConsistencyClauses
    blockers : List UHierarchyConsistencyBlocker
    blockersCanonical : blockers ≡ canonicalUHierarchyConsistencyBlockers
    clauseCountIs7 : uHierarchyConsistencyClauseCount ≡ 7
    theoremStillFalse :
      UnificationHierarchyConsistencyKillsFourPointDefectProved ≡ false
    fourPointStillFalse :
      FourPointPromotionFromHierarchyConsistency ≡ false

canonicalUnificationHierarchyConsistencyKillsFourPointDefectBoundary :
  UnificationHierarchyConsistencyKillsFourPointDefectBoundary
canonicalUnificationHierarchyConsistencyKillsFourPointDefectBoundary =
  record
    { clauses = canonicalUHierarchyConsistencyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUHierarchyConsistencyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    ; fourPointStillFalse = refl
    }

UnificationHierarchyConsistencyKillsFourPointDefectRecordedIsTrue :
  UnificationHierarchyConsistencyKillsFourPointDefectRecorded ≡ true
UnificationHierarchyConsistencyKillsFourPointDefectRecordedIsTrue = refl
