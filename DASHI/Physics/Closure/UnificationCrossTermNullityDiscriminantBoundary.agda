module DASHI.Physics.Closure.UnificationCrossTermNullityDiscriminantBoundary where

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

quadraticText : String
quadraticText =
  "f(t)=G(s2)t^2+2B(s1,s2)t+G(s1) >= 0"

discriminantText : String
discriminantText =
  "B(s1,s2)^2 <= G(s1)G(s2)"

data UDiscriminantClause : Set where
  nonnegativeQuadraticFamilyRecorded : UDiscriminantClause
  discriminantNonpositiveRouteRecorded : UDiscriminantClause
  cauchySchwarzFromDiscriminantRecorded : UDiscriminantClause
  nullOrthogonalityForZeroNormRecorded : UDiscriminantClause
  representativeIndependenceSeedRecorded : UDiscriminantClause
  quotientDescentSeedRecorded : UDiscriminantClause
  downstreamParallelogramRouteRecorded : UDiscriminantClause

canonicalUDiscriminantClauses : List UDiscriminantClause
canonicalUDiscriminantClauses =
  nonnegativeQuadraticFamilyRecorded
  ∷ discriminantNonpositiveRouteRecorded
  ∷ cauchySchwarzFromDiscriminantRecorded
  ∷ nullOrthogonalityForZeroNormRecorded
  ∷ representativeIndependenceSeedRecorded
  ∷ quotientDescentSeedRecorded
  ∷ downstreamParallelogramRouteRecorded
  ∷ []

uDiscriminantClauseCount : Nat
uDiscriminantClauseCount = listLength canonicalUDiscriminantClauses

uDiscriminantClauseCountIs7 : uDiscriminantClauseCount ≡ 7
uDiscriminantClauseCountIs7 = refl

data UDiscriminantBlocker : Set where
  blocker-nonnegativeQuadraticAssumptionStillAbstract : UDiscriminantBlocker
  blocker-cauchySchwarzTheoremStillOpen : UDiscriminantBlocker
  blocker-nullClassClosureStillOpen : UDiscriminantBlocker
  blocker-u1aPromotionForbidden : UDiscriminantBlocker

canonicalUDiscriminantBlockers : List UDiscriminantBlocker
canonicalUDiscriminantBlockers =
  blocker-nonnegativeQuadraticAssumptionStillAbstract
  ∷ blocker-cauchySchwarzTheoremStillOpen
  ∷ blocker-nullClassClosureStillOpen
  ∷ blocker-u1aPromotionForbidden
  ∷ []

UnificationCrossTermNullityDiscriminantRecorded : Bool
UnificationCrossTermNullityDiscriminantRecorded = true

UnificationCrossTermNullityDiscriminantProved : Bool
UnificationCrossTermNullityDiscriminantProved = false

record UnificationCrossTermNullityDiscriminantBoundary : Set where
  field
    clauses : List UDiscriminantClause
    clausesCanonical : clauses ≡ canonicalUDiscriminantClauses
    blockers : List UDiscriminantBlocker
    blockersCanonical : blockers ≡ canonicalUDiscriminantBlockers
    clauseCountIs7 : uDiscriminantClauseCount ≡ 7
    theoremStillFalse :
      UnificationCrossTermNullityDiscriminantProved ≡ false

canonicalUnificationCrossTermNullityDiscriminantBoundary :
  UnificationCrossTermNullityDiscriminantBoundary
canonicalUnificationCrossTermNullityDiscriminantBoundary =
  record
    { clauses = canonicalUDiscriminantClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUDiscriminantBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

UnificationCrossTermNullityDiscriminantRecordedIsTrue :
  UnificationCrossTermNullityDiscriminantRecorded ≡ true
UnificationCrossTermNullityDiscriminantRecordedIsTrue = refl
