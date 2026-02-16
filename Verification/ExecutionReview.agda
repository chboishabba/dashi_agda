module Verification.ExecutionReview where

open import Verification.Prelude

-- A tiny abstract control-flow model.
postulate Program : Set
postulate Path    : Set

-- Static analyzer produces a set/list of feasible paths
postulate enumeratePaths : Program → List Path

-- A property you claim holds on all paths.
postulate SafeOnPath : Program → Path → Set

-- “Execution review” = proof that for every enumerated path, Safe holds.
All : ∀ {A : Set} → (A → Set) → List A → Set
All P []       = ⊤
All P (x ∷ xs) = P x × All P xs

record ExecutionReview : Set₁ where
  field
    P   : Program
    ok  : All (SafeOnPath P) (enumeratePaths P)
