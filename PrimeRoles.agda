module PrimeRoles where

open import Agda.Builtin.Nat      using (Nat)
open import Data.Nat.Base         using (_<_ )
open import Agda.Builtin.Bool     using (Bool; true; false)
open import MonsterOntos

------------------------------------------------------------------------
-- Roles (you can refine these into a lattice later)

data Role : Set where
  Types       : Role
  Operators   : Role
  Functions   : Role
  Consensus   : Role
  Completion  : Role
  Domain      : Nat → Role   -- generic “domain lane” if you want more structure

roleOf : SSP → Role
roleOf p2  = Types
roleOf p3  = Operators
roleOf p11 = Functions
roleOf p23 = Consensus
roleOf p71 = Completion
-- the rest: either assign Domain lanes or make a richer record
roleOf p5  = Domain 5
roleOf p7  = Domain 7
roleOf p13 = Domain 13
roleOf p17 = Domain 17
roleOf p19 = Domain 19
roleOf p29 = Domain 29
roleOf p31 = Domain 31
roleOf p41 = Domain 41
roleOf p47 = Domain 47
roleOf p59 = Domain 59

------------------------------------------------------------------------
-- “Axiom of completion” as a termination measure contract:
-- Completion prime provides a stop condition for any recursive refinement loop.

record CompletionLaw (S : Set) : Set₁ where
  field
    measure : S → Nat
    step    : S → S
    -- If step decreases measure, recursion terminates.
    decreases : ∀ s → measure (step s) < measure s
