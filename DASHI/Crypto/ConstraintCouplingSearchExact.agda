module DASHI.Crypto.ConstraintCouplingSearchExact where

------------------------------------------------------------------------
-- CONSTRAINT COUPLING / SEPARATOR SEARCH
--
-- This is a finite abstraction of the graph induced by shared variables across
-- local residual constraints.  It proves three boundaries:
--   * disconnected components compose constructively;
--   * merely being connected is not a hardness theorem;
--   * a supplied bounded separator yields an explicit dynamic-programming work
--     formula.  No universal treewidth theorem is claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

record DisconnectedTwoComponentProblem : Set₁ where
  constructor disconnectedTwoComponentProblem
  field
    Left Right : Set
    ValidL : Left → Set
    ValidR : Right → Set

open DisconnectedTwoComponentProblem public

GlobalDisconnected :
  (problem : DisconnectedTwoComponentProblem) → Left problem × Right problem → Set
GlobalDisconnected problem (l , r) = ValidL problem l × ValidR problem r

disconnectedSearchFactors :
  ∀ {problem : DisconnectedTwoComponentProblem}
    {l : Left problem} {r : Right problem} →
  ValidL problem l → ValidR problem r → GlobalDisconnected problem (l , r)
disconnectedSearchFactors left right = left , right

------------------------------------------------------------------------
-- Connectedness alone is not hardness.  Equality couples two Bool variables,
-- yet (false,false) is an immediate satisfying witness.
------------------------------------------------------------------------

data EqualityConstraint : Bool → Bool → Set where
  eq-false : EqualityConstraint false false
  eq-true : EqualityConstraint true true

record ConnectedBoolWitness : Set where
  constructor connectedBoolWitness
  field
    left right : Bool
    edgeConstraint : EqualityConstraint left right

connectedConstraintHasEasyWitness : ConnectedBoolWitness
connectedConstraintHasEasyWitness = connectedBoolWitness false false eq-false

------------------------------------------------------------------------
-- Separator certificate.  Rather than smuggling a complete treewidth theorem
-- into a small formal layer, the application supplies a separator-state count
-- and the work to solve each side conditioned on one separator state.
------------------------------------------------------------------------

record BoundedSeparatorSearchCertificate : Set where
  constructor boundedSeparatorSearchCertificate
  field
    separatorStates : Nat
    leftWorkPerState : Nat
    rightWorkPerState : Nat
    reconcileWorkPerState : Nat

open BoundedSeparatorSearchCertificate public

separatorDPBound : BoundedSeparatorSearchCertificate → Nat
separatorDPBound certificate =
  separatorStates certificate *
  (leftWorkPerState certificate +
   rightWorkPerState certificate +
   reconcileWorkPerState certificate)

-- A width-like bound becomes useful only through a proof-bearing certificate
-- connecting it to the actual separator state count.
record WidthBoundedSeparator : Set where
  constructor widthBoundedSeparator
  field
    widthBound : Nat
    stateAlphabetSize : Nat
    suppliedStateBound : Nat
    separatorSearch : BoundedSeparatorSearchCertificate

open WidthBoundedSeparator public

------------------------------------------------------------------------
-- Coupling can restore the full bottleneck after excellent local compression.
------------------------------------------------------------------------

record ReconciliationRestoresBottleneck : Set where
  constructor reconciliationRestoresBottleneck
  field
    rawHiddenWork : Nat
    localWork : Nat
    reconciliationWork : Nat
    combinedWork : Nat
    exactAccounting : combinedWork ≡ localWork + reconciliationWork

open ReconciliationRestoresBottleneck public
