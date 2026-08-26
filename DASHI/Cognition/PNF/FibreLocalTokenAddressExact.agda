module DASHI.Cognition.PNF.FibreLocalTokenAddressExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_)

------------------------------------------------------------------------
-- Identity and addressing layers for the delta-native hot path.
--
-- Stable semantic identity, database authority identity, fibre-local execution
-- address, and transient solver/path address are distinct coordinates.  The hot
-- token solver therefore need not carry one corpus-global surrogate for every
-- token or branch candidate.
------------------------------------------------------------------------

data IdentityLayer : Set where
  semanticIdentityLayer
  authorityIdentityLayer
  fibreAddressLayer
  solverPathLayer : IdentityLayer

record FibreAddress : Set where
  constructor fibreAddress
  field
    fibreAuthorityId : Nat
    tokenOrdinal : Nat

open FibreAddress public

record LocalTokenAddress : Set where
  constructor localTokenAddress
  field
    localOrdinal : Nat

open LocalTokenAddress public

globalizeLocal : Nat → LocalTokenAddress → FibreAddress
globalizeLocal fibre (localTokenAddress ordinal) =
  fibreAddress fibre ordinal

localizeGlobal : FibreAddress → LocalTokenAddress
localizeGlobal address = localTokenAddress (tokenOrdinal address)

localizeGlobalize :
  (fibre : Nat) → (address : LocalTokenAddress) →
  localizeGlobal (globalizeLocal fibre address) ≡ address
localizeGlobalize fibre (localTokenAddress ordinal) = refl

------------------------------------------------------------------------
-- Token-owned parser observation.
--
-- start/end coordinates and lexical/parser annotations are properties of the
-- token observation.  Sentence/fibre identity is supplied by containment, and
-- the dependency head is represented by a local fibre coordinate rather than a
-- mandatory independent global token surrogate.
------------------------------------------------------------------------

record TokenOwnedObservation : Set where
  constructor tokenOwnedObservation
  field
    startChar endChar : Nat
    orthSymbol lemmaSymbol posSymbol tagSymbol dependencySymbol morphSet : Nat
    lemmaOrigin posOrigin tagOrigin dependencyOrigin : Nat

open TokenOwnedObservation public

data LocalHeadAddress : Set where
  selfHead : LocalHeadAddress
  headAtLocalOrdinal : Nat → LocalHeadAddress

record TokenInFibre : Set where
  constructor tokenInFibre
  field
    observation : TokenOwnedObservation
    headAddress : LocalHeadAddress

open TokenInFibre public

record SentenceFibre : Set where
  constructor sentenceFibre
  field
    semanticFibreIdentity : Nat
    authorityFibreIdentity : Nat
    sentenceOrdinal : Nat
    baseChar : Nat
    tokens : List TokenInFibre

open SentenceFibre public

------------------------------------------------------------------------
-- Solver/path address.
--
-- A branch choice is bounded by the number of branch options at that solver
-- step.  A path is a list of such small local choices; no corpus-global branch
-- candidate id is intrinsic to the semantic address.
------------------------------------------------------------------------

record BranchStepAddress : Set where
  constructor branchStepAddress
  field
    optionCount : Nat
    selectedOption : Nat
    selectedWithinOptions : suc selectedOption ≤ᶜ optionCount

open BranchStepAddress public

BranchPathAddress : Set
BranchPathAddress = List BranchStepAddress

record IdentityCoordinates : Set where
  constructor identityCoordinates
  field
    semanticIdentity : Nat
    authorityIdentity : Nat
    fibreAddress : FibreAddress
    solverPath : BranchPathAddress

open IdentityCoordinates public

------------------------------------------------------------------------
-- Boundary: an independent corpus-global surrogate is optional physical
-- machinery, not demanded by the token/fibre semantics.
------------------------------------------------------------------------

data IndependentGlobalTokenSurrogateRequired : Set where

data IndependentGlobalBranchSurrogateRequired : Set where

fibreAddressDoesNotRequireIndependentGlobalTokenSurrogate :
  IndependentGlobalTokenSurrogateRequired → ⊥
fibreAddressDoesNotRequireIndependentGlobalTokenSurrogate ()

branchPathDoesNotRequireIndependentGlobalBranchSurrogate :
  IndependentGlobalBranchSurrogateRequired → ⊥
branchPathDoesNotRequireIndependentGlobalBranchSurrogate ()
