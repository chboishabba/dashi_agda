module DASHI.Foundations.InverseLimitClopenRefinement where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

record RefinementTower : Set₁ where
  field
    State : Nat → Set
    project : (depth : Nat) → State (suc depth) → State depth

open RefinementTower public

record CompatibleThread (tower : RefinementTower) : Set₁ where
  field
    atDepth : (depth : Nat) → State tower depth
    compatible :
      (depth : Nat) →
      project tower depth (atDepth (suc depth)) ≡ atDepth depth

open CompatibleThread public

InverseLimit : RefinementTower → Set₁
InverseLimit = CompatibleThread

record NestedClopenChain (Point : Set) : Set₁ where
  field
    Ball : Nat → Point → Set
    centre : Point
    nested :
      (depth : Nat) →
      (point : Point) →
      Ball (suc depth) point →
      Ball depth point

open NestedClopenChain public

record CompleteClopenAuthority
    (tower : RefinementTower)
    (Point : Set)
    (chain : NestedClopenChain Point) : Set₁ where
  field
    decodeThread : InverseLimit tower → Point
    encodePoint : Point → InverseLimit tower
    decodeEncode : ∀ point → decodeThread (encodePoint point) ≡ point
    encodeDecode : ∀ thread → encodePoint (decodeThread thread) ≡ thread
    intersectionSingleton : Set
    ultrametricComplete : Set

open CompleteClopenAuthority public
