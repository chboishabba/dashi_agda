{-# OPTIONS --safe #-}
module DASHI.Cognition.CCDCOEMultiplexGraphCutCoreExact where

-- Structural graph theorem, intentionally independent of any psychological,
-- military, clinical, political, observational or measurement interpretation.
-- All vertices and edges are typed; every edge is evidence-bearing.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data Void : Set where

trueNotFalse : true ≡ false → Void
trueNotFalse ()

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

chainEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
chainEq refl equality = equality

record LayerNode (Actor Layer : Set) : Set where
  constructor node
  field
    actor : Actor
    layer : Layer

-- A common actor carrier is reused in every layer. Neither local links
-- nor cross-layer links are inferred from the other kind of link.
record Multiplex (Actor Layer : Set) : Set₁ where
  field
    within : Layer → Actor → Actor → Set
    between : Layer → Layer → Actor → Actor → Set

data NetworkEdge {Actor Layer : Set}
    (M : Multiplex Actor Layer) :
    LayerNode Actor Layer → LayerNode Actor Layer → Set where
  local : ∀ {a b l} →
    Multiplex.within M l a b →
    NetworkEdge M (node a l) (node b l)
  cross : ∀ {a b l k} →
    Multiplex.between M l k a b →
    NetworkEdge M (node a l) (node b k)

-- Path is the proof-bearing reflexive-transitive closure of E.
data Walk {V : Set} (E : V → V → Set) : V → V → Set where
  halt : ∀ {v} → Walk E v v
  advance : ∀ {u v w} → E u v → Walk E v w → Walk E u w

appendWalk :
  ∀ {V : Set} {E : V → V → Set} {u v w} →
  Walk E u v → Walk E v w → Walk E u w
appendWalk halt rest = rest
appendWalk (advance edge prefix) rest =
  advance edge (appendWalk prefix rest)

-- Retain only edges respecting a declared partition. The certificate
-- is edge-local, not a statement that all graphs share this partition.
data Retained {V : Set} (E : V → V → Set)
    (side : V → Bool) : V → V → Set where
  keep : ∀ {u v} → E u v → side u ≡ side v → Retained E side u v

retainedWalkPreservesSide :
  ∀ {V : Set}
  (E : V → V → Set) (side : V → Bool)
  {u v} →
  Walk (Retained E side) u v → side u ≡ side v
retainedWalkPreservesSide E side halt = refl
retainedWalkPreservesSide E side (advance (keep edge equality) rest) =
  chainEq equality (retainedWalkPreservesSide E side rest)

-- If all original edges are side-preserving, any walk can be promoted to
-- a retained walk. This is the criterion an actual cut certificate pays.
retainCertifiedWalk :
  ∀ {V : Set} (E : V → V → Set) (side : V → Bool) →
  (∀ {u v} → E u v → side u ≡ side v) →
  ∀ {u v} →
  Walk E u v → Walk (Retained E side) u v
retainCertifiedWalk E side stable halt = halt
retainCertifiedWalk E side stable (advance edge rest) =
  advance
    (keep edge (stable edge))
    (retainCertifiedWalk E side stable rest)

noRetainedWalkAcrossCut :
  ∀ {V : Set} (E : V → V → Set) (side : V → Bool)
  {u v} →
  side u ≡ true →
  side v ≡ false →
  Walk (Retained E side) u v → Void
noRetainedWalkAcrossCut E side uLeft vRight route =
  trueNotFalse
    (chainEq
      (symEq uLeft)
      (chainEq (retainedWalkPreservesSide E side route) vRight))

-- General, graph-independent disconnection theorem.
noWalkAcrossCertifiedCut :
  ∀ {V : Set} (E : V → V → Set) (side : V → Bool) →
  (∀ {u v} → E u v → side u ≡ side v) →
  ∀ {u v} →
  side u ≡ true →
  side v ≡ false →
  Walk E u v → Void
noWalkAcrossCertifiedCut E side stable uLeft vRight route =
  noRetainedWalkAcrossCut E side uLeft vRight
    (retainCertifiedWalk E side stable route)
