module DASHI.Core.ExplodedGraphGeometry where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Core.NonlinearExplodedSparsity
open import DASHI.Core.QuantitativeNonlinearSparsity

------------------------------------------------------------------------
-- Graph paths and exact distances
------------------------------------------------------------------------

record GraphGeometry (X : Set) : Set₁ where
  field
    edge : X → X → Set

open GraphGeometry public

data Path {X : Set} (G : GraphGeometry X) : X → X → Nat → Set where
  here : (x : X) → Path G x x zero
  step : {x y z : X} {n : Nat} →
    edge G x y → Path G y z n → Path G x z (suc n)

Connected : {X : Set} → GraphGeometry X → X → X → Set
Connected G x y = Σ Nat (λ n → Path G x y n)

record ExactDistance
  {X : Set}
  (G : GraphGeometry X)
  (x y : X)
  (n : Nat) : Set where
  field
    path : Path G x y n
    noShorter : (m : Nat) → m < n → ¬ Path G x y m

open ExactDistance public

------------------------------------------------------------------------
-- Signed induced geometry
------------------------------------------------------------------------

HasSign : {X : Set} → State X → Trit → X → Set
HasSign s t x = s x ≡ t

InducedEdge :
  {X : Set} → GraphGeometry X → State X → Trit → X → X → Set
InducedEdge G s t x y = edge G x y × (HasSign s t x × HasSign s t y)

record SignedComponent
  {X : Set}
  (G : GraphGeometry X)
  (s : State X)
  (t : Trit) : Set₁ where
  field
    member : X → Set
    root : X
    rootMember : member root
    signed : (x : X) → member x → HasSign s t x
    internallyConnected : (x : X) → member x →
      Σ Nat (λ n → Path G root x n)
    maximal : (x : X) → HasSign s t x → Connected G root x → member x

open SignedComponent public

record LargestSignedComponent
  {X : Set}
  (C : FiniteCounting X)
  (G : GraphGeometry X)
  (s : State X)
  (t : Trit) : Set₁ where
  field
    component : SignedComponent G s t
    largest : (other : SignedComponent G s t) →
      count C (SignedComponent.member other) ≤
      count C (SignedComponent.member component)

------------------------------------------------------------------------
-- Shells and source affiliation
------------------------------------------------------------------------

ShellAt :
  {X : Set} → GraphGeometry X → (X → Set) → Nat → X → Set
ShellAt G Source n x =
  Σ X (λ y → Source y × ExactDistance G x y n)

BoundaryShell :
  {X : Set} → GraphGeometry X → State X → Nat → X → Set
BoundaryShell G s n x =
  (s x ≡ zer) × ShellAt G (λ y → ¬ (s y ≡ zer)) n x

record SingleSourceAffiliation
  {X : Set}
  (G : GraphGeometry X)
  (Source : X → Set)
  (x : X) : Set₁ where
  field
    source : X
    sourceMember : Source source
    distance : Nat
    exactDistance : ExactDistance G x source distance
    uniqueNearest : (other : X) → Source other →
      (m : Nat) → ExactDistance G x other m → distance ≤ m

record MultiSourceAffiliation
  {X : Set}
  (G : GraphGeometry X)
  (Source : X → Set)
  (x : X) : Set₁ where
  field
    left right : X
    leftSource : Source left
    rightSource : Source right
    distinct : ¬ (left ≡ right)
    distance : Nat
    leftExact : ExactDistance G x left distance
    rightExact : ExactDistance G x right distance

------------------------------------------------------------------------
-- Neutral islands and defect shells
------------------------------------------------------------------------

record NeutralIsland
  {X : Set}
  (G : GraphGeometry X)
  (s : State X) : Set₁ where
  field
    member : X → Set
    inhabited : Σ X member
    neutral : (x : X) → member x → s x ≡ zer
    internallyConnected : (x y : X) → member x → member y → Connected G x y
    isolatedFromActive : (x y : X) → member x → edge G x y → s y ≡ zer

DefectShell :
  {X L : Set} → GraphGeometry X →
  (K : ThresholdKernel X L) → State X → Nat → X → Set
DefectShell G K s n x =
  ShellAt G (KernelDefect K s) n x

------------------------------------------------------------------------
-- Sprint-style geometry certificate
------------------------------------------------------------------------

record ExplodedGeometryCertificate
  {X L : Set}
  (C : FiniteCounting X)
  (G : GraphGeometry X)
  (K : ThresholdKernel X L)
  (s : State X) : Set₁ where
  field
    positiveComponents : List (SignedComponent G s pos)
    negativeComponents : List (SignedComponent G s neg)
    neutralIslands : List (NeutralIsland G s)
    largestPositive : LargestSignedComponent C G s pos
    shellRadius : Nat
    everyNeutralAffiliated :
      (x : X) → s x ≡ zer →
      SingleSourceAffiliation G (λ y → s y ≡ pos) x ⊎
      MultiSourceAffiliation G (λ y → s y ≡ pos) x
    everyDefectInShell :
      (x : X) → KernelDefect K s x →
      BoundaryShell G s shellRadius x
