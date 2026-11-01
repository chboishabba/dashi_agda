module DASHI.Puzzles.RubiksPhasicState where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finite Rubik carrier with a canonical phasic lift.
--
-- This module does not identify U(1) with floating-point complex numbers.
-- Phase is an abstract carrier equipped with the exact operations required by
-- M3/M6/M9.  Concrete roots-of-unity and numerical visualisations may be
-- supplied by an implementation instance.
------------------------------------------------------------------------

record PhaseStructure : Set₁ where
  field
    Phase : Set
    one : Phase
    multiply : Phase → Phase → Phase
    inverse : Phase → Phase
    distanceToOne : Phase → Nat

record RubiksIndexing : Set₁ where
  field
    CornerSlot : Set
    CornerIdentity : Set
    EdgeSlot : Set
    EdgeIdentity : Set
    FaceGenerator : Set

record Assignment (Slot Identity : Set) : Set₁ where
  field
    weight : Slot → Identity → Nat
    rowOneHot : Bool
    columnOneHot : Bool

record M3Corner
  (P : PhaseStructure)
  (I : RubiksIndexing) : Set₁ where
  open PhaseStructure P
  open RubiksIndexing I
  field
    slot : CornerSlot
    identityMass : CornerIdentity → Nat
    twistPhase : Phase

record M3Edge
  (P : PhaseStructure)
  (I : RubiksIndexing) : Set₁ where
  open PhaseStructure P
  open RubiksIndexing I
  field
    slot : EdgeSlot
    identityMass : EdgeIdentity → Nat
    flipPhase : Phase

record M6Transport
  (P : PhaseStructure)
  (Site : Set) : Set₁ where
  open PhaseStructure P
  field
    source : Site
    target : Site
    relativePhase : Phase
    assignmentOverlap : Nat

record M9Holonomy
  (P : PhaseStructure)
  (Site : Set) : Set₁ where
  open PhaseStructure P
  field
    first : Site
    second : Site
    third : Site
    fourth : Site
    boundaryPhase : Phase
    scalarDefect : Nat

record RubiksM9State
  (P : PhaseStructure)
  (I : RubiksIndexing) : Set₁ where
  open PhaseStructure P
  open RubiksIndexing I
  field
    cornerAssignment : Assignment CornerSlot CornerIdentity
    edgeAssignment : Assignment EdgeSlot EdgeIdentity
    cornerPhase : CornerSlot → Phase
    edgePhase : EdgeSlot → Phase

    cornerPhasePinnedToThirdRoots : Bool
    edgePhasePinnedToSecondRoots : Bool
    cornerTwistClosure : Bool
    edgeFlipClosure : Bool
    permutationParityMatched : Bool

    cornerTransport : CornerSlot → CornerSlot → M6Transport P CornerSlot
    edgeTransport : EdgeSlot → EdgeSlot → M6Transport P EdgeSlot

    cornerHolonomy :
      CornerSlot → CornerSlot → CornerSlot → CornerSlot →
      M9Holonomy P CornerSlot
    edgeHolonomy :
      EdgeSlot → EdgeSlot → EdgeSlot → EdgeSlot →
      M9Holonomy P EdgeSlot

  assignmentClosed : Bool
  assignmentClosed =
    Assignment.rowOneHot cornerAssignment
    ∧ Assignment.columnOneHot cornerAssignment
    ∧ Assignment.rowOneHot edgeAssignment
    ∧ Assignment.columnOneHot edgeAssignment
    where
      infixr 6 _∧_
      _∧_ : Bool → Bool → Bool
      true ∧ b = b
      false ∧ _ = false

  orientationClosed : Bool
  orientationClosed =
    cornerPhasePinnedToThirdRoots
    ∧ edgePhasePinnedToSecondRoots
    ∧ cornerTwistClosure
    ∧ edgeFlipClosure
    where
      infixr 6 _∧_
      _∧_ : Bool → Bool → Bool
      true ∧ b = b
      false ∧ _ = false

  admissible : Bool
  admissible = assignmentClosed ∧ orientationClosed ∧ permutationParityMatched
    where
      infixr 6 _∧_
      _∧_ : Bool → Bool → Bool
      true ∧ b = b
      false ∧ _ = false

------------------------------------------------------------------------
-- The M-level hierarchy is rank-unbounded: M3 is local state, M6 is paired
-- transport, M9 is a closed move/plaquette boundary, and further levels are
-- finite words of M3 channels with contraction maps supplied by the kernel.
------------------------------------------------------------------------

record FiniteRankLift : Set₁ where
  field
    rank : Nat
    arity : Nat
    contractionAvailable : Bool
    generatorActionAvailable : Bool

record UnboundedMHierarchy : Set₁ where
  field
    M3 : FiniteRankLift
    M6 : FiniteRankLift
    M9 : FiniteRankLift
    liftAt : Nat → FiniteRankLift
    nineOfNineIterates : Bool
    noFiniteRankCeiling : Bool

rubiksStateStatement : String
rubiksStateStatement =
  "A legal Rubik state is a permutation vertex paired with corner mu3 and "
  ++ "edge mu2 phases, subject to twist, flip and parity closure. M6 records "
  ++ "relative transport; M9 records closed-boundary holonomy and its scalar "
  ++ "defect contraction."
