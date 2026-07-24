module DASHI.Foundations.ConstraintClopenRefinement where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Constraint order and state-region order are contravariant.
------------------------------------------------------------------------

record ConstraintSystem : Set₁ where
  field
    State : Set
    Constraint : Set
    satisfies : State → Constraint → Set

open ConstraintSystem public

record FineExtendsCoarse
    (S : ConstraintSystem)
    (coarse fine : Constraint S) : Set₁ where
  field
    forgetConstraint :
      ∀ {state} →
      satisfies S state fine →
      satisfies S state coarse

open FineExtendsCoarse public

AdmissibleRegion :
  (S : ConstraintSystem) →
  Constraint S →
  Set
AdmissibleRegion S constraint =
  Σ (State S) (λ state → satisfies S state constraint)

refinedRegionInclusion :
  ∀ {S coarse fine} →
  FineExtendsCoarse S coarse fine →
  AdmissibleRegion S fine →
  AdmissibleRegion S coarse
refinedRegionInclusion refinement (state , fineWitness) =
  state , forgetConstraint refinement fineWitness

------------------------------------------------------------------------
-- Resolution-indexed descriptions and their projection fibres.
------------------------------------------------------------------------

record RefinementSystem : Set₁ where
  field
    Level : Set
    StateAt : Level → Set
    Refines : Level → Level → Set
    project :
      ∀ {fine coarse} →
      Refines fine coarse →
      StateAt fine →
      StateAt coarse

open RefinementSystem public

FibreAt :
  (R : RefinementSystem) →
  ∀ {fine coarse} →
  Refines R fine coarse →
  StateAt R coarse →
  Set
FibreAt R {fine} refinement coarseState =
  Σ (StateAt R fine) (λ fineState →
    project R refinement fineState ≡ coarseState)

------------------------------------------------------------------------
-- Clopen-ball refinement.  Openness/closedness are explicit authority fields;
-- they are not inferred from a name or from digit counting alone.
------------------------------------------------------------------------

data BTBranch : Set where
  negativeBranch : BTBranch
  zeroBranch : BTBranch
  positiveBranch : BTBranch

record ClopenBallSystem : Set₁ where
  field
    Point : Set
    Depth : Set
    nextDepth : Depth → Depth

    Ball : Depth → Point → Point → Set

    ballOpen :
      (depth : Depth) →
      (centre : Point) →
      Set

    ballClosed :
      (depth : Depth) →
      (centre : Point) →
      Set

    childCentre :
      BTBranch →
      (depth : Depth) →
      Point →
      Point

    childContained :
      (branch : BTBranch) →
      (depth : Depth) →
      (centre point : Point) →
      Ball (nextDepth depth) (childCentre branch depth centre) point →
      Ball depth centre point

    childCover :
      (depth : Depth) →
      (centre point : Point) →
      Ball depth centre point →
      Σ BTBranch (λ branch →
        Ball (nextDepth depth) (childCentre branch depth centre) point)

open ClopenBallSystem public

record ClopenSupervoxel
    (B : ClopenBallSystem)
    (depth : Depth B)
    (centre : Point B) : Set₁ where
  field
    Weight : Set
    weight : Point B → Weight
    transition : Point B → Point B

    transitionStaysInParent :
      ∀ {point} →
      Ball B depth centre point →
      Ball B depth centre (transition point)

    parentIsOpen : ballOpen B depth centre
    parentIsClosed : ballClosed B depth centre

open ClopenSupervoxel public

------------------------------------------------------------------------
-- The complete-state reading: deeper constraints select nested smaller balls.
------------------------------------------------------------------------

record NestedClopenChain (B : ClopenBallSystem) : Set₁ where
  field
    centre : Point B
    depthAt : Nat → Depth B
    ballAt : Nat → Point B → Set

    ballAtIsCanonical :
      ∀ index point →
      ballAt index point ≡ Ball B (depthAt index) centre point

    deeperContained :
      ∀ index point →
      ballAt (suc index) point →
      ballAt index point

open NestedClopenChain public
