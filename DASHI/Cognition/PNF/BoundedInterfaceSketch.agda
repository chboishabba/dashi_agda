module DASHI.Cognition.PNF.BoundedInterfaceSketch where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.BoundedMDLPlanner using
  (PathStorage; constantBackpointers)

------------------------------------------------------------------------
-- Backpointers bound retained dynamic-programming state, but they do not make
-- exact interface sketches constant size.  The current runtime joins three
-- exact key families: object, factor and demand keys.  C is therefore an
-- explicit per-family interface budget rather than an erased implementation
-- constant.
------------------------------------------------------------------------

data SketchStorage : Set where
  unboundedExactKeys boundedExactKeys constantSummary : SketchStorage

sketchJoinWork : Nat → Nat
sketchJoinWork capacity = capacity +ᶜ (capacity +ᶜ capacity)

candidateStateWork : Nat → Nat → Nat → Nat
candidateStateWork regions window beam =
  regions *ᶜ (window *ᶜ beam)

exactSketchJoinWork : Nat → Nat → Nat → Nat
exactSketchJoinWork regions window capacity =
  regions *ᶜ (window *ᶜ sketchJoinWork capacity)

boundedPlannerWork : Nat → Nat → Nat → Nat → Nat
boundedPlannerWork zero window beam capacity = zero
boundedPlannerWork (suc regions) window beam capacity =
  (window *ᶜ (sketchJoinWork capacity +ᶜ beam)) +ᶜ
  boundedPlannerWork regions window beam capacity

boundedPlannerWorkClosed : ∀ regions window beam capacity →
  boundedPlannerWork regions window beam capacity ≡
    regions *ᶜ (window *ᶜ (sketchJoinWork capacity +ᶜ beam))
boundedPlannerWorkClosed zero window beam capacity = refl
boundedPlannerWorkClosed (suc regions) window beam capacity
  rewrite boundedPlannerWorkClosed regions window beam capacity = refl

record InterfaceSketchBudget (capacity : Nat) : Set where
  constructor interfaceSketchBudget
  field
    objectKeyCount factorKeyCount demandKeyCount : Nat
    objectKeysBounded : objectKeyCount ≤ᶜ capacity
    factorKeysBounded : factorKeyCount ≤ᶜ capacity
    demandKeysBounded : demandKeyCount ≤ᶜ capacity

open InterfaceSketchBudget public

record EndToEndPlannerCertificate
    (regions window beam capacity : Nat) : Set where
  constructor endToEndPlannerCertificate
  field
    pathStorage : PathStorage
    pathStorageIsConstant : pathStorage ≡ constantBackpointers
    sketchStorage : SketchStorage
    sketchStorageIsBoundedExact : sketchStorage ≡ boundedExactKeys
    candidateBound : Nat
    candidateBoundIsNWB :
      candidateBound ≡ regions *ᶜ (window *ᶜ beam)
    exactSketchBound : Nat
    exactSketchBoundIsNW3C :
      exactSketchBound ≡
        regions *ᶜ (window *ᶜ sketchJoinWork capacity)
    combinedWorkBound : Nat
    combinedWorkBoundClosed :
      combinedWorkBound ≡
        regions *ᶜ
          (window *ᶜ (sketchJoinWork capacity +ᶜ beam))

open EndToEndPlannerCertificate public

canonicalBoundedPlannerCertificate : ∀ regions window beam capacity →
  EndToEndPlannerCertificate regions window beam capacity
canonicalBoundedPlannerCertificate regions window beam capacity =
  endToEndPlannerCertificate
    constantBackpointers
    refl
    boundedExactKeys
    refl
    (regions *ᶜ (window *ᶜ beam))
    refl
    (regions *ᶜ (window *ᶜ sketchJoinWork capacity))
    refl
    (regions *ᶜ
      (window *ᶜ (sketchJoinWork capacity +ᶜ beam)))
    refl

unboundedExactKeysAreNotBounded :
  unboundedExactKeys ≡ boundedExactKeys → ⊥
unboundedExactKeysAreNotBounded ()

unboundedRuntimeCannotUseBoundedCertificate :
  ∀ regions window beam capacity →
  unboundedExactKeys ≡
    sketchStorage
      (canonicalBoundedPlannerCertificate
        regions window beam capacity) → ⊥
unboundedRuntimeCannotUseBoundedCertificate
  regions window beam capacity proof =
  unboundedExactKeysAreNotBounded proof

------------------------------------------------------------------------
-- Interpretation:
--
--   candidate states       = N * W * B
--   three exact key unions = N * W * 3C
--   combined bound         = N * W * (3C + B)
--
-- Fixed W, B and C give linear work in N.  Without a runtime witness for C,
-- only the candidate-state and retained-backpointer claims are certified.
------------------------------------------------------------------------
