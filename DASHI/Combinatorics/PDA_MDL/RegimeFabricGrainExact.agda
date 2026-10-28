module DASHI.Combinatorics.PDA_MDL.RegimeFabricGrainExact where

-- O: Add fabric and grain regime moves to a PDA world.
-- R: Reuse the existing PDA and natural-number code-length carriers.
-- C: Index panels by their position in an assignment list.
-- S: Cost coefficients are model inputs, not physical material laws.
-- L: This leaf changes only the PDA_MDL regime surface.
-- P: Both moves are total. Their costs and observable states are explicit.
-- G: Reuse the original PDA_MDL authors' definitions without copying them.
-- F: The finite equations below are definitionally checked by Agda.

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import DASHI.Combinatorics.PDA_MDL.PDA using (PDA)
open import Agda.Builtin.Bool using (Bool; true; false)

data Grain : Set where
  alongWarp : Grain
  acrossWeft : Grain
  bias : Grain

rotateGrain : Grain → Grain
rotateGrain alongWarp = acrossWeft
rotateGrain acrossWeft = bias
rotateGrain bias = alongWarp

rotateGrainThree : (g : Grain) →
  rotateGrain (rotateGrain (rotateGrain g)) ≡ g
rotateGrainThree alongWarp = refl
rotateGrainThree acrossWeft = refl
rotateGrainThree bias = refl

record Assignment : Set where
  constructor assignment
  field
    fabricCode : Nat
    grain : Grain
open Assignment public

record RegimeState : Set where
  constructor regimeState
  field
    panels : List Assignment
    editCost : CodeLength
open RegimeState public

-- The index is zero-based. Out-of-range moves preserve the panel list.
switchAt : Nat → Nat → List Assignment → List Assignment
switchAt zero newFabric [] = []
switchAt zero newFabric (assignment old g ∷ rest) =
  assignment newFabric g ∷ rest
switchAt (suc i) newFabric [] = []
switchAt (suc i) newFabric (a ∷ rest) =
  a ∷ switchAt i newFabric rest

rotateAt : Nat → List Assignment → List Assignment
rotateAt zero [] = []
rotateAt zero (assignment f g ∷ rest) =
  assignment f (rotateGrain g) ∷ rest
rotateAt (suc i) [] = []
rotateAt (suc i) (a ∷ rest) =
  a ∷ rotateAt i rest

record RegimeWeights : Set where
  constructor regimeWeights
  field
    switchCodeCost : CodeLength
    rotationCodeCost : CodeLength
    fabricDescriptionWeight : Nat
    grainMismatchWeight : Nat
    unsupportedFabricWeight : Nat
open RegimeWeights public

-- A policy is explicit. The Boolean guard is not a proof of sewability.
record FabricPolicy : Set₁ where
  field
    supported : Nat → Grain → Bool
    referenceGrain : Nat → Grain
open FabricPolicy public

grainDifferent : Grain → Grain → Bool
grainDifferent alongWarp alongWarp = false
grainDifferent acrossWeft acrossWeft = false
grainDifferent bias bias = false
grainDifferent _ _ = true

boolPenalty : Nat → Bool → Nat
boolPenalty cost true = zero
boolPenalty cost false = cost

grainPenalty : Nat → Bool → Nat
grainPenalty cost true = cost
grainPenalty cost false = zero

assignmentCost : FabricPolicy → RegimeWeights → Assignment → CodeLength
assignmentCost policy weights a =
  fabricDescriptionWeight weights * fabricCode a
  + grainPenalty (grainMismatchWeight weights)
      (grainDifferent (grain a) (referenceGrain policy (fabricCode a)))
  + boolPenalty (unsupportedFabricWeight weights)
      (supported policy (fabricCode a) (grain a))

panelsCost : FabricPolicy → RegimeWeights → List Assignment → CodeLength
panelsCost policy weights [] = zero
panelsCost policy weights (a ∷ as) =
  assignmentCost policy weights a + panelsCost policy weights as

regimeMDL : FabricPolicy → RegimeWeights → RegimeState → CodeLength
regimeMDL policy weights s =
  editCost s + panelsCost policy weights (panels s)

-- An edit is encoded even when the index is out of range.
-- This prevents a free no-op from hiding a model description cost.
switch_fabric : RegimeWeights → Nat → Nat → RegimeState → RegimeState
switch_fabric weights i f (regimeState as cost) =
  regimeState (switchAt i f as) (cost + switchCodeCost weights)

rotate_grain : RegimeWeights → Nat → RegimeState → RegimeState
rotate_grain weights i (regimeState as cost) =
  regimeState (rotateAt i as) (cost + rotationCodeCost weights)

-- An existing PDA consumer can observe this richer world without a new
-- observer foundation. Admissibility remains the policy owner's obligation.
record RegimePDA (O : Set) : Set₁ where
  field
    lens : PDA RegimeState O
    policy : FabricPolicy
    weights : RegimeWeights
open RegimePDA public

regimeObservation : ∀ {O} → RegimePDA O → RegimeState → O
regimeObservation r = PDA.observe (lens r)

totalMDL : ∀ {O} → RegimePDA O → RegimeState → CodeLength
totalMDL r s = PDA.costPDA (lens r) + regimeMDL (policy r) (weights r) s

switchPreservesGrainAtHead :
  (newFabric oldFabric : Nat) (g : Grain) (rest : List Assignment) →
  grain (AssignmentHead (switchAt zero newFabric (assignment oldFabric g ∷ rest)))
  ≡ g
  where
    AssignmentHead : List Assignment → Assignment
    AssignmentHead [] = assignment zero alongWarp
    AssignmentHead (x ∷ xs) = x
switchPreservesGrainAtHead newFabric oldFabric g rest = refl

rotatePreservesFabricAtHead :
  (f : Nat) (g : Grain) (rest : List Assignment) →
  fabricCode (headAssignment (rotateAt zero (assignment f g ∷ rest))) ≡ f
  where
    headAssignment : List Assignment → Assignment
    headAssignment [] = assignment zero alongWarp
    headAssignment (a ∷ as) = a
rotatePreservesFabricAtHead f g rest = refl

-- Regression fixtures. These check the exact state transitions.
sampleWeights : RegimeWeights
sampleWeights = regimeWeights 2 1 1 3 5

sampleState : RegimeState
sampleState = regimeState (assignment 0 alongWarp ∷
  assignment 1 acrossWeft ∷ []) 0

switchExample :
  panels (switch_fabric sampleWeights 0 2 sampleState)
  ≡ assignment 2 alongWarp ∷ assignment 1 acrossWeft ∷ []
switchExample = refl

rotateExample :
  panels (rotate_grain sampleWeights 1 sampleState)
  ≡ assignment 0 alongWarp ∷ assignment 1 bias ∷ []
rotateExample = refl

switchEditCostExample :
  editCost (switch_fabric sampleWeights 0 2 sampleState) ≡ 2
switchEditCostExample = refl

rotateEditCostExample :
  editCost (rotate_grain sampleWeights 1 sampleState) ≡ 1
rotateEditCostExample = refl

outOfRangeSwitch :
  panels (switch_fabric sampleWeights 4 2 sampleState) ≡ panels sampleState
outOfRangeSwitch = refl

outOfRangeRotate :
  panels (rotate_grain sampleWeights 4 sampleState) ≡ panels sampleState
outOfRangeRotate = refl
