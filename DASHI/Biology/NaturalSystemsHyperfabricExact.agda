module DASHI.Biology.NaturalSystemsHyperfabricExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric
import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as ReactionDiffusion
import DASHI.Biology.NaturalGrowthAlgorithmAtlas as Growth
import DASHI.Biology.Ecology.EcologicalInteractionDynamics as Ecology

------------------------------------------------------------------------
-- A common typed architecture for finite examples from population dynamics,
-- diffusion, chemistry, morphogenesis, multiway rewriting, and forest
-- symbiosis.  The imported repository modules retain their richer domain
-- boundaries; this file supplies the shared finite transition spine.

data NaturalLayer : Set where
  atomicLayer : NaturalLayer
  chemicalLayer : NaturalLayer
  cellularLayer : NaturalLayer
  tissueLayer : NaturalLayer
  organismLayer : NaturalLayer
  ecologicalLayer : NaturalLayer
  symbolicLayer : NaturalLayer

data CouplingKind : Set where
  diffusionCoupling : CouplingKind
  reactionCoupling : CouplingKind
  bioelectricCoupling : CouplingKind
  mechanicalCoupling : CouplingKind
  resourceCoupling : CouplingKind
  signallingCoupling : CouplingKind
  competitiveCoupling : CouplingKind
  symbioticCoupling : CouplingKind

record NaturalHyperfabricCell : Set where
  constructor naturalHyperfabricCell
  field
    layer : NaturalLayer
    localState : Nat
    resource : Nat
    residual : Nat
    activeCouplings : List CouplingKind

open NaturalHyperfabricCell public

------------------------------------------------------------------------
-- Logistic population map at carrying-capacity normalization four.

logisticFour : Nat → Nat
logisticFour x = x * (4 ∸ x)

logisticAtZero : logisticFour 0 ≡ 0
logisticAtZero = refl

logisticAtOne : logisticFour 1 ≡ 3
logisticAtOne = refl

logisticAtTwo : logisticFour 2 ≡ 4
logisticAtTwo = refl

logisticAtThree : logisticFour 3 ≡ 3
logisticAtThree = refl

logisticAtFour : logisticFour 4 ≡ 0
logisticAtFour = refl

------------------------------------------------------------------------
-- Finite diffusion and reaction witnesses.

record ThreeCompartmentField : Set where
  constructor threeCompartmentField
  field
    leftMass : Nat
    middleMass : Nat
    rightMass : Nat

open ThreeCompartmentField public

moveOneLeftToMiddle : ThreeCompartmentField → ThreeCompartmentField
moveOneLeftToMiddle (threeCompartmentField zero b c) =
  threeCompartmentField zero b c
moveOneLeftToMiddle (threeCompartmentField (suc a) b c) =
  threeCompartmentField a (suc b) c

canonicalConcentrationGradient : ThreeCompartmentField
canonicalConcentrationGradient = threeCompartmentField 3 0 0

firstDiffusionStep :
  moveOneLeftToMiddle canonicalConcentrationGradient
  ≡ threeCompartmentField 2 1 0
firstDiffusionStep = refl

record ActivatorInhibitorState : Set where
  constructor activatorInhibitorState
  field
    activator : Nat
    inhibitor : Nat
    availableMaterial : Nat

open ActivatorInhibitorState public

reactionStep : ActivatorInhibitorState → ActivatorInhibitorState
reactionStep (activatorInhibitorState a i zero) =
  activatorInhibitorState a i zero
reactionStep (activatorInhibitorState a i (suc material)) =
  activatorInhibitorState (suc a) (suc i) material

canonicalReactionStep :
  reactionStep (activatorInhibitorState 0 0 3)
  ≡ activatorInhibitorState 1 1 2
canonicalReactionStep = refl

------------------------------------------------------------------------
-- Bioelectric target-state abstraction in the same typed carrier.

data MorphologicalTarget : Set where
  targetA : MorphologicalTarget
  targetB : MorphologicalTarget
  targetC : MorphologicalTarget

record BioelectricTargetState : Set where
  constructor bioelectricTargetState
  field
    voltagePatternCode : Nat
    target : MorphologicalTarget
    perturbationDepth : Nat
    repairEnabled : Bool

open BioelectricTargetState public

repairStep : BioelectricTargetState → BioelectricTargetState
repairStep (bioelectricTargetState code goal zero enabled) =
  bioelectricTargetState code goal zero enabled
repairStep (bioelectricTargetState code goal (suc depth) false) =
  bioelectricTargetState code goal (suc depth) false
repairStep (bioelectricTargetState code goal (suc depth) true) =
  bioelectricTargetState code goal depth true

canonicalBioelectricRepair :
  repairStep (bioelectricTargetState 9 targetB 2 true)
  ≡ bioelectricTargetState 9 targetB 1 true
canonicalBioelectricRepair = refl

------------------------------------------------------------------------
-- Wolfram-style multiway rewriting with DASHI path residual.

data RewriteOrder : Set where
  leftThenRight : RewriteOrder
  rightThenLeft : RewriteOrder

record MultiwayResult : Set where
  constructor multiwayResult
  field
    visibleEndpoint : Nat
    pathResidual : Nat
    order : RewriteOrder

open MultiwayResult public

executeMultiway : RewriteOrder → MultiwayResult
executeMultiway leftThenRight = multiwayResult 3 1 leftThenRight
executeMultiway rightThenLeft = multiwayResult 3 2 rightThenLeft

multiwayPathsShareVisibleEndpoint :
  visibleEndpoint (executeMultiway leftThenRight)
  ≡ visibleEndpoint (executeMultiway rightThenLeft)
multiwayPathsShareVisibleEndpoint = refl

multiwayPathsRetainDifferentResiduals :
  pathResidual (executeMultiway leftThenRight) ≡ 1
  ×
  pathResidual (executeMultiway rightThenLeft) ≡ 2
multiwayPathsRetainDifferentResiduals = refl , refl

------------------------------------------------------------------------
-- Forest/mycorrhizal multiplex typing.

data ForestChannel : Set where
  carbonChannel : ForestChannel
  nitrogenChannel : ForestChannel
  waterChannel : ForestChannel
  chemicalSignalChannel : ForestChannel
  pathogenChannel : ForestChannel
  competitionChannel : ForestChannel

record ForestTransfer : Set where
  constructor forestTransfer
  field
    channel : ForestChannel
    amount : Nat
    donorResourceAfter : Nat
    receiverResourceAfter : Nat
    mutualBenefitEstablished : Bool

open ForestTransfer public

canonicalCarbonTransfer : ForestTransfer
canonicalCarbonTransfer =
  forestTransfer carbonChannel 1 4 3 false

carbonTransferDoesNotDefinitionallyEstablishMutualBenefit :
  mutualBenefitEstablished canonicalCarbonTransfer ≡ false
carbonTransferDoesNotDefinitionallyEstablishMutualBenefit = refl

record NaturalSystemsBoundary : Set where
  constructor naturalSystemsBoundary
  field
    oneEquationExplainsAllNaturalLayers : Bool
    oneEquationExplainsAllNaturalLayersIsFalse :
      oneEquationExplainsAllNaturalLayers ≡ false

    deterministicLogisticDynamicsAreAlwaysSimple : Bool
    deterministicLogisticDynamicsAreAlwaysSimpleIsFalse :
      deterministicLogisticDynamicsAreAlwaysSimple ≡ false

    bioelectricPatternIsSoleMorphogeneticCause : Bool
    bioelectricPatternIsSoleMorphogeneticCauseIsFalse :
      bioelectricPatternIsSoleMorphogeneticCause ≡ false

    branchMergingErasesPathResidual : Bool
    branchMergingErasesPathResidualIsFalse :
      branchMergingErasesPathResidual ≡ false

    materialTransferEntailsAltruisticSymbiosis : Bool
    materialTransferEntailsAltruisticSymbiosisIsFalse :
      materialTransferEntailsAltruisticSymbiosis ≡ false

open NaturalSystemsBoundary public

canonicalNaturalSystemsBoundary : NaturalSystemsBoundary
canonicalNaturalSystemsBoundary =
  naturalSystemsBoundary false refl false refl false refl false refl false refl
