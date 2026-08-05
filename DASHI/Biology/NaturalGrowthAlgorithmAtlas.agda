module DASHI.Biology.NaturalGrowthAlgorithmAtlas where

open import DASHI.Core.Prelude

import DASHI.Biology.MorphogeneticVisualGenerator as Morphogenesis

------------------------------------------------------------------------
-- Exact finite witnesses for distinct natural-growth algorithm families.
--
-- These constructions intentionally preserve causal distinctions between
-- grammar rewriting, environmental attraction, transported inhibition,
-- boundary accretion, diffusion-limited sticking, recursive contraction, and
-- resource-limited structural growth.
--
-- Source-facing references are carried by
-- ConsciousAccessRound3SourceAtlas.agda and MorphogeneticVisualGenerator.agda.

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

------------------------------------------------------------------------
-- L-system: recursive parallel rewriting.

data GrowthSymbol : Set where
  apexSymbol : GrowthSymbol
  internodeSymbol : GrowthSymbol
  leftBranchSymbol : GrowthSymbol
  rightBranchSymbol : GrowthSymbol

rewriteSymbol : GrowthSymbol → List GrowthSymbol
rewriteSymbol apexSymbol =
  internodeSymbol
  ∷ leftBranchSymbol
  ∷ apexSymbol
  ∷ rightBranchSymbol
  ∷ apexSymbol
  ∷ []
rewriteSymbol internodeSymbol = internodeSymbol ∷ []
rewriteSymbol leftBranchSymbol = leftBranchSymbol ∷ []
rewriteSymbol rightBranchSymbol = rightBranchSymbol ∷ []

rewriteWord : List GrowthSymbol → List GrowthSymbol
rewriteWord [] = []
rewriteWord (x ∷ xs) = append (rewriteSymbol x) (rewriteWord xs)

lSystemAxiom : List GrowthSymbol
lSystemAxiom = apexSymbol ∷ []

firstLSystemGeneration : List GrowthSymbol
firstLSystemGeneration = rewriteWord lSystemAxiom

firstLSystemGenerationIsBranched :
  firstLSystemGeneration
  ≡
  internodeSymbol
  ∷ leftBranchSymbol
  ∷ apexSymbol
  ∷ rightBranchSymbol
  ∷ apexSymbol
  ∷ []
firstLSystemGenerationIsBranched = refl

data GrowthContext : Set where
  openContext : GrowthContext
  inhibitedContext : GrowthContext

contextRewrite : GrowthContext → GrowthSymbol → List GrowthSymbol
contextRewrite openContext apexSymbol = rewriteSymbol apexSymbol
contextRewrite inhibitedContext apexSymbol = internodeSymbol ∷ apexSymbol ∷ []
contextRewrite _ x = x ∷ []

contextChangesRewrite :
  contextRewrite openContext apexSymbol
  ≡
  contextRewrite inhibitedContext apexSymbol
  →
  ⊥
contextChangesRewrite ()

record ParametricBud : Set where
  constructor parametricBud
  field
    internodeLength : Nat
    storedEnergy : Nat

open ParametricBud public

growParametricBud : ParametricBud → ParametricBud
growParametricBud (parametricBud length energy) =
  parametricBud (suc length) (energy ∸ 1)

parametricGrowthConsumesEnergy :
  growParametricBud (parametricBud 2 3)
  ≡
  parametricBud 3 2
parametricGrowthConsumesEnergy = refl

------------------------------------------------------------------------
-- Space colonisation: environmental attraction is assigned to growth tips.

data AttractionPoint : Set where
  leftLight : AttractionPoint
  centralLight : AttractionPoint
  rightLight : AttractionPoint

data GrowthTip : Set where
  rootTip : GrowthTip
  leftTip : GrowthTip
  rightTip : GrowthTip

assignedTip : AttractionPoint → GrowthTip
assignedTip leftLight = leftTip
assignedTip centralLight = leftTip
assignedTip rightLight = rightTip

attractionCount : GrowthTip → Nat
attractionCount rootTip = 0
attractionCount leftTip = 2
attractionCount rightTip = 1

selectedColonisingTip : GrowthTip
selectedColonisingTip = leftTip

selectedColonisingTipIsMaximal :
  (t : GrowthTip) →
  attractionCount t ≤ attractionCount selectedColonisingTip
selectedColonisingTipIsMaximal rootTip = z≤n
selectedColonisingTipIsMaximal leftTip = ≤-refl
selectedColonisingTipIsMaximal rightTip = s≤s z≤n

leftTipClaimsTwoAttractors :
  assignedTip leftLight ≡ leftTip
  ×
  assignedTip centralLight ≡ leftTip
leftTipClaimsTwoAttractors = refl , refl

------------------------------------------------------------------------
-- Phyllotactic inhibition: transported activation competes with exclusion by
-- prior primordia.

data PrimordiumSite : Set where
  northSite : PrimordiumSite
  eastSite : PrimordiumSite
  southSite : PrimordiumSite
  westSite : PrimordiumSite

transportedActivation : PrimordiumSite → Nat
transportedActivation northSite = 3
transportedActivation eastSite = 4
transportedActivation southSite = 5
transportedActivation westSite = 4

priorPrimordiumInhibition : PrimordiumSite → Nat
priorPrimordiumInhibition northSite = 2
priorPrimordiumInhibition eastSite = 3
priorPrimordiumInhibition southSite = 1
priorPrimordiumInhibition westSite = 3

phyllotacticScore : PrimordiumSite → Nat
phyllotacticScore s =
  transportedActivation s ∸ priorPrimordiumInhibition s

selectedPrimordiumSite : PrimordiumSite
selectedPrimordiumSite = southSite

selectedPrimordiumScoreIsFour :
  phyllotacticScore selectedPrimordiumSite ≡ 4
selectedPrimordiumScoreIsFour = refl

selectedPrimordiumSiteIsMaximal :
  (s : PrimordiumSite) →
  phyllotacticScore s ≤ phyllotacticScore selectedPrimordiumSite
selectedPrimordiumSiteIsMaximal northSite = s≤s z≤n
selectedPrimordiumSiteIsMaximal eastSite = s≤s z≤n
selectedPrimordiumSiteIsMaximal southSite = ≤-refl
selectedPrimordiumSiteIsMaximal westSite = s≤s z≤n

------------------------------------------------------------------------
-- Eden growth: add the frontier cell with greatest occupied-neighbour support.

data FrontierCell : Set where
  frontierA : FrontierCell
  frontierB : FrontierCell
  frontierC : FrontierCell

occupiedNeighbourCount : FrontierCell → Nat
occupiedNeighbourCount frontierA = 1
occupiedNeighbourCount frontierB = 3
occupiedNeighbourCount frontierC = 2

selectedEdenCell : FrontierCell
selectedEdenCell = frontierB

selectedEdenCellIsMaximal :
  (c : FrontierCell) →
  occupiedNeighbourCount c
  ≤
  occupiedNeighbourCount selectedEdenCell
selectedEdenCellIsMaximal frontierA = s≤s z≤n
selectedEdenCellIsMaximal frontierB = ≤-refl
selectedEdenCellIsMaximal frontierC = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Diffusion-limited aggregation: a random walker sticks on first contact.

data WalkerPosition : Set where
  farPosition : WalkerPosition
  nearPosition : WalkerPosition
  contactPosition : WalkerPosition

data AggregateState : Set where
  seedAggregate : AggregateState
  grownAggregate : AggregateState

walkerStep : WalkerPosition → WalkerPosition
walkerStep farPosition = nearPosition
walkerStep nearPosition = contactPosition
walkerStep contactPosition = contactPosition

stickAt : WalkerPosition → AggregateState → AggregateState
stickAt contactPosition seedAggregate = grownAggregate
stickAt _ aggregate = aggregate

walkerContactsInTwoSteps :
  walkerStep (walkerStep farPosition) ≡ contactPosition
walkerContactsInTwoSteps = refl

firstContactGrowsAggregate :
  stickAt (walkerStep (walkerStep farPosition)) seedAggregate
  ≡
  grownAggregate
firstContactGrowsAggregate = refl

------------------------------------------------------------------------
-- Iterated-function-system contraction depth.

data IFSBranch : Set where
  leftContraction : IFSBranch
  rightContraction : IFSBranch

record IFSPoint : Set where
  constructor ifsPoint
  field
    contractionDepth : Nat
    branch : IFSBranch

open IFSPoint public

contract : IFSBranch → IFSPoint → IFSPoint
contract b (ifsPoint depth oldBranch) =
  ifsPoint (suc depth) b

initialIFSPoint : IFSPoint
initialIFSPoint = ifsPoint 0 leftContraction

threeContractionsHaveDepthThree :
  contractionDepth
    (contract rightContraction
      (contract leftContraction
        (contract rightContraction initialIFSPoint)))
  ≡
  3
threeContractionsHaveDepthThree = refl

------------------------------------------------------------------------
-- Functional-structural growth: resource capture must cover maintenance and
-- the selected growth cost.

record ResourceBudget : Set where
  constructor resourceBudget
  field
    capturedResource : Nat
    maintenanceCost : Nat
    growthCost : Nat

open ResourceBudget public

availableForGrowth : ResourceBudget → Nat
availableForGrowth b =
  capturedResource b ∸ maintenanceCost b

canPay : Nat → Nat → Bool
canPay available zero = true
canPay zero (suc cost) = false
canPay (suc available) (suc cost) =
  canPay available cost

canAffordGrowth : ResourceBudget → Bool
canAffordGrowth b =
  canPay (availableForGrowth b) (growthCost b)

productiveBudget : ResourceBudget
productiveBudget = resourceBudget 5 2 2

starvedBudget : ResourceBudget
starvedBudget = resourceBudget 1 2 1

productiveBudgetCanGrow :
  canAffordGrowth productiveBudget ≡ true
productiveBudgetCanGrow = refl

starvedBudgetCannotGrow :
  canAffordGrowth starvedBudget ≡ false
starvedBudgetCannotGrow = refl

------------------------------------------------------------------------
-- Algorithms can share a morphology class without sharing update law.

data GrowthAlgorithm : Set where
  lSystemAlgorithm : GrowthAlgorithm
  spaceColonisationAlgorithm : GrowthAlgorithm
  phyllotacticAlgorithm : GrowthAlgorithm
  edenAlgorithm : GrowthAlgorithm
  dlaAlgorithm : GrowthAlgorithm
  ifsAlgorithm : GrowthAlgorithm
  functionalStructuralAlgorithm : GrowthAlgorithm

data GrowthMorphology : Set where
  branchingMorphology : GrowthMorphology
  packedMorphology : GrowthMorphology
  accretiveMorphology : GrowthMorphology

morphologyOf : GrowthAlgorithm → GrowthMorphology
morphologyOf lSystemAlgorithm = branchingMorphology
morphologyOf spaceColonisationAlgorithm = branchingMorphology
morphologyOf phyllotacticAlgorithm = packedMorphology
morphologyOf edenAlgorithm = accretiveMorphology
morphologyOf dlaAlgorithm = branchingMorphology
morphologyOf ifsAlgorithm = branchingMorphology
morphologyOf functionalStructuralAlgorithm = branchingMorphology

lSystemAndSpaceColonisationShareMorphology :
  morphologyOf lSystemAlgorithm
  ≡
  morphologyOf spaceColonisationAlgorithm
lSystemAndSpaceColonisationShareMorphology = refl

lSystemAndSpaceColonisationRemainDistinct :
  lSystemAlgorithm ≡ spaceColonisationAlgorithm → ⊥
lSystemAndSpaceColonisationRemainDistinct ()

record NaturalGrowthAlgorithmBoundary : Set₁ where
  constructor naturalGrowthAlgorithmBoundary
  field
    morphologyDeterminesGrowthMechanism : Bool
    morphologyDeterminesGrowthMechanismIsFalse :
      morphologyDeterminesGrowthMechanism ≡ false

    allNaturalGrowthIsOneAlgorithm : Bool
    allNaturalGrowthIsOneAlgorithmIsFalse :
      allNaturalGrowthIsOneAlgorithm ≡ false

    priorMorphogeneticBoundary :
      Morphogenesis.MorphogeneticVisualBoundary

open NaturalGrowthAlgorithmBoundary public

canonicalNaturalGrowthAlgorithmBoundary : NaturalGrowthAlgorithmBoundary
canonicalNaturalGrowthAlgorithmBoundary =
  naturalGrowthAlgorithmBoundary
    false refl
    false refl
    Morphogenesis.canonicalMorphogeneticVisualBoundary
