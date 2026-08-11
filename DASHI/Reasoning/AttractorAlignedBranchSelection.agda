module DASHI.Reasoning.AttractorAlignedBranchSelection where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact finite branch-selection accounting.
--
-- The objective is deliberately split into non-negative benefit and burden
-- ledgers.  Comparing portfolios by cross-addition avoids pretending that all
-- relational values already inhabit a canonical scalar field:
--
--   P ≻ Q  iff  benefit(P) + burden(Q)
--                    > benefit(Q) + burden(P).
--
-- This is equivalent to positive net advantage when subtraction is available,
-- but remains constructive over Nat and keeps every contribution inspectable.
------------------------------------------------------------------------

data DriftDirection : Set where
  towardAttractor neutralDrift awayFromAttractor : DriftDirection

record AttractorDrift : Set where
  constructor attractorDrift
  field
    driftDirection : DriftDirection
    driftMagnitude : Nat

open AttractorDrift public

driftBenefit : AttractorDrift → Nat
driftBenefit (attractorDrift towardAttractor magnitude) = magnitude
driftBenefit (attractorDrift neutralDrift magnitude) = zero
driftBenefit (attractorDrift awayFromAttractor magnitude) = zero

driftBurden : AttractorDrift → Nat
driftBurden (attractorDrift towardAttractor magnitude) = zero
driftBurden (attractorDrift neutralDrift magnitude) = zero
driftBurden (attractorDrift awayFromAttractor magnitude) = magnitude

record BranchMetric : Set where
  constructor branchMetric
  field
    branchLabel : String
    destinationBasin : Nat
    expectedDrift : AttractorDrift
    informationGain : Nat
    servicingCost : Nat
    diversionCost : Nat
    immediateUtility : Nat
    reversible : Bool
    metricReceipt : String

open BranchMetric public

data InteractionDirection : Set where
  reinforcing independent interfering : InteractionDirection

------------------------------------------------------------------------
-- Typed unordered interaction matrix.
--
-- A PairInteraction is indexed by its two actual branch values.  Validated
-- interactions form an upper-triangular matrix over the portfolio list:
--
--   * no diagonal cell exists, so self-interaction cannot be entered;
--   * exactly one cell exists for each unordered pair of list positions;
--   * each cell is either absent or carries one typed interaction;
--   * foreign string-labelled endpoints cannot contribute to portfolio value.
------------------------------------------------------------------------

record PairInteraction (left right : BranchMetric) : Set where
  constructor pairInteraction
  field
    interactionDirection : InteractionDirection
    interactionMagnitude : Nat
    interactionReceipt : String

open PairInteraction public

data InteractionCell (left right : BranchMetric) : Set where
  noInteraction : InteractionCell left right
  presentInteraction : PairInteraction left right → InteractionCell left right

data InteractionRow (left : BranchMetric) : List BranchMetric → Set where
  rowNil : InteractionRow left []
  rowCons :
    ∀ {right rest} →
    InteractionCell left right →
    InteractionRow left rest →
    InteractionRow left (right ∷ rest)

data ValidatedInteractions : List BranchMetric → Set where
  matrixNil : ValidatedInteractions []
  matrixCons :
    ∀ {left rest} →
    InteractionRow left rest →
    ValidatedInteractions rest →
    ValidatedInteractions (left ∷ rest)

cellConstructiveMass :
  ∀ {left right} → InteractionCell left right → Nat
cellConstructiveMass noInteraction = zero
cellConstructiveMass (presentInteraction interaction)
  with interactionDirection interaction
... | reinforcing = interactionMagnitude interaction
... | independent = zero
... | interfering = zero

cellDestructiveMass :
  ∀ {left right} → InteractionCell left right → Nat
cellDestructiveMass noInteraction = zero
cellDestructiveMass (presentInteraction interaction)
  with interactionDirection interaction
... | reinforcing = zero
... | independent = zero
... | interfering = interactionMagnitude interaction

rowConstructiveMass :
  ∀ {left rest} → InteractionRow left rest → Nat
rowConstructiveMass rowNil = zero
rowConstructiveMass (rowCons cell row) =
  cellConstructiveMass cell + rowConstructiveMass row

rowDestructiveMass :
  ∀ {left rest} → InteractionRow left rest → Nat
rowDestructiveMass rowNil = zero
rowDestructiveMass (rowCons cell row) =
  cellDestructiveMass cell + rowDestructiveMass row

sumConstructiveMass :
  ∀ {branches} → ValidatedInteractions branches → Nat
sumConstructiveMass matrixNil = zero
sumConstructiveMass (matrixCons row matrix) =
  rowConstructiveMass row + sumConstructiveMass matrix

sumDestructiveMass :
  ∀ {branches} → ValidatedInteractions branches → Nat
sumDestructiveMass matrixNil = zero
sumDestructiveMass (matrixCons row matrix) =
  rowDestructiveMass row + sumDestructiveMass matrix

emptyInteractionRow :
  (left : BranchMetric) →
  (rest : List BranchMetric) →
  InteractionRow left rest
emptyInteractionRow left [] = rowNil
emptyInteractionRow left (right ∷ rest) =
  rowCons noInteraction (emptyInteractionRow left rest)

emptyInteractionMatrix :
  (branches : List BranchMetric) →
  ValidatedInteractions branches
emptyInteractionMatrix [] = matrixNil
emptyInteractionMatrix (left ∷ rest) =
  matrixCons
    (emptyInteractionRow left rest)
    (emptyInteractionMatrix rest)

twoBranchInteractionMatrix :
  ∀ {left right} →
  PairInteraction left right →
  ValidatedInteractions (left ∷ right ∷ [])
twoBranchInteractionMatrix interaction =
  matrixCons
    (rowCons (presentInteraction interaction) rowNil)
    (matrixCons rowNil matrixNil)

sumBranchBenefit : List BranchMetric → Nat
sumBranchBenefit [] = zero
sumBranchBenefit (branch ∷ branches) =
  driftBenefit (expectedDrift branch)
  + informationGain branch
  + sumBranchBenefit branches

sumBranchBurden : List BranchMetric → Nat
sumBranchBurden [] = zero
sumBranchBurden (branch ∷ branches) =
  driftBurden (expectedDrift branch)
  + servicingCost branch
  + diversionCost branch
  + sumBranchBurden branches

record BranchPortfolio : Set where
  constructor branchPortfolio
  field
    portfolioLabel : String
    branches : List BranchMetric
    interactions : ValidatedInteractions branches
    availableCapacity : Nat
    portfolioReceipt : String

open BranchPortfolio public

portfolioBenefit : BranchPortfolio → Nat
portfolioBenefit portfolio =
  sumBranchBenefit (branches portfolio)
  + sumConstructiveMass (interactions portfolio)

portfolioBurden : BranchPortfolio → Nat
portfolioBurden portfolio =
  sumBranchBurden (branches portfolio)
  + sumDestructiveMass (interactions portfolio)

totalServicingDemand : BranchPortfolio → Nat
totalServicingDemand portfolio = servicingDemand (branches portfolio)
  where
  servicingDemand : List BranchMetric → Nat
  servicingDemand [] = zero
  servicingDemand (branch ∷ rest) =
    servicingCost branch + servicingDemand rest

advantageAgainst : BranchPortfolio → BranchPortfolio → Nat
advantageAgainst left right =
  portfolioBenefit left + portfolioBurden right

record StrictlyPreferred
    (preferred rejected : BranchPortfolio) : Set where
  constructor strictlyPreferred
  field
    strictMargin : Nat
    strictWitness :
      advantageAgainst preferred rejected
      ≡
      suc strictMargin + advantageAgainst rejected preferred

open StrictlyPreferred public

record WithinCapacity (portfolio : BranchPortfolio) : Set where
  constructor withinCapacity
  field
    slack : Nat
    capacityWitness :
      totalServicingDemand portfolio + slack
      ≡
      availableCapacity portfolio

record ExceedsCapacity (portfolio : BranchPortfolio) : Set where
  constructor exceedsCapacity
  field
    excess : Nat
    overloadWitness :
      totalServicingDemand portfolio
      ≡
      suc excess + availableCapacity portfolio

------------------------------------------------------------------------
-- Effective option count: nominal branches are quotiented by destination
-- basin.  Three labels reaching one basin count as one effective basin.
------------------------------------------------------------------------

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

containsNat : Nat → List Nat → Bool
containsNat x [] = false
containsNat x (y ∷ ys) with natEq x y
... | true = true
... | false = containsNat x ys

insertUniqueNat : Nat → List Nat → List Nat
insertUniqueNat x xs with containsNat x xs
... | true = xs
... | false = x ∷ xs

collectBasins : List BranchMetric → List Nat
collectBasins [] = []
collectBasins (branch ∷ rest) =
  insertUniqueNat (destinationBasin branch) (collectBasins rest)

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

nominalOptionCount : BranchPortfolio → Nat
nominalOptionCount portfolio = listCount (branches portfolio)

effectiveOptionCount : BranchPortfolio → Nat
effectiveOptionCount portfolio =
  listCount (collectBasins (branches portfolio))

------------------------------------------------------------------------
-- Concrete exact witnesses.
------------------------------------------------------------------------

emptyPortfolio : BranchPortfolio
emptyPortfolio =
  branchPortfolio
    "empty"
    []
    matrixNil
    10
    "no live branch"

alignedBranchA : BranchMetric
alignedBranchA =
  branchMetric
    "aligned-a"
    0
    (attractorDrift towardAttractor 4)
    1
    2
    0
    2
    true
    "direct drift four; information one; servicing two"

alignedBranchB : BranchMetric
alignedBranchB =
  branchMetric
    "aligned-b"
    1
    (attractorDrift towardAttractor 3)
    1
    2
    0
    2
    true
    "direct drift three; information one; servicing two"

noiseBranch : BranchMetric
noiseBranch =
  branchMetric
    "nominal-noise"
    0
    (attractorDrift neutralDrift 0)
    0
    2
    3
    1
    true
    "duplicates an existing basin while adding service and diversion cost"

explorationBranch : BranchMetric
explorationBranch =
  branchMetric
    "exploration"
    2
    (attractorDrift neutralDrift 0)
    4
    1
    0
    0
    true
    "neutral direct drift but positive constraint-learning value"

trapBranch : BranchMetric
trapBranch =
  branchMetric
    "attractive-dead-end"
    3
    (attractorDrift awayFromAttractor 3)
    0
    1
    0
    5
    false
    "high immediate utility with adverse global drift"

reinforcingAB : PairInteraction alignedBranchA alignedBranchB
reinforcingAB =
  pairInteraction
    reinforcing
    2
    "shared evidence and compatible work reinforce both branches"

destructiveAB : PairInteraction alignedBranchA alignedBranchB
destructiveAB =
  pairInteraction
    interfering
    8
    "incompatible requirements dominate their separate positive drift"

portfolioA : BranchPortfolio
portfolioA =
  branchPortfolio
    "a-only"
    (alignedBranchA ∷ [])
    (emptyInteractionMatrix (alignedBranchA ∷ []))
    10
    "single aligned branch"

portfolioB : BranchPortfolio
portfolioB =
  branchPortfolio
    "b-only"
    (alignedBranchB ∷ [])
    (emptyInteractionMatrix (alignedBranchB ∷ []))
    10
    "second individually useful branch"

constructivePortfolio : BranchPortfolio
constructivePortfolio =
  branchPortfolio
    "constructive-a-b"
    (alignedBranchA ∷ alignedBranchB ∷ [])
    (twoBranchInteractionMatrix reinforcingAB)
    10
    "two aligned branches with constructive interaction"

destructivePortfolio : BranchPortfolio
destructivePortfolio =
  branchPortfolio
    "destructive-a-b"
    (alignedBranchA ∷ alignedBranchB ∷ [])
    (twoBranchInteractionMatrix destructiveAB)
    10
    "two individually useful branches with larger destructive interaction"

noisePortfolio : BranchPortfolio
noisePortfolio =
  branchPortfolio
    "a-plus-noise"
    (alignedBranchA ∷ noiseBranch ∷ [])
    (emptyInteractionMatrix (alignedBranchA ∷ noiseBranch ∷ []))
    10
    "nominal option count rises but benefit does not"

explorationPortfolio : BranchPortfolio
explorationPortfolio =
  branchPortfolio
    "exploration-only"
    (explorationBranch ∷ [])
    (emptyInteractionMatrix (explorationBranch ∷ []))
    10
    "information value makes a zero-drift branch useful"

trapPortfolio : BranchPortfolio
trapPortfolio =
  branchPortfolio
    "trap-only"
    (trapBranch ∷ [])
    (emptyInteractionMatrix (trapBranch ∷ []))
    10
    "locally attractive but globally adverse"

branchBBeatsEmpty : StrictlyPreferred portfolioB emptyPortfolio
branchBBeatsEmpty = strictlyPreferred 1 refl

explorationBeatsEmpty :
  StrictlyPreferred explorationPortfolio emptyPortfolio
explorationBeatsEmpty = strictlyPreferred 2 refl

constructiveBeatsA :
  StrictlyPreferred constructivePortfolio portfolioA
constructiveBeatsA = strictlyPreferred 3 refl

aBeatsNoise :
  StrictlyPreferred portfolioA noisePortfolio
aBeatsNoise = strictlyPreferred 4 refl

aBeatsDestructivePair :
  StrictlyPreferred portfolioA destructivePortfolio
aBeatsDestructivePair = strictlyPreferred 5 refl

constructiveBeatsNoise :
  StrictlyPreferred constructivePortfolio noisePortfolio
constructiveBeatsNoise = strictlyPreferred 8 refl

constructiveBeatsDestructive :
  StrictlyPreferred constructivePortfolio destructivePortfolio
constructiveBeatsDestructive = strictlyPreferred 9 refl

constructiveBeatsEmpty :
  StrictlyPreferred constructivePortfolio emptyPortfolio
constructiveBeatsEmpty = strictlyPreferred 6 refl

constructiveWithinCapacity :
  WithinCapacity constructivePortfolio
constructiveWithinCapacity = withinCapacity 6 refl

trapHasImmediateUtilityFive :
  immediateUtility trapBranch ≡ 5
trapHasImmediateUtilityFive = refl

trapMovesAwayGlobally :
  driftDirection (expectedDrift trapBranch) ≡ awayFromAttractor
trapMovesAwayGlobally = refl

------------------------------------------------------------------------
-- Option-noise witness: three nominal branches, one reachable basin.
------------------------------------------------------------------------

sameBasinOne sameBasinTwo sameBasinThree : BranchMetric
sameBasinOne =
  branchMetric "same-basin-1" 7 (attractorDrift neutralDrift 0)
    0 1 0 0 true "first label for blocked basin seven"
sameBasinTwo =
  branchMetric "same-basin-2" 7 (attractorDrift neutralDrift 0)
    0 1 0 0 true "second label for blocked basin seven"
sameBasinThree =
  branchMetric "same-basin-3" 7 (attractorDrift neutralDrift 0)
    0 1 0 0 true "third label for blocked basin seven"

optionNoisePortfolio : BranchPortfolio
optionNoisePortfolio =
  branchPortfolio
    "three-label-one-basin"
    (sameBasinOne ∷ sameBasinTwo ∷ sameBasinThree ∷ [])
    (emptyInteractionMatrix
      (sameBasinOne ∷ sameBasinTwo ∷ sameBasinThree ∷ []))
    10
    "nominal diversity collapses after basin quotient"

optionNoiseNominalCountIsThree :
  nominalOptionCount optionNoisePortfolio ≡ 3
optionNoiseNominalCountIsThree = refl

optionNoiseEffectiveCountIsOne :
  effectiveOptionCount optionNoisePortfolio ≡ 1
optionNoiseEffectiveCountIsOne = refl

------------------------------------------------------------------------
-- Finite candidate-family certificate.
------------------------------------------------------------------------

record FiniteSelectionCertificate : Set where
  field
    selectedPortfolio : BranchPortfolio
    selectedWithinCapacity : WithinCapacity selectedPortfolio
    preferredToSingleA : StrictlyPreferred selectedPortfolio portfolioA
    preferredToNoise : StrictlyPreferred selectedPortfolio noisePortfolio
    preferredToDestructivePair :
      StrictlyPreferred selectedPortfolio destructivePortfolio
    preferredToEmpty : StrictlyPreferred selectedPortfolio emptyPortfolio

canonicalFiniteSelection : FiniteSelectionCertificate
canonicalFiniteSelection = record
  { selectedPortfolio = constructivePortfolio
  ; selectedWithinCapacity = constructiveWithinCapacity
  ; preferredToSingleA = constructiveBeatsA
  ; preferredToNoise = constructiveBeatsNoise
  ; preferredToDestructivePair = constructiveBeatsDestructive
  ; preferredToEmpty = constructiveBeatsEmpty
  }

record AttractorSelectionAuthorityBoundary : Set where
  field
    branchCountAloneDeterminesValue : Bool
    immediateUtilityEqualsGlobalProgress : Bool
    neutralDriftMeansNoInformationValue : Bool
    individuallyUsefulBranchesAlwaysCombineUsefully : Bool
    nominalOptionCountEqualsEffectiveBasinCount : Bool
    arbitraryOrDuplicatePairEntriesAffectValue : Bool
    scalarWeightsAreMorallyCanonical : Bool
    boundaryNote : String

canonicalAttractorSelectionAuthorityBoundary :
  AttractorSelectionAuthorityBoundary
canonicalAttractorSelectionAuthorityBoundary = record
  { branchCountAloneDeterminesValue = false
  ; immediateUtilityEqualsGlobalProgress = false
  ; neutralDriftMeansNoInformationValue = false
  ; individuallyUsefulBranchesAlwaysCombineUsefully = false
  ; nominalOptionCountEqualsEffectiveBasinCount = false
  ; arbitraryOrDuplicatePairEntriesAffectValue = false
  ; scalarWeightsAreMorallyCanonical = false
  ; boundaryNote =
      "Portfolio interactions form an upper-triangular typed matrix: no diagonal cell and one cell per unordered branch-position pair. The finite ledger proves exact examples of constructive gain, option noise, destructive interaction, exploration value and trap attraction without claiming a morally canonical scalarization."
  }
