module DASHI.Reasoning.RelationalBranchCobordismGeometry where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.List.Base using (map; _++_)

import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftPhaseTableInterference as Phase4
import DASHI.Physics.ShiftUnitaryLikeConstraint as Norm
import DASHI.Reasoning.RelationalBranchInterference as Interference

------------------------------------------------------------------------
-- Finite 1 -> n branching cobordism carrier.
--
-- This is a combinatorial boundary-and-channel model of the pants analogy:
-- one coarse input boundary is split into n fine channels.  It does not claim
-- a smooth surface, a TQFT, a Hilbert space, or a literal modular j-invariant.
------------------------------------------------------------------------

record BoundaryInterface : Set where
  constructor boundaryInterface
  field
    boundaryLabel : String
    propositionType : String
    scaleLabel : String
    boundaryCapacity : Nat
    boundaryPhase : Phase4.Phase4
    boundaryOpen : Bool
    boundaryProvenance : List String

open BoundaryInterface public

record BranchChannel : Set where
  constructor branchChannel
  field
    channelBoundary : BoundaryInterface
    channelWave : Interference.BranchWave
    destinationBasin : String
    channelReceipt : String

open BranchChannel public

record OneToNBranching : Set where
  constructor oneToNBranching
  field
    junctionLabel : String
    coarseInput : BranchChannel
    fineOutputs : List BranchChannel
    splitReceipt : String

open OneToNBranching public

channelCount : List BranchChannel → Nat
channelCount [] = zero
channelCount (_ ∷ xs) = suc (channelCount xs)

outputCount : OneToNBranching → Nat
outputCount junction = channelCount (fineOutputs junction)

sumChannelCapacity : List BranchChannel → Nat
sumChannelCapacity [] = zero
sumChannelCapacity (channel ∷ channels) =
  boundaryCapacity (channelBoundary channel)
  + sumChannelCapacity channels

inputCapacity : OneToNBranching → Nat
inputCapacity junction =
  boundaryCapacity (channelBoundary (coarseInput junction))

outputCapacity : OneToNBranching → Nat
outputCapacity junction = sumChannelCapacity (fineOutputs junction)

outputWaves : OneToNBranching → List Interference.BranchWave
outputWaves junction = map channelWave (fineOutputs junction)

recombinedWave : OneToNBranching → Interference.BranchWave
recombinedWave junction = Interference.sumWaves (outputWaves junction)

subtractWave :
  Interference.BranchWave →
  Interference.BranchWave →
  Interference.BranchWave
subtractWave x y =
  Wave.mkDiscreteWave
    (Wave.DiscreteWave.re x - Wave.DiscreteWave.re y)
    (Wave.DiscreteWave.im x - Wave.DiscreteWave.im y)

splitRecombineResidual : OneToNBranching → Interference.BranchWave
splitRecombineResidual junction =
  subtractWave (recombinedWave junction) (channelWave (coarseInput junction))

record CapacityConservative (junction : OneToNBranching) : Set where
  constructor capacityConservative
  field
    capacityConservation : outputCapacity junction ≡ inputCapacity junction

record CapacityDissipative (junction : OneToNBranching) : Set where
  constructor capacityDissipative
  field
    lostCapacity : Nat
    capacityLossWitness :
      outputCapacity junction + lostCapacity ≡ inputCapacity junction

record WaveConservative (junction : OneToNBranching) : Set where
  constructor waveConservative
  field
    splitRecombinesExactly :
      recombinedWave junction ≡ channelWave (coarseInput junction)

------------------------------------------------------------------------
-- Boundary gluing and pants composition.
------------------------------------------------------------------------

record InterfaceMatch (left right : BranchChannel) : Set where
  constructor interfaceMatch
  field
    propositionMatches :
      propositionType (channelBoundary left)
      ≡ propositionType (channelBoundary right)
    capacityMatches :
      boundaryCapacity (channelBoundary left)
      ≡ boundaryCapacity (channelBoundary right)
    phaseMatches :
      boundaryPhase (channelBoundary left)
      ≡ boundaryPhase (channelBoundary right)
    waveMatches : channelWave left ≡ channelWave right
    opennessMatches :
      boundaryOpen (channelBoundary left)
      ≡ boundaryOpen (channelBoundary right)

record BranchSubstitution
    (outer inner : OneToNBranching) : Set where
  constructor branchSubstitution
  field
    prefix : List BranchChannel
    selected : BranchChannel
    suffix : List BranchChannel
    selectedDecomposition :
      fineOutputs outer ≡ prefix ++ selected ∷ suffix
    gluingInterface : InterfaceMatch selected (coarseInput inner)
    gluingReceipt : String

open BranchSubstitution public

composeAt :
  (outer inner : OneToNBranching) →
  BranchSubstitution outer inner →
  OneToNBranching
composeAt outer inner gluing =
  oneToNBranching
    (junctionLabel outer)
    (coarseInput outer)
    (prefix gluing ++ fineOutputs inner ++ suffix gluing)
    "fine branch replaced by a matching secondary 1-to-n junction"

------------------------------------------------------------------------
-- Canonical exact 1 -> 2 and 1 -> 3 pants witnesses.
------------------------------------------------------------------------

coarseBoundary3 : BoundaryInterface
coarseBoundary3 = boundaryInterface
  "coarse waist"
  "shared proposition"
  "j-coarse"
  3
  Phase4.φ0
  true
  ("coarse proposition provenance" ∷ [])

coarseChannel3 : BranchChannel
coarseChannel3 = branchChannel
  coarseBoundary3
  (Wave.waveOfData 3 Phase4.φ0)
  "coarse basin"
  "incoming amplitude three"

selectedBoundary2 : BoundaryInterface
selectedBoundary2 = boundaryInterface
  "first coarse leg"
  "shared proposition"
  "j-fine-1"
  2
  Phase4.φ0
  true
  ("first split output" ∷ [])

selectedChannel2 : BranchChannel
selectedChannel2 = branchChannel
  selectedBoundary2
  (Wave.waveOfData 2 Phase4.φ0)
  "refined basin a"
  "first output carries amplitude two"

remainderBoundary1 : BoundaryInterface
remainderBoundary1 = boundaryInterface
  "second coarse leg"
  "shared proposition"
  "j-fine-2"
  1
  Phase4.φ0
  true
  ("second split output" ∷ [])

remainderChannel1 : BranchChannel
remainderChannel1 = branchChannel
  remainderBoundary1
  (Wave.waveOfData 1 Phase4.φ0)
  "refined basin b"
  "second output carries amplitude one"

outerOneToTwo : OneToNBranching
outerOneToTwo = oneToNBranching
  "outer one-to-two pants"
  coarseChannel3
  (selectedChannel2 ∷ remainderChannel1 ∷ [])
  "3 = 2 + 1 at both capacity and in-phase amplitude levels"

innerInputBoundary2 : BoundaryInterface
innerInputBoundary2 = boundaryInterface
  "inner waist"
  "shared proposition"
  "j-fine-1"
  2
  Phase4.φ0
  true
  ("glued from first coarse leg" ∷ [])

innerInputChannel2 : BranchChannel
innerInputChannel2 = branchChannel
  innerInputBoundary2
  (Wave.waveOfData 2 Phase4.φ0)
  "refined basin a"
  "matches selected outer leg"

fineBoundaryA fineBoundaryB : BoundaryInterface
fineBoundaryA = boundaryInterface
  "fine leg a1" "shared proposition" "j-fine-1a"
  1 Phase4.φ0 true ("secondary split a" ∷ [])
fineBoundaryB = boundaryInterface
  "fine leg a2" "shared proposition" "j-fine-1b"
  1 Phase4.φ0 true ("secondary split b" ∷ [])

fineChannelA fineChannelB : BranchChannel
fineChannelA = branchChannel
  fineBoundaryA (Wave.waveOfData 1 Phase4.φ0)
  "refined basin a1" "unit in-phase output"
fineChannelB = branchChannel
  fineBoundaryB (Wave.waveOfData 1 Phase4.φ0)
  "refined basin a2" "unit in-phase output"

innerOneToTwo : OneToNBranching
innerOneToTwo = oneToNBranching
  "inner one-to-two pants"
  innerInputChannel2
  (fineChannelA ∷ fineChannelB ∷ [])
  "2 = 1 + 1 at capacity and in-phase amplitude levels"

outerInnerMatch : InterfaceMatch selectedChannel2 innerInputChannel2
outerInnerMatch = interfaceMatch refl refl refl refl refl

canonicalSubstitution :
  BranchSubstitution outerOneToTwo innerOneToTwo
canonicalSubstitution = branchSubstitution
  []
  selectedChannel2
  (remainderChannel1 ∷ [])
  refl
  outerInnerMatch
  "replace the amplitude-two outer leg by two amplitude-one fine legs"

composedOneToThree : OneToNBranching
composedOneToThree =
  composeAt outerOneToTwo innerOneToTwo canonicalSubstitution

outerCapacityConservative : CapacityConservative outerOneToTwo
outerCapacityConservative = capacityConservative refl

innerCapacityConservative : CapacityConservative innerOneToTwo
innerCapacityConservative = capacityConservative refl

composedCapacityConservative : CapacityConservative composedOneToThree
composedCapacityConservative = capacityConservative refl

outerWaveConservative : WaveConservative outerOneToTwo
outerWaveConservative = waveConservative refl

innerWaveConservative : WaveConservative innerOneToTwo
innerWaveConservative = waveConservative refl

composedWaveConservative : WaveConservative composedOneToThree
composedWaveConservative = waveConservative refl

composedOutputCountIsThree : outputCount composedOneToThree ≡ 3
composedOutputCountIsThree = refl

composedResidualIsZero :
  splitRecombineResidual composedOneToThree
  ≡ Wave.mkDiscreteWave (+ 0) (+ 0)
composedResidualIsZero = refl

------------------------------------------------------------------------
-- Split/recombine memory defect.
------------------------------------------------------------------------

phaseChangedBoundary0 phaseChangedBoundary1 : BoundaryInterface
phaseChangedBoundary0 = boundaryInterface
  "phase leg zero" "shared proposition" "j-fine-phase-0"
  1 Phase4.φ0 true ("path zero" ∷ [])
phaseChangedBoundary1 = boundaryInterface
  "phase leg quarter" "shared proposition" "j-fine-phase-1"
  1 Phase4.φ1 true ("path quarter-turn" ∷ [])

phaseChangedChannel0 phaseChangedChannel1 : BranchChannel
phaseChangedChannel0 = branchChannel
  phaseChangedBoundary0 (Wave.waveOfData 1 Phase4.φ0)
  "phase basin zero" "first path"
phaseChangedChannel1 = branchChannel
  phaseChangedBoundary1 (Wave.waveOfData 1 Phase4.φ1)
  "phase basin one" "second path"

phaseChangedInputBoundary : BoundaryInterface
phaseChangedInputBoundary = boundaryInterface
  "phase-changing waist" "shared proposition" "j-coarse"
  2 Phase4.φ0 true ("pre-branch state" ∷ [])

phaseChangedInput : BranchChannel
phaseChangedInput = branchChannel
  phaseChangedInputBoundary (Wave.waveOfData 2 Phase4.φ0)
  "coarse basin" "incoming amplitude two"

phaseChangedJunction : OneToNBranching
phaseChangedJunction = oneToNBranching
  "path-dependent split"
  phaseChangedInput
  (phaseChangedChannel0 ∷ phaseChangedChannel1 ∷ [])
  "capacity is conserved, but phase transport changes the recombined state"

phaseChangedCapacityConservative :
  CapacityConservative phaseChangedJunction
phaseChangedCapacityConservative = capacityConservative refl

phaseChangedResidualExact :
  splitRecombineResidual phaseChangedJunction
  ≡ Wave.mkDiscreteWave (-[1+ 0 ]) (+ 1)
phaseChangedResidualExact = refl

------------------------------------------------------------------------
-- j-coarse / j-fine scale aliases.
------------------------------------------------------------------------

jCoarse : OneToNBranching → BranchChannel
jCoarse = coarseInput

jFine : OneToNBranching → List BranchChannel
jFine = fineOutputs

splitJ : OneToNBranching → List BranchChannel
splitJ = fineOutputs

recombineJ : OneToNBranching → Interference.BranchWave
recombineJ = recombinedWave

------------------------------------------------------------------------
-- Exact attractor-projected coherence.
--
-- cos(theta_att) is discretised to the balanced values +1, 0, -1.  The
-- squared intensity measures coherent magnitude; signedAttractorFlux retains
-- the direction which squaring alone would erase.
------------------------------------------------------------------------

data AlignmentTrit : Set where
  towardAttractor orthogonalToAttractor awayFromAttractor : AlignmentTrit

alignmentScalar : AlignmentTrit → ℤ
alignmentScalar towardAttractor = + 1
alignmentScalar orthogonalToAttractor = + 0
alignmentScalar awayFromAttractor = -[1+ 0 ]

record AttractorBranch : Set where
  constructor attractorBranch
  field
    attractorChannel : BranchChannel
    alignment : AlignmentTrit
    pathPhaseReceipt : String

open AttractorBranch public

projectedWave : AttractorBranch → Interference.BranchWave
projectedWave branch =
  Wave.scaleWave
    (alignmentScalar (alignment branch))
    (channelWave (attractorChannel branch))

projectedWaves : List AttractorBranch → List Interference.BranchWave
projectedWaves [] = []
projectedWaves (branch ∷ branches) =
  projectedWave branch ∷ projectedWaves branches

attractorResultant : List AttractorBranch → Interference.BranchWave
attractorResultant branches =
  Interference.sumWaves (projectedWaves branches)

attractorCoherentIntensity : List AttractorBranch → ℤ
attractorCoherentIntensity branches =
  Norm.waveNormSq (attractorResultant branches)

attractorAxis : Interference.BranchWave
attractorAxis = Wave.encodePhase4 Phase4.φ0

signedAttractorFlux : List AttractorBranch → ℤ
signedAttractorFlux branches =
  Interference.waveDot attractorAxis (attractorResultant branches)

unitAttractorBoundary : BoundaryInterface
unitAttractorBoundary = boundaryInterface
  "unit attractor branch" "goal continuation" "j-fine"
  1 Phase4.φ0 true ("attractor test" ∷ [])

unitAttractorChannel : BranchChannel
unitAttractorChannel = branchChannel
  unitAttractorBoundary (Wave.waveOfData 1 Phase4.φ0)
  "test basin" "unit branch"

alignedUnit orthogonalUnit opposedUnit : AttractorBranch
alignedUnit = attractorBranch
  unitAttractorChannel towardAttractor "cos(theta)=+1"
orthogonalUnit = attractorBranch
  unitAttractorChannel orthogonalToAttractor "cos(theta)=0"
opposedUnit = attractorBranch
  unitAttractorChannel awayFromAttractor "cos(theta)=-1"

twoAlignedIntensityIsFour :
  attractorCoherentIntensity (alignedUnit ∷ alignedUnit ∷ []) ≡ + 4
twoAlignedIntensityIsFour = refl

twoAlignedFluxIsTwo :
  signedAttractorFlux (alignedUnit ∷ alignedUnit ∷ []) ≡ + 2
twoAlignedFluxIsTwo = refl

alignedOpposedCancel :
  attractorCoherentIntensity (alignedUnit ∷ opposedUnit ∷ []) ≡ + 0
alignedOpposedCancel = refl

alignedOpposedFluxIsZero :
  signedAttractorFlux (alignedUnit ∷ opposedUnit ∷ []) ≡ + 0
alignedOpposedFluxIsZero = refl

orthogonalBranchContributesNoProjectedFlux :
  signedAttractorFlux (alignedUnit ∷ orthogonalUnit ∷ []) ≡ + 1
orthogonalBranchContributesNoProjectedFlux = refl

twoOpposedIntensityStillFour :
  attractorCoherentIntensity (opposedUnit ∷ opposedUnit ∷ []) ≡ + 4
twoOpposedIntensityStillFour = refl

twoOpposedFluxIsMinusTwo :
  signedAttractorFlux (opposedUnit ∷ opposedUnit ∷ []) ≡ -[1+ 1 ]
twoOpposedFluxIsMinusTwo = refl

------------------------------------------------------------------------
-- Which-path memory and finite decoherence.
------------------------------------------------------------------------

data PathMarkerRelation : Set where
  indistinguishablePaths distinguishablePaths : PathMarkerRelation

retainedCrossTerm :
  PathMarkerRelation →
  Interference.BranchWave →
  Interference.BranchWave →
  ℤ
retainedCrossTerm indistinguishablePaths left right =
  Interference.pairInterference left right
retainedCrossTerm distinguishablePaths left right = + 0

markedPairIntensity :
  PathMarkerRelation →
  Interference.BranchWave →
  Interference.BranchWave →
  ℤ
markedPairIntensity relation left right =
  (Norm.waveNormSq left + Norm.waveNormSq right)
  + retainedCrossTerm relation left right

indistinguishableInPhaseIntensityIsFour :
  markedPairIntensity
    indistinguishablePaths Interference.phase0 Interference.phase0
  ≡ + 4
indistinguishableInPhaseIntensityIsFour = refl

distinguishableInPhaseIntensityIsTwo :
  markedPairIntensity
    distinguishablePaths Interference.phase0 Interference.phase0
  ≡ + 2
distinguishableInPhaseIntensityIsTwo = refl

indistinguishableOpposedIntensityIsZero :
  markedPairIntensity
    indistinguishablePaths Interference.phase0 Interference.phase2
  ≡ + 0
indistinguishableOpposedIntensityIsZero = refl

distinguishableOpposedIntensityIsTwo :
  markedPairIntensity
    distinguishablePaths Interference.phase0 Interference.phase2
  ≡ + 2
distinguishableOpposedIntensityIsTwo = refl

pathErasureCanCreateSpuriousConstructiveMass :
  markedPairIntensity
    distinguishablePaths Interference.phase0 Interference.phase0
  + (+ 2)
  ≡
  markedPairIntensity
    indistinguishablePaths Interference.phase0 Interference.phase0
pathErasureCanCreateSpuriousConstructiveMass = refl

pathOverseparationCanDestroyConstructiveMass :
  markedPairIntensity
    indistinguishablePaths Interference.phase0 Interference.phase0
  ≡
  markedPairIntensity
    distinguishablePaths Interference.phase0 Interference.phase0
  + (+ 2)
pathOverseparationCanDestroyConstructiveMass = refl

record PersistentPathMarker : Set where
  constructor persistentPathMarker
  field
    historicalRoute currentRoute : String
    relationTransported : PathMarkerRelation
    currentContextChecked : Bool
    transportReceipt : String

------------------------------------------------------------------------
-- Closing a slit removes its diagonal term and every cross term touching it.
------------------------------------------------------------------------

branchMarginalLaw :
  (branch : Interference.BranchWave) →
  (others : List Interference.BranchWave) →
  Interference.coherentIntensity (branch ∷ others)
  ≡
  (Norm.waveNormSq branch + Interference.coherentIntensity others)
  + Interference.pairInterferenceWith branch others
branchMarginalLaw branch others =
  trans
    (Interference.doubleSlitLaw branch (Interference.sumWaves others))
    (cong
      (λ cross →
        (Norm.waveNormSq branch + Interference.coherentIntensity others)
        + cross)
      (Interference.pairInterferenceWithSum branch others))

inPhaseMarginalContainsPositiveCrossTerm :
  Interference.coherentIntensity
    (Interference.phase0 ∷ Interference.phase0 ∷ [])
  ≡
  (Norm.waveNormSq Interference.phase0
    + Interference.coherentIntensity (Interference.phase0 ∷ []))
  + Interference.pairInterferenceWith
      Interference.phase0 (Interference.phase0 ∷ [])
inPhaseMarginalContainsPositiveCrossTerm = refl

opposedMarginalContainsNegativeCrossTerm :
  Interference.coherentIntensity
    (Interference.phase0 ∷ Interference.phase2 ∷ [])
  ≡
  (Norm.waveNormSq Interference.phase0
    + Interference.coherentIntensity (Interference.phase2 ∷ []))
  + Interference.pairInterferenceWith
      Interference.phase0 (Interference.phase2 ∷ [])
opposedMarginalContainsNegativeCrossTerm = refl

------------------------------------------------------------------------
-- Pairwise relation count grows quadratically by recurrence.
------------------------------------------------------------------------

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

pairRelationCount : ∀ {A : Set} → List A → Nat
pairRelationCount [] = zero
pairRelationCount (_ ∷ xs) = listLength xs + pairRelationCount xs

threeBranchesHaveThreePairs :
  pairRelationCount
    (Interference.phase0 ∷ Interference.phase1 ∷ Interference.phase2 ∷ [])
  ≡ 3
threeBranchesHaveThreePairs = refl

fourBranchesHaveSixPairs :
  pairRelationCount
    (Interference.phase0
      ∷ Interference.phase1
      ∷ Interference.phase2
      ∷ Interference.phase3
      ∷ [])
  ≡ 6
fourBranchesHaveSixPairs = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record BranchCobordismAuthorityBoundary : Set where
  field
    exactFiniteBoundaryComposition : Bool
    exactSplitRecombineResidual : Bool
    exactAttractorTritProjection : Bool
    exactMarkerSuppressionModel : Bool
    smoothCobordismClaimed : Bool
    tqftFunctorClaimed : Bool
    continuousAngleRecovered : Bool
    modularJInvariantClaimed : Bool
    markerRelationDiagnosesTrauma : Bool
    boundaryNote : String

canonicalBranchCobordismAuthorityBoundary :
  BranchCobordismAuthorityBoundary
canonicalBranchCobordismAuthorityBoundary = record
  { exactFiniteBoundaryComposition = true
  ; exactSplitRecombineResidual = true
  ; exactAttractorTritProjection = true
  ; exactMarkerSuppressionModel = true
  ; smoothCobordismClaimed = false
  ; tqftFunctorClaimed = false
  ; continuousAngleRecovered = false
  ; modularJInvariantClaimed = false
  ; markerRelationDiagnosesTrauma = false
  ; boundaryNote =
      "The pants object is a finite typed 1-to-n boundary carrier. Composition, capacity, wave recombination, residual memory, signed attractor projection, marker suppression, and branch marginality are exact on the stated discrete carriers. Smooth topology, TQFT, continuous geometry, modular-j identity, and clinical diagnosis remain outside the theorem surface."
  }
