module DASHI.Biology.ImageHexagramSSP15MDLExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ListExact public

import DASHI.Biology.StageSymmetrySSP15SpectrumExact as Spectrum
import DASHI.Foundations.ActionMDLSeparation as ActionMDL
import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Selector
import DASHI.Foundations.FrameWitnessFibreMDLExact as FrameMDL

data PipelineStage : Set where
  featureExtractionStage hexagramProjectionStage candidateFrameGenerationStage
    localGluingWitnessStage ssp15SpectrumStage mdlResidualSelectionStage
    selectedFrameStage : PipelineStage

canonicalPipeline : List PipelineStage
canonicalPipeline =
  featureExtractionStage
  ∷ hexagramProjectionStage
  ∷ candidateFrameGenerationStage
  ∷ localGluingWitnessStage
  ∷ ssp15SpectrumStage
  ∷ mdlResidualSelectionStage
  ∷ selectedFrameStage
  ∷ []

pipelineHasSevenTypedStages : listCount canonicalPipeline ≡ 7
pipelineHasSevenTypedStages = refl

canonicalObservation : Selector.HexagramObservation
canonicalObservation =
  Selector.ImageHexagramProjection.observation
    Selector.canonicalImageProjection

canonicalLowerPatternIsClosed :
  Selector.HexagramObservation.lowerTriad canonicalObservation
  ≡ BT.allPositive
canonicalLowerPatternIsClosed = refl

canonicalUpperPatternIsOpen :
  Selector.HexagramObservation.upperTriad canonicalObservation
  ≡ BT.twoPositiveOneOpen
canonicalUpperPatternIsOpen = refl

canonicalObservationAmplitudeIsFive :
  Selector.HexagramObservation.lowerAmplitude canonicalObservation
  + Selector.HexagramObservation.upperAmplitude canonicalObservation
  ≡ 5
canonicalObservationAmplitudeIsFive = refl

record IntegratedFrameCandidate : Set where
  constructor integratedFrameCandidate
  field
    frame : FrameMDL.CandidateFrame
    localClosure : FrameMDL.ClosesThreeAt frame
    spectrum : Spectrum.RichSSP15Signature
    evidenceCompatible : Bool
    totalCost : Nat
    totalCostExact :
      totalCost ≡ FrameMDL.totalFrameCost (FrameMDL.frameCostOf frame)

open IntegratedFrameCandidate public

compactIntegratedCandidate : IntegratedFrameCandidate
compactIntegratedCandidate =
  integratedFrameCandidate
    FrameMDL.compactFrame
    FrameMDL.compactClosure
    Spectrum.crossScaleStageThreeSignature
    true 2 refl

expansiveIntegratedCandidate : IntegratedFrameCandidate
expansiveIntegratedCandidate =
  integratedFrameCandidate
    FrameMDL.expansiveFrame
    FrameMDL.expansiveClosure
    Spectrum.localOnlyStageThreeSignature
    false 7 refl

record AdmissibleIntegratedCandidate
  (candidate : IntegratedFrameCandidate) : Set where
  constructor admissibleIntegratedCandidate
  field
    evidenceCompatibleIsTrue : evidenceCompatible candidate ≡ true

compactIntegratedCandidateIsAdmissible :
  AdmissibleIntegratedCandidate compactIntegratedCandidate
compactIntegratedCandidateIsAdmissible =
  admissibleIntegratedCandidate refl

expansiveIntegratedCandidateIsNotAdmissible :
  AdmissibleIntegratedCandidate expansiveIntegratedCandidate → ⊥
expansiveIntegratedCandidateIsNotAdmissible
  (admissibleIntegratedCandidate ())

selectedIntegratedCandidate : IntegratedFrameCandidate
selectedIntegratedCandidate = compactIntegratedCandidate

selectedIntegratedCandidateIsAdmissible :
  AdmissibleIntegratedCandidate selectedIntegratedCandidate
selectedIntegratedCandidateIsAdmissible =
  compactIntegratedCandidateIsAdmissible

selectedIntegratedFrameIsCompact :
  frame selectedIntegratedCandidate ≡ FrameMDL.compactFrame
selectedIntegratedFrameIsCompact = refl

selectedIntegratedFrameMatchesMDL :
  frame selectedIntegratedCandidate
  ≡ ActionMDL.MDLSelection.selected
      FrameMDL.canonicalFrameMDLSelection tt
selectedIntegratedFrameMatchesMDL = refl

selectedIntegratedCostIsTwo : totalCost selectedIntegratedCandidate ≡ 2
selectedIntegratedCostIsTwo = refl

selectedCostIsMinimalAmongConstructedCandidates :
  totalCost selectedIntegratedCandidate
  ≤ totalCost expansiveIntegratedCandidate
selectedCostIsMinimalAmongConstructedCandidates =
  s≤s (s≤s z≤n)

record StageFiveAttentionWitness : Set where
  constructor stageFiveAttentionWitness
  field
    lower : BT.TriadPattern
    upper : BT.TriadPattern
    lowerAmplitude : Amp.Amplitude7
    upperAmplitude : Amp.Amplitude7
    totalAmplitude : Amp.JoinedAmplitude13
    lowerExact : Amp.triadAmplitude lower ≡ lowerAmplitude
    upperExact : Amp.triadAmplitude upper ≡ upperAmplitude
    totalExact : Amp.joinAmplitude lower upper ≡ totalAmplitude
    unresolvedLineCode : Nat
    resolutionPredicted : Bool
    resolutionPredictedIsFalse : resolutionPredicted ≡ false

canonicalStageFiveAttentionWitness : StageFiveAttentionWitness
canonicalStageFiveAttentionWitness =
  stageFiveAttentionWitness
    BT.allPositive BT.twoPositiveOneOpen
    Amp.ampPos3 Amp.ampPos2 Amp.joinedPos5
    refl refl refl 3 false refl

swapFirstSecond : BT.TriadPattern → BT.TriadPattern
swapFirstSecond triadPattern =
  BT.triad
    (BT.second triadPattern)
    (BT.first triadPattern)
    (BT.third triadPattern)

swapPreservesOpenAmplitude :
  Amp.triadAmplitude (swapFirstSecond Amp.secondLineOpen)
  ≡ Amp.triadAmplitude Amp.secondLineOpen
swapPreservesOpenAmplitude = refl

swapChangesOpenLine :
  swapFirstSecond Amp.secondLineOpen ≡ Amp.secondLineOpen → ⊥
swapChangesOpenLine ()

record ScalarGeometrySeparationBoundary : Set where
  constructor scalarGeometrySeparationBoundary
  field
    equalAmplitudeCanRetainDifferentLineGeometry : Bool
    equalAmplitudeCanRetainDifferentLineGeometryIsTrue :
      equalAmplitudeCanRetainDifferentLineGeometry ≡ true
    scalarTraceReconstructsHeisenbergGeometry : Bool
    scalarTraceReconstructsHeisenbergGeometryIsFalse :
      scalarTraceReconstructsHeisenbergGeometry ≡ false
    monster3BLocalModuleIntertwinerImportedHere : Bool
    monster3BLocalModuleIntertwinerImportedHereIsFalse :
      monster3BLocalModuleIntertwinerImportedHere ≡ false
    normaliserMatricesConstructedHere : Bool
    normaliserMatricesConstructedHereIsFalse :
      normaliserMatricesConstructedHere ≡ false

canonicalScalarGeometrySeparationBoundary :
  ScalarGeometrySeparationBoundary
canonicalScalarGeometrySeparationBoundary =
  scalarGeometrySeparationBoundary
    true refl false refl false refl false refl

record IntegratedSelectorBoundary : Set where
  constructor integratedSelectorBoundary
  field
    typedPipelineConstructed : Bool
    typedPipelineConstructedIsTrue : typedPipelineConstructed ≡ true
    localClosureAndSSPProfileIdentified : Bool
    localClosureAndSSPProfileIdentifiedIsFalse :
      localClosureAndSSPProfileIdentified ≡ false
    tarotOrHexagramPredictsResolution : Bool
    tarotOrHexagramPredictsResolutionIsFalse :
      tarotOrHexagramPredictsResolution ≡ false
    selectedFrameExplainsEveryScale : Bool
    selectedFrameExplainsEveryScaleIsFalse :
      selectedFrameExplainsEveryScale ≡ false

canonicalIntegratedSelectorBoundary : IntegratedSelectorBoundary
canonicalIntegratedSelectorBoundary =
  integratedSelectorBoundary true refl false refl false refl false refl
