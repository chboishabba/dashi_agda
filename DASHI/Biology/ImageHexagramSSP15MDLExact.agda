module DASHI.Biology.ImageHexagramSSP15MDLExact where

open import DASHI.Core.Prelude

import DASHI.Biology.StageSymmetrySSP15SpectrumExact as Spectrum
import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Selector
import DASHI.Foundations.FrameWitnessFibreMDLExact as FrameMDL

------------------------------------------------------------------------
-- Concrete integrated pipeline:
--
-- image receipts -> six-line observation -> candidate frames -> local/gluing
-- witnesses -> SSP15 signatures -> MDL/residual policy -> selected witness.
------------------------------------------------------------------------

data PipelineStage : Set where
  featureExtractionStage
    hexagramProjectionStage
    candidateFrameGenerationStage
    localGluingWitnessStage
    ssp15SpectrumStage
    mdlResidualSelectionStage
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

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = 1 + listCount xs

pipelineHasSevenTypedStages : listCount canonicalPipeline ≡ 7
pipelineHasSevenTypedStages = refl

------------------------------------------------------------------------
-- Image evidence is retained before interpretation.  The existing projection
-- already supplies a concrete Stage-5 hexagram with lower +++ and upper ++0.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Local closure and the SSP15 spectrum are separate coordinates of a frame.
------------------------------------------------------------------------

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
    true
    2 refl

expansiveIntegratedCandidate : IntegratedFrameCandidate
expansiveIntegratedCandidate =
  integratedFrameCandidate
    FrameMDL.expansiveFrame
    FrameMDL.expansiveClosure
    Spectrum.localOnlyStageThreeSignature
    false
    7 refl

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

selectedIntegratedFrameIsCompact :
  frame selectedIntegratedCandidate ≡ FrameMDL.compactFrame
selectedIntegratedFrameIsCompact = refl

selectedIntegratedCostIsTwo : totalCost selectedIntegratedCandidate ≡ 2
selectedIntegratedCostIsTwo = refl

------------------------------------------------------------------------
-- Divination locates an unresolved line; it does not predict its resolution.
------------------------------------------------------------------------

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
    refl refl refl
    3
    false refl

------------------------------------------------------------------------
-- Scalar amplitude / trace information does not reconstruct internal geometry.
-- This is the exact interface-level parallel with the separate 3B/Heisenberg
-- work: a central scalar phase or trace and the Weyl/normaliser geometry are
-- distinct structures.  The actual PR-464 local-module intertwiner is not
-- imported into this stacked branch and is not fabricated here.
------------------------------------------------------------------------

swapFirstSecond : BT.TriadPattern → BT.TriadPattern
swapFirstSecond pattern =
  BT.triad (BT.second pattern) (BT.first pattern) (BT.third pattern)

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
    true refl
    false refl
    false refl
    false refl

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
  integratedSelectorBoundary
    true refl
    false refl
    false refl
    false refl
