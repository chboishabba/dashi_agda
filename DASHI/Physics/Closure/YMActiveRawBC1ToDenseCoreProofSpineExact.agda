{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.YMActiveRawBC1ToDenseCoreProofSpineExact where

------------------------------------------------------------------------
-- YM FULL-PROOF SPINE / ACTIVE RAW CMP119 -> BC1 -> ROW C -> DENSE CORE
--
-- Round250 already carries the exact finite-history raw E_k into the canonical
-- differentiated BC1 carrier.  Row C is parameterized by that carrier directly,
-- so there is no additional BC1 -> Row-C same-object theorem to invent.
--
-- The next genuine representation seam is later:
--
--   Row-C geometric connected clustering
--     -> SAME continuum dense local core
--     -> dense-core spectral exclusion.
--
-- This module composes the existing theorem-bearing pieces and leaves each
-- physical/source payment visible.  It does not claim continuum reconstruction,
-- a physical mass gap, or Clay Yang-Mills closure.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248
import DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact as R250
import DASHI.Physics.YangMills.CompactLieHeatDoobMultiscaleLSIExact as HeatLSI
import DASHI.Physics.YangMills.BalabanRowCPostBC2PhysicalCompletionRound108Exact as RowC
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact as Dense
import DASHI.Physics.Closure.YMPaper3RowCToDenseCoreGapAdapterExact as Bridge

record ActiveRawBC1ToDenseCoreInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum : Set}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)}
    {decoder : R248.RawELocalizedAnalyticDecoder objects predicates}
    {rawWitness : Raw.ActiveCMP119Section2Witness
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {source = RawHistory.rawStateFromFiniteBetaHistory objects}
      predicates}
    (bc1Inputs : R250.ActiveRawCMP119BC1Inputs
      objects predicates decoder rawWitness) : Set₂ where
  field
    heatData : HeatLSI.HeatDoobMultiscaleLSIData

    rowC :
      RowC.PostBC2RowCPhysicalCompletion
        heatData
        (R250.activeRawBC1Carrier bc1Inputs)

    CoreVector HilbertVector : Set
    denseData : Dense.DenseCoreProjectionData CoreVector HilbertVector

    -- This is the first continuum same-object payment on this composed route:
    -- the Row-C observable family must actually be the dense centered local core
    -- consumed by the spectral theorem, not merely an analogous clustering bound.
    rowCToDenseCoreWeld :
      Bridge.RowCToDenseCoreClusteringWeld
        denseData
        (RowC.clustering rowC)

open ActiveRawBC1ToDenseCoreInputs public

activeRawRowCDenseCoreSpectralExclusion :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs} →
  (inputs : ActiveRawBC1ToDenseCoreInputs
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
    {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
    {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
    {objects = objects} {predicates = predicates}
    {decoder = decoder} {rawWitness = rawWitness}
    bc1Inputs) →
  Dense.DenseCoreSpectralExclusion (denseData inputs)
activeRawRowCDenseCoreSpectralExclusion inputs =
  Bridge.rowCClusteringImpliesDenseCoreSpectralExclusion
    (denseData inputs)
    (RowC.clustering (rowC inputs))
    (rowCToDenseCoreWeld inputs)

activeRawRowCPositiveDenseCoreGap :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness bc1Inputs}
    (inputs : ActiveRawBC1ToDenseCoreInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background} {Fluctuation = Fluctuation}
      {Action = Action} {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {objects = objects} {predicates = predicates}
      {decoder = decoder} {rawWitness = rawWitness}
      bc1Inputs) →
  (CandidateGapPositive : Set) →
  CandidateGapPositive →
  Dense.PositiveDenseCoreGap (denseData inputs) CandidateGapPositive
activeRawRowCPositiveDenseCoreGap inputs CandidateGapPositive positiveGap =
  Bridge.rowCClusteringImpliesPositiveDenseCoreGap
    (denseData inputs)
    (RowC.clustering (rowC inputs))
    (rowCToDenseCoreWeld inputs)
    positiveGap

activeRawBC1ToDenseCoreCompilerLevel : ProofLevel
activeRawBC1ToDenseCoreCompilerLevel = machineChecked

-- Finite/source payments inherited from the modern Round250 spine.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R250.literalRawELocalizedAnalyticDecoderLevel

physicalSecondVariationLinearityLevel : ProofLevel
physicalSecondVariationLinearityLevel =
  R250.physicalSecondVariationLinearityLevel

literalCMP109Equation51OnActiveRegularELevel : ProofLevel
literalCMP109Equation51OnActiveRegularELevel =
  R250.literalCMP109Equation51OnActiveRegularELevel

literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel =
  R250.literalCMP116FiniteNormalizedDemandExtractionLevel

-- Row-C physical payments remain independent theorem inputs.
rowCPostBC2PhysicalCompletionLevel : ProofLevel
rowCPostBC2PhysicalCompletionLevel = conditional

-- First continuum same-object / carrier payments on this composed proof spine.
physicalDenseCoreProjectionDataLevel : ProofLevel
physicalDenseCoreProjectionDataLevel =
  Bridge.physicalDenseCoreProjectionDataLevel

rowCToDenseCoreSameObjectWeldLevel : ProofLevel
rowCToDenseCoreSameObjectWeldLevel =
  Bridge.rowCToDenseCoreSameObjectWeldLevel
