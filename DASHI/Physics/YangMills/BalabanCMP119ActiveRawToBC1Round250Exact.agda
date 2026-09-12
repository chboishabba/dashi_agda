{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact where

------------------------------------------------------------------------
-- ROUND250 / MODERN ACTIVE RAW CMP119 -> BC1 PROOF SPINE
--
-- This is the consumer-first composition of the current source route:
--
--   finite-history raw CMP119 E_k
--     -> exact raw E-localization decoder                 [source payment]
--     -> active regular-E/localization form              [R248 compiler]
--     -> active CMP109/CMP116 continuation               [R247 compiler]
--     -> D2 + CMP109 Eq.(5.1) + finite CMP116 demands    [physical inputs]
--     -> canonical differentiated BC1 carrier            [R115 compiler].
--
-- No all-Nat source history is reintroduced.  No full CMP122 quantitative-bounds
-- package is required merely to reach BC1.  The BC1 effective potential remains
-- definitionally the SAME function-valued raw E_k at the selected active scale.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanBC1CanonicalCarrierCompilerRound115Exact as BC1
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

------------------------------------------------------------------------
-- The exact active regular-E witness and continuation generated from the raw
-- finite-history source objects.
------------------------------------------------------------------------

activeRegularEFormWitness :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)} →
  (decoder : R248.RawELocalizedAnalyticDecoder objects predicates) →
  Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = RawHistory.rawStateFromFiniteBetaHistory objects}
    predicates →
  R246.ActiveRegularESection2FormWitness
    (R248.asRound246ActiveInputs decoder)
activeRegularEFormWitness = R248.activeRegularEFormWitnessFromRaw

activeContinuation :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)} →
  (decoder : R248.RawELocalizedAnalyticDecoder objects predicates) →
  (rawWitness : Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = RawHistory.rawStateFromFiniteBetaHistory objects}
    predicates) →
  (Tangent : Set) →
  _
activeContinuation decoder rawWitness Tangent =
  R247.asActiveCMP109116ContinuationFromRegularEForm
    (activeRegularEFormWitness decoder rawWitness)
    Tangent

------------------------------------------------------------------------
-- Remaining physical/source inputs after all representation compilers.
------------------------------------------------------------------------

record ActiveRawCMP119BC1Inputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum : Set}
    (objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum)
    (predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects))
    (decoder : R248.RawELocalizedAnalyticDecoder objects predicates)
    (rawWitness : Raw.ActiveCMP119Section2Witness
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {source = RawHistory.rawStateFromFiniteBetaHistory objects}
      predicates) : Set₂ where
  field
    Tangent : Set

    calculus :
      Finite.SecondVariationLinearity Background Tangent

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (activeContinuation decoder rawWitness Tangent)
        calculus

    index : R247.ActiveScaleIndex history
    volume : R248.Volume decoder

    -- Round104 turns these four literal CMP116 normalized demands into the
    -- common positive analytic radius; the radius is not another primitive.
    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open ActiveRawCMP119BC1Inputs public

asBC1CanonicalPhysicalInputs :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
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
      predicates} →
  ActiveRawCMP119BC1Inputs objects predicates decoder rawWitness →
  BC1.BC1CanonicalPhysicalInputs
asBC1CanonicalPhysicalInputs
    {decoder = decoder} {rawWitness = rawWitness} inputs = record
  { BC1.BC1CanonicalPhysicalInputs.source =
      activeContinuation decoder rawWitness (Tangent inputs)
  ; BC1.BC1CanonicalPhysicalInputs.calculus = calculus inputs
  ; BC1.BC1CanonicalPhysicalInputs.equation51 = equation51 inputs
  ; BC1.BC1CanonicalPhysicalInputs.scale = index inputs
  ; BC1.BC1CanonicalPhysicalInputs.volume = volume inputs
  ; BC1.BC1CanonicalPhysicalInputs.analyticDemands = analyticDemands inputs
  }

activeRawBC1Carrier :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
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
      predicates} →
  ActiveRawCMP119BC1Inputs objects predicates decoder rawWitness →
  Carrier.LiteralDifferentiatedEffectiveDensityCarrier
activeRawBC1Carrier inputs =
  BC1.bc1CanonicalCarrier (asBC1CanonicalPhysicalInputs inputs)

-- The source identity carried all the way through the modern active path:
-- the generated BC1 potential is literally the raw CMP119 regular small-field
-- function at the underlying active scale.
activeRawBC1PotentialIsExactRawRegularE :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
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
    (inputs : ActiveRawCMP119BC1Inputs
      objects predicates decoder rawWitness) →
  ∀ background →
  Carrier.effectivePotential (activeRawBC1Carrier inputs) background
  ≡ RawHistory.regularSmallFieldTerm objects
      (R247.scale (index inputs)) background
activeRawBC1PotentialIsExactRawRegularE inputs background = refl

------------------------------------------------------------------------
-- Status / remaining proof payments.
------------------------------------------------------------------------

activeRawToBC1CompilerLevel : ProofLevel
activeRawToBC1CompilerLevel = machineChecked

activeRawBC1SameRegularELevel : ProofLevel
activeRawBC1SameRegularELevel = machineChecked

-- Exact source interpretation of CMP119 (2.25)--(2.29) on the raw E_k.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel =
  R248.literalRawELocalizedAnalyticDecoderLevel

-- Concrete physical second-variation calculus and CMP109 Eq.(5.1) on the SAME
-- active continuation remain theorem-bearing analytic/source inputs.
physicalSecondVariationLinearityLevel : ProofLevel
physicalSecondVariationLinearityLevel = conditional

literalCMP109Equation51OnActiveRegularELevel : ProofLevel
literalCMP109Equation51OnActiveRegularELevel = conditional

-- Physical extraction of the four normalized CMP116 Sect.-1 demand constants.
literalCMP116FiniteNormalizedDemandExtractionLevel : ProofLevel
literalCMP116FiniteNormalizedDemandExtractionLevel =
  Canon.literalCMP116FiniteNormalizedDemandExtractionLevel
