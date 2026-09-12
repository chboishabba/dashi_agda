{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact where

------------------------------------------------------------------------
-- ROUND248 / LEAST-PRIVILEGE RAW CMP119 E-LOCALIZATION DECODER
--
-- The finite-history raw CMP119 carrier already owns the selected density,
-- the exact raw regular small-field term E_k, and the active Sect.-2 witness.
-- However `ELocalizedAnalytic` is intentionally an opaque source predicate: it
-- does not itself contain the repository's concrete components/activity/sum
-- data required by the BC1-facing Round246 carrier.
--
-- This adapter names exactly that missing interpretation.  It is indexed by the
-- SAME raw E_k, so a decoder cannot silently replace the source term by a more
-- convenient function.  Once the interpretation is supplied, the existing
-- active raw Sect.-2 witness compiles mechanically to Round246's least-privilege
-- `ActiveRegularESection2FormWitness`, and Round247 can continue to CMP109/116.
--
-- No CMP122 quantitative-bounds field is consumed here.  No new localization
-- theorem is asserted: the literal source/repository interpretation remains the
-- conditional physical/source payment.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as R246

record ExactRawRegularELocalization
    (Background Volume Component : Set)
    (regularE : Background → ℝ) : Set₁ where
  field
    components : Volume → List Component
    localizedRegularActivity : Volume → Component → Background → ℝ
    regularEIsLocalizedCompositeSum : ∀ volume background →
      regularE background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity volume)
            (components volume))
          background

open ExactRawRegularELocalization public

asRound246Form :
  ∀ {Density Background Volume Component : Set}
    {scale : Nat}
    {density : Density}
    {regularE : Background → ℝ} →
  ExactRawRegularELocalization Background Volume Component regularE →
  R246.CMP119RegularESection2Form
    Density Background Volume Component scale density
asRound246Form {regularE = regularE} localized = record
  { R246.CMP119RegularESection2Form.regularE = regularE
  ; R246.CMP119RegularESection2Form.components = components localized
  ; R246.CMP119RegularESection2Form.localizedRegularActivity =
      localizedRegularActivity localized
  ; R246.CMP119RegularESection2Form.regularEIsLocalizedCompositeSum =
      regularEIsLocalizedCompositeSum localized
  }

record RawELocalizedAnalyticDecoder
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
      (RawHistory.rawStateFromFiniteBetaHistory objects)) : Set₂ where
  field
    Volume Component : Set

    decodeELocalizedAnalytic : ∀ scale →
      Raw.ELocalizedAnalytic predicates scale
        (RawHistory.regularSmallFieldTerm objects scale) →
      ExactRawRegularELocalization
        Background Volume Component
        (RawHistory.regularSmallFieldTerm objects scale)

open RawELocalizedAnalyticDecoder public

asRound246ActiveInputs :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)} →
  (decoder : RawELocalizedAnalyticDecoder objects predicates) →
  R246.ActiveRegularESection2Inputs betaData history
asRound246ActiveInputs
    {Density = Density} {Background = Background}
    {objects = objects} {predicates = predicates} decoder = record
  { R246.ActiveRegularESection2Inputs.Density = Density
  ; R246.ActiveRegularESection2Inputs.Background = Background
  ; R246.ActiveRegularESection2Inputs.Volume = Volume decoder
  ; R246.ActiveRegularESection2Inputs.Component = Component decoder
  ; R246.ActiveRegularESection2Inputs.densityAt =
      RawHistory.effectiveDensity objects
  ; R246.ActiveRegularESection2Inputs.Section2ConditionsAndBounds =
      λ scale density →
        density ≡ RawHistory.effectiveDensity objects scale →
        Raw.CMP119Section2AtScale predicates scale
  }

activeRegularEFormWitnessFromRaw :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)}
    (decoder : RawELocalizedAnalyticDecoder objects predicates) →
  Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = RawHistory.rawStateFromFiniteBetaHistory objects}
    predicates →
  R246.ActiveRegularESection2FormWitness
    (asRound246ActiveInputs decoder)
activeRegularEFormWitnessFromRaw decoder witness = record
  { R246.ActiveRegularESection2FormWitness.regularEFormOnActiveScale =
      λ scale active →
        asRound246Form
          (decodeELocalizedAnalytic decoder scale
            (Raw.eSector
              (Raw.section2OnActiveScale witness scale active)))
  }

rawActiveRegularEDecoderCompilerLevel : ProofLevel
rawActiveRegularEDecoderCompilerLevel = machineChecked

rawActiveRegularEFormWitnessCompilerLevel : ProofLevel
rawActiveRegularEFormWitnessCompilerLevel = machineChecked

-- First remaining source/repository payment on this route: interpret the literal
-- CMP119 Sect.-2 E-localization predicate as concrete localization data for the
-- exact raw function-valued E_k.  Source authority alone does not manufacture
-- this decoder.
literalRawELocalizedAnalyticDecoderLevel : ProofLevel
literalRawELocalizedAnalyticDecoderLevel = conditional
