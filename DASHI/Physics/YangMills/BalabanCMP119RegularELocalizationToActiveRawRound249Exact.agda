{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationToActiveRawRound249Exact where

------------------------------------------------------------------------
-- ROUND249 / REUSE FUNCTION-VALUED CMP119 LOCALIZATION ON ACTIVE RAW HISTORY
--
-- Round244 already carries concrete source localization data for a function-
-- valued regular E_k.  Round248 identifies the finite-history active route's
-- remaining source payment as decoding the opaque `ELocalizedAnalytic(k,E_k)`
-- proposition into exactly such localization data for the SAME raw E_k.
--
-- Do not coerce the older beta-driven history into the finite-mode history.
-- Instead require the one honest same-object statement actually needed here:
-- the R242/R244 selected regular-E function equals the finite-history raw
-- regular small-field term at each scale.  Under that weld, Round244's concrete
-- localized-sum equality transports to the raw E_k and constructs the Round248
-- decoder mechanically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact as R242
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as R244
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248

record FunctionalToActiveRawRegularEWeld
    {sourceTrajectory split inputs}
    (source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = sourceTrajectory} {split = split} inputs)
    {trajectory Mode Atom betaData history
      Density Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum}
    (objects : RawHistory.CMP119RawObjectsOverHistory history
      Density (R242.Background source) Fluctuation
      Action WilsonTerm (R242.Background source → ℝ)
      RTerm BoundaryTerm Vacuum) : Set₁ where
  field
    selectedRegularEIsRawRegularE : ∀ scale →
      R242.selectedRegularEFunction source scale
      ≡ RawHistory.regularSmallFieldTerm objects scale

open FunctionalToActiveRawRegularEWeld public

rawDecoderFromFunctionalLocalization :
  ∀ {sourceTrajectory split inputs}
    {source : R242.FunctionalRegularESourceFlowInputs
      {trajectory = sourceTrajectory} {split = split} inputs}
    {trajectory Mode Atom betaData history
      Density Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum}
    {objects : RawHistory.CMP119RawObjectsOverHistory history
      Density (R242.Background source) Fluctuation
      Action WilsonTerm (R242.Background source → ℝ)
      RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects)} →
  R244.CMP119RegularELocalizationCarrier source →
  FunctionalToActiveRawRegularEWeld source objects →
  R248.RawELocalizedAnalyticDecoder objects predicates
rawDecoderFromFunctionalLocalization
    {source = source} {objects = objects}
    localization weld = record
  { R248.RawELocalizedAnalyticDecoder.Volume = R244.Volume localization
  ; R248.RawELocalizedAnalyticDecoder.Component = R244.Component localization
  ; R248.RawELocalizedAnalyticDecoder.decodeELocalizedAnalytic =
      λ scale _ → record
        { R248.ExactRawRegularELocalization.components =
            R244.components localization scale
        ; R248.ExactRawRegularELocalization.localizedRegularActivity =
            R244.localizedRegularActivity localization scale
        ; R248.ExactRawRegularELocalization.regularEIsLocalizedCompositeSum =
            λ volume background →
              trans
                (cong (λ f → f background)
                  (sym (selectedRegularEIsRawRegularE weld scale)))
                (R244.selectedRegularEIsLocalizedCompositeSum
                  localization scale volume background)
        }
  }

functionalLocalizationToRawDecoderCompilerLevel : ProofLevel
functionalLocalizationToRawDecoderCompilerLevel = machineChecked

-- Remaining source payments after reuse:
--   1. instantiate the literal R244 localization carrier;
--   2. prove that its selected E_k is the SAME function as the finite-history
--      raw regular small-field term at each scale.
-- No history coercion and no fresh localization theorem are introduced here.
literalFunctionalRegularELocalizationCarrierLevel : ProofLevel
literalFunctionalRegularELocalizationCarrierLevel =
  R244.literalCMP119RegularELocalizationCarrierLevel

literalFunctionalToActiveRawRegularEWeldLevel : ProofLevel
literalFunctionalToActiveRawRegularEWeldLevel = conditional
