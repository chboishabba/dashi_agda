module DASHI.Foundations.RealElementaryFunctionsBishopTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import Sequence as BishopSequence
import DASHI.Foundations.RealAnalysisAxioms as DASHIReal
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
import DASHI.Foundations.RealElementaryFunctionsAlternatingSeriesExact as Alt
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Transport policy for the Bishop submodule.
--
-- This file deliberately does not assert Bishopℝ ≡ DASHIReal.ℝ.  Bishop's
-- equality is a setoid relation on regular rational sequences, while the older
-- DASHI socket used propositional equality over a postulated carrier.  The
-- bridge is therefore explicit and theorem-bearing.
------------------------------------------------------------------------

record BishopBackedDASHIElementaryFunctions : Set₁ where
  field
    bridge : Bishop.BishopToDASHIRealBridge
    series : Series.BishopElementaryPowerSeriesData
    tails : Series.BishopConfiguredElementaryTailProofs series

    dashiSin dashiCos dashiExp dashiLog :
      DASHIReal.ℝ → DASHIReal.ℝ

    bishopSineTransport : ∀ point →
      dashiSin (Bishop.embed bridge point)
      ≡ Bishop.embed bridge (Series.bishopSin series point)

    bishopCosineTransport : ∀ point →
      dashiCos (Bishop.embed bridge point)
      ≡ Bishop.embed bridge (Series.bishopCos series point)

    bishopExponentialTransport : ∀ point →
      dashiExp (Bishop.embed bridge point)
      ≡ Bishop.embed bridge (Series.bishopExp series point)

    bishopNegativeLogTransport : ∀ point inUnit →
      dashiLog
        (DASHIReal._-ℝ_ DASHIReal.1ℝ
          (Bishop.embed bridge point))
      ≡ DASHIReal.-ℝ_
          (Bishop.embed bridge
            (Series.bishopNegativeLogOneMinus series point inUnit))

    -- The pre-existing generic authority is now required to be the transport of
    -- the Bishop-backed functions, rather than an unrelated postulated package.
    dashiPrimitivePackage :
      Alt.ConfiguredElementaryFunctionPrimitivePackage DASHIReal.ℝ

    dashiSineAuthorityAgreesWithTransport : Set
    dashiCosineAuthorityAgreesWithTransport : Set
    dashiExponentialAuthorityAgreesWithTransport : Set
    dashiNegativeLogAuthorityAgreesWithTransport : Set

open BishopBackedDASHIElementaryFunctions public

sinePartialSums :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
sinePartialSums dataSet point =
  BishopSequence.SeriesOf (Series.sineTerm (series dataSet) point)

cosinePartialSums :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
cosinePartialSums dataSet point =
  BishopSequence.SeriesOf (Series.cosineTerm (series dataSet) point)

exponentialPartialSums :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
exponentialPartialSums dataSet point =
  BishopSequence.SeriesOf (Series.exponentialTerm (series dataSet) point)

bishopSineConvergenceTransported :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  (point : Bishop.Bishopℝ) →
  Bishop.DASHIConvergesTo (bridge dataSet)
    (λ index →
      Bishop.embed (bridge dataSet)
        (sinePartialSums dataSet point index))
    (Bishop.embed (bridge dataSet)
      (Series.bishopSin (series dataSet) point))
bishopSineConvergenceTransported dataSet point =
  Bishop.convergencePreserved (bridge dataSet)
    (Series.bishopSinConvergence (series dataSet) point)

bishopCosineConvergenceTransported :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  (point : Bishop.Bishopℝ) →
  Bishop.DASHIConvergesTo (bridge dataSet)
    (λ index →
      Bishop.embed (bridge dataSet)
        (cosinePartialSums dataSet point index))
    (Bishop.embed (bridge dataSet)
      (Series.bishopCos (series dataSet) point))
bishopCosineConvergenceTransported dataSet point =
  Bishop.convergencePreserved (bridge dataSet)
    (Series.bishopCosConvergence (series dataSet) point)

bishopExponentialConvergenceTransported :
  (dataSet : BishopBackedDASHIElementaryFunctions) →
  (point : Bishop.Bishopℝ) →
  Bishop.DASHIConvergesTo (bridge dataSet)
    (λ index →
      Bishop.embed (bridge dataSet)
        (exponentialPartialSums dataSet point index))
    (Bishop.embed (bridge dataSet)
      (Series.bishopExp (series dataSet) point))
bishopExponentialConvergenceTransported dataSet point =
  Bishop.convergencePreserved (bridge dataSet)
    (Series.bishopExpConvergence (series dataSet) point)

------------------------------------------------------------------------
-- A migration can now proceed in two auditable steps:
--   1. prove coefficient/tail bounds directly on Bishopℝ;
--   2. provide the explicit setoid-respecting bridge above for legacy modules.
------------------------------------------------------------------------

bishopBackedFunctionDefinitionsLevel : ProofLevel
bishopBackedFunctionDefinitionsLevel = machineChecked

bishopToLegacyRealTransportLevel : ProofLevel
bishopToLegacyRealTransportLevel = conditional

legacyElementaryAuthorityAgreementLevel : ProofLevel
legacyElementaryAuthorityAgreementLevel = conditional
