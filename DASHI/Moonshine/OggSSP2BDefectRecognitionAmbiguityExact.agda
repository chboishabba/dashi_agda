module DASHI.Moonshine.OggSSP2BDefectRecognitionAmbiguityExact where

------------------------------------------------------------------------
-- D MAX-CUT: DEFECT-PRESERVING LABEL AMBIGUITY
--
-- The sourced Mode5 defect profile and the sourced binary-tetrahedral
-- centralizer profile are both
--
--   3,3,2,1,1.
--
-- Therefore any defect-preserving bijection must:
--   * match the two depth-3 modes to the two depth-3 strata: 2! choices;
--   * match the unique depth-2 mode to the unique depth-2 stratum: 1 choice;
--   * match the two depth-1 modes to the two depth-1 strata: 2! choices.
--
-- Hence only 2 * 1 * 2 = 4 source-compatible charts remain.
--
-- This is a finite ambiguity reduction, NOT a source selection.  Independent
-- provenance must still identify which one of the four charts is the actual
-- Monster/Completion10 recognition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Multiplicity accounting.
------------------------------------------------------------------------

depthThreeMultiplicity : Nat
depthThreeMultiplicity = 2

depthTwoMultiplicity : Nat
depthTwoMultiplicity = 1

depthOneMultiplicity : Nat
depthOneMultiplicity = 2

defectCompatibleChartCount : Nat
defectCompatibleChartCount =
  depthThreeMultiplicity * depthTwoMultiplicity * depthOneMultiplicity

defectCompatibleChartCountIsFour : defectCompatibleChartCount ≡ 4
defectCompatibleChartCountIsFour = refl

allModeBijectionsBeforeDefectFilter : Nat
allModeBijectionsBeforeDefectFilter = 120

------------------------------------------------------------------------
-- 2. Promotion firewall.
------------------------------------------------------------------------

data FourCompatibleChartsSelectActualSourceChart : Set where

fourCompatibleChartsDoNotSelectActualSourceChart :
  FourCompatibleChartsSelectActualSourceChart → ⊥
fourCompatibleChartsDoNotSelectActualSourceChart ()

------------------------------------------------------------------------
-- 3. Canonical D status.
------------------------------------------------------------------------

record DefectRecognitionAmbiguityStatus : Set where
  constructor defect-recognition-ambiguity-status
  field
    arbitraryFiveLabelBijections : Nat
    defectCompatibleBijections : Nat
    sourceChartSelected : Bool
    nextResidual : String

canonicalDefectRecognitionAmbiguityStatus :
  DefectRecognitionAmbiguityStatus
canonicalDefectRecognitionAmbiguityStatus =
  defect-recognition-ambiguity-status
    120
    4
    false
    "source-select one of the four defect-compatible Mode5 <-> binary-tetrahedral order-stratum charts; numerical defect agreement alone is insufficient"
