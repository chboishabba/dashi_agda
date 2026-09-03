module DASHI.Physics.QuantumVacuum.CasimirRemainingClosureCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact
import DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact
import DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact
import DASHI.Physics.QuantumVacuum.CasimirRegulatorDominatedTailCutsetExact
import DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact
import DASHI.Physics.QuantumVacuum.CasimirPressureDerivativeSameObjectCompletionExact

------------------------------------------------------------------------
-- FINAL REMAINING CASIMIR CLOSURE CAPSTONE
------------------------------------------------------------------------

record RemainingClosureStatus : Set where
  field
    importedBishopSetoidCompleteRealBackend : Bool
    localFastCauchyBackendStillCritical : Bool
    setoidNativeCasimirScalarInterface : Bool
    maxwellPDECutset : Bool
    radialMeasureCutset : Bool
    regulatorAnalyticCutset : Bool
    zetaMinusThreeCutset : Bool
    pressureDerivativeCutset : Bool

    legacyPropositionalWeldClosed : Bool
    maxwellPDEClosed : Bool
    teTmCompletenessClosed : Bool
    polarMeasureClosed : Bool
    radialOneSixthClosed : Bool
    dominationInterchangeClosed : Bool
    regulatorTailClosed : Bool
    zetaMinusThreeAnalyticClosed : Bool
    casimirZetaSameObjectWeldClosed : Bool
    pressureSameObjectDerivativeClosed : Bool

    importedBishopSetoidCompleteRealBackendIsTrue :
      importedBishopSetoidCompleteRealBackend ≡ true
    localFastCauchyBackendStillCriticalIsFalse :
      localFastCauchyBackendStillCritical ≡ false
    setoidNativeCasimirScalarInterfaceIsTrue : setoidNativeCasimirScalarInterface ≡ true
    maxwellPDECutsetIsTrue : maxwellPDECutset ≡ true
    radialMeasureCutsetIsTrue : radialMeasureCutset ≡ true
    regulatorAnalyticCutsetIsTrue : regulatorAnalyticCutset ≡ true
    zetaMinusThreeCutsetIsTrue : zetaMinusThreeCutset ≡ true
    pressureDerivativeCutsetIsTrue : pressureDerivativeCutset ≡ true

    legacyPropositionalWeldClosedIsFalse : legacyPropositionalWeldClosed ≡ false
    maxwellPDEClosedIsFalse : maxwellPDEClosed ≡ false
    teTmCompletenessClosedIsFalse : teTmCompletenessClosed ≡ false
    polarMeasureClosedIsFalse : polarMeasureClosed ≡ false
    radialOneSixthClosedIsFalse : radialOneSixthClosed ≡ false
    dominationInterchangeClosedIsFalse : dominationInterchangeClosed ≡ false
    regulatorTailClosedIsFalse : regulatorTailClosed ≡ false
    zetaMinusThreeAnalyticClosedIsFalse : zetaMinusThreeAnalyticClosed ≡ false
    casimirZetaSameObjectWeldClosedIsFalse : casimirZetaSameObjectWeldClosed ≡ false
    pressureSameObjectDerivativeClosedIsFalse : pressureSameObjectDerivativeClosed ≡ false

open RemainingClosureStatus public

canonicalRemainingClosureStatus : RemainingClosureStatus
canonicalRemainingClosureStatus = record
  { importedBishopSetoidCompleteRealBackend = true
  ; localFastCauchyBackendStillCritical = false
  ; setoidNativeCasimirScalarInterface = true
  ; maxwellPDECutset = true
  ; radialMeasureCutset = true
  ; regulatorAnalyticCutset = true
  ; zetaMinusThreeCutset = true
  ; pressureDerivativeCutset = true
  ; legacyPropositionalWeldClosed = false
  ; maxwellPDEClosed = false
  ; teTmCompletenessClosed = false
  ; polarMeasureClosed = false
  ; radialOneSixthClosed = false
  ; dominationInterchangeClosed = false
  ; regulatorTailClosed = false
  ; zetaMinusThreeAnalyticClosed = false
  ; casimirZetaSameObjectWeldClosed = false
  ; pressureSameObjectDerivativeClosed = false
  ; importedBishopSetoidCompleteRealBackendIsTrue = refl
  ; localFastCauchyBackendStillCriticalIsFalse = refl
  ; setoidNativeCasimirScalarInterfaceIsTrue = refl
  ; maxwellPDECutsetIsTrue = refl
  ; radialMeasureCutsetIsTrue = refl
  ; regulatorAnalyticCutsetIsTrue = refl
  ; zetaMinusThreeCutsetIsTrue = refl
  ; pressureDerivativeCutsetIsTrue = refl
  ; legacyPropositionalWeldClosedIsFalse = refl
  ; maxwellPDEClosedIsFalse = refl
  ; teTmCompletenessClosedIsFalse = refl
  ; polarMeasureClosedIsFalse = refl
  ; radialOneSixthClosedIsFalse = refl
  ; dominationInterchangeClosedIsFalse = refl
  ; regulatorTailClosedIsFalse = refl
  ; zetaMinusThreeAnalyticClosedIsFalse = refl
  ; casimirZetaSameObjectWeldClosedIsFalse = refl
  ; pressureSameObjectDerivativeClosedIsFalse = refl
  }

record ClosureOrder : Set where
  field
    first : String
    second : String
    third : String
    fourth : String

canonicalClosureOrder : ClosureOrder
canonicalClosureOrder = record
  { first = "close perfect-conductor Maxwell PDE/completeness"
  ; second = "close radial measure + regulated analytic estimates and 1/6"
  ; third = "close zeta(-3) analytic theorem + literal Casimir defect weld"
  ; fourth = "provide setoid-to-legacy kernel weld and compile pressure derivative"
  }
