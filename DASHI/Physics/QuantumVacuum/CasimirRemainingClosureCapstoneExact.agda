module DASHI.Physics.QuantumVacuum.CasimirRemainingClosureCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirBishopSetoidBackendReuseExact
import DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact
import DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact
import DASHI.Physics.QuantumVacuum.CasimirOneSixthFactorisationExact
import DASHI.Physics.QuantumVacuum.CasimirRegulatorDominatedTailCutsetExact
import DASHI.Analysis.ZetaMinusThreeAnalyticCutsetExact
import DASHI.Analysis.ZetaMinusThreeSourceAuthorityExact
import DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact
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

    brownMaclaySameSystemSourceBacked : Bool
    zetaMinusThreeSourceBacked : Bool
    oneSixthDenominatorCompilerOwned : Bool

    legacyPropositionalWeldClosed : Bool
    maxwellPDEClosed : Bool
    teTmCompletenessClosed : Bool
    polarMeasureClosed : Bool
    angularHalfClosed : Bool
    radialThirdClosed : Bool
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

    brownMaclaySameSystemSourceBackedIsTrue :
      brownMaclaySameSystemSourceBacked ≡ true
    zetaMinusThreeSourceBackedIsTrue : zetaMinusThreeSourceBacked ≡ true
    oneSixthDenominatorCompilerOwnedIsTrue : oneSixthDenominatorCompilerOwned ≡ true

    legacyPropositionalWeldClosedIsFalse : legacyPropositionalWeldClosed ≡ false
    maxwellPDEClosedIsFalse : maxwellPDEClosed ≡ false
    teTmCompletenessClosedIsFalse : teTmCompletenessClosed ≡ false
    polarMeasureClosedIsFalse : polarMeasureClosed ≡ false
    angularHalfClosedIsFalse : angularHalfClosed ≡ false
    radialThirdClosedIsFalse : radialThirdClosed ≡ false
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
  ; brownMaclaySameSystemSourceBacked = true
  ; zetaMinusThreeSourceBacked = true
  ; oneSixthDenominatorCompilerOwned = true
  ; legacyPropositionalWeldClosed = false
  ; maxwellPDEClosed = false
  ; teTmCompletenessClosed = false
  ; polarMeasureClosed = false
  ; angularHalfClosed = false
  ; radialThirdClosed = false
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
  ; brownMaclaySameSystemSourceBackedIsTrue = refl
  ; zetaMinusThreeSourceBackedIsTrue = refl
  ; oneSixthDenominatorCompilerOwnedIsTrue = refl
  ; legacyPropositionalWeldClosedIsFalse = refl
  ; maxwellPDEClosedIsFalse = refl
  ; teTmCompletenessClosedIsFalse = refl
  ; polarMeasureClosedIsFalse = refl
  ; angularHalfClosedIsFalse = refl
  ; radialThirdClosedIsFalse = refl
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
  { first = "close perfect-conductor Maxwell PDE/completeness; Brown-Maclay same-system result is source-backed but not a mode proof"
  ; second = "close polar angular 1/2 + radial finite-part 1/3; denominator 2*3=6 is already compiler output"
  ; third = "close regulator estimates and internal zeta(-3) derivation / literal Casimir defect weld; DLMF special value is source-backed"
  ; fourth = "provide setoid-to-legacy kernel weld and compile pressure derivative"
  }
