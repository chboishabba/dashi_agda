module DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact as M

r120R122BuildR123Regression :
  M.r120AndR122BuildR123CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
r120R122BuildR123Regression = refl

r123R124BuildR125Regression :
  M.r123AndR124BuildR125CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
r123R124BuildR125Regression = refl

pinnedContinuumBuildsR126Regression :
  M.pinnedContinuumBuildsR126CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
pinnedContinuumBuildsR126Regression = refl

pinnedSourceInputsBuildR457Regression :
  M.pinnedSourceInputsBuildR457CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
pinnedSourceInputsBuildR457Regression = refl

independentR123NotRequiredRegression :
  M.independentR123StressLaneRequiredAfterR120R122
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
independentR123NotRequiredRegression = refl

independentR125NotRequiredRegression :
  M.independentR125FiniteMeasureLaneRequiredAfterR124
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
independentR125NotRequiredRegression = refl

independentR126ContinuumNotRequiredRegression :
  M.independentR126ContinuumWitnessRequiredAfterPinned
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
independentR126ContinuumNotRequiredRegression = refl

r457PinnedEqualityNotRequiredRegression :
  M.independentR457PinnedConstructionEqualityRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
r457PinnedEqualityNotRequiredRegression = refl

r120StillRequiredRegression :
  M.canonicalMetricSelectedStressLaneStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
r120StillRequiredRegression = refl

r122StillRequiredRegression :
  M.literalDensityAnchoringStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
r122StillRequiredRegression = refl

finiteMeasureWeldStillRequiredRegression :
  M.literalDensityFiniteMeasureWeldStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
finiteMeasureWeldStillRequiredRegression = refl

sourceOSWeldStillRequiredRegression :
  M.sourceOSLiteralSchwingerWeldStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
sourceOSWeldStillRequiredRegression = refl
