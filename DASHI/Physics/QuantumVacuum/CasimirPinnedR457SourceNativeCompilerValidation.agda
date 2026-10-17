module DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirPinnedR457SourceNativeCompilerExact as M

pinnedContinuumBuildsR126Regression :
  M.pinnedContinuumBuildsR126CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
pinnedContinuumBuildsR126Regression = refl

pinnedR125AndOSBuildR457Regression :
  M.pinnedFiniteMeasureAndOSBuildR457CompilerOwned
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
pinnedR125AndOSBuildR457Regression = refl

independentR126ContinuumNotRequiredRegression :
  M.independentR126ContinuumWitnessRequiredAfterPinned
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
independentR126ContinuumNotRequiredRegression = refl

r457PinnedEqualityNotRequiredRegression :
  M.independentR457PinnedConstructionEqualityRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ false
r457PinnedEqualityNotRequiredRegression = refl

finiteMeasureWeldStillRequiredRegression :
  M.literalDensityFiniteMeasureWeldStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
finiteMeasureWeldStillRequiredRegression = refl

sourceOSWeldStillRequiredRegression :
  M.sourceOSLiteralSchwingerWeldStillRequired
    M.canonicalPinnedR457SourceNativeBoundary ≡ true
sourceOSWeldStillRequiredRegression = refl
