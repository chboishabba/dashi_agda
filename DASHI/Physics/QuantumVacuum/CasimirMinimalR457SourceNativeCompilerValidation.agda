module DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerExact as M

minimalContinuumCompilerOwnedRegression :
  M.minimalContinuumBuildsR126CompilerOwned
    M.canonicalMinimalR457SourceNativeBoundary ≡ true
minimalContinuumCompilerOwnedRegression = refl

minimalR457CompilerOwnedRegression :
  M.minimalPrimitiveSourceInputsBuildR457CompilerOwned
    M.canonicalMinimalR457SourceNativeBoundary ≡ true
minimalR457CompilerOwnedRegression = refl

fullPinnedConstructionNotRequiredRegression :
  M.fullPinnedYangMillsConstructionRequiredForCasimirR457
    M.canonicalMinimalR457SourceNativeBoundary ≡ false
fullPinnedConstructionNotRequiredRegression = refl

massGapPackageNotRequiredRegression :
  M.pinnedMassGapPackageRequiredForCasimirR457
    M.canonicalMinimalR457SourceNativeBoundary ≡ false
massGapPackageNotRequiredRegression = refl

literalConstructionStillRequiredRegression :
  M.literalConstructionStillRequired
    M.canonicalMinimalR457SourceNativeBoundary ≡ true
literalConstructionStillRequiredRegression = refl

continuumLimitStillRequiredRegression :
  M.continuumLimitStillRequired
    M.canonicalMinimalR457SourceNativeBoundary ≡ true
continuumLimitStillRequiredRegression = refl

schwingerBelongsStillRequiredRegression :
  M.schwingerBelongsToContinuumMeasureStillRequired
    M.canonicalMinimalR457SourceNativeBoundary ≡ true
schwingerBelongsStillRequiredRegression = refl
