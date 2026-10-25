module DASHI.Moonshine.OggSSPClimbingGymAttributionObserverValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Moonshine.OggSSPClimbingGymSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPClimbingGymConsumerDescentExact as Consumer
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact as Replay

------------------------------------------------------------------------
-- RED-first regression contract for the final attribution / observer weld.
------------------------------------------------------------------------

sourceAtlasHasThreeBoundedSources :
  Source.sourceCount (Source.sources Attribution.climbingGymSourceAtlas) ≡ 3
sourceAtlasHasThreeBoundedSources = refl

citationCannotPromoteProof :
  Source.citationImportsProof Attribution.mpmathZetaZeroDocumentation ≡ false
citationCannotPromoteProof = refl

mpmathDocumentationReleaseIs130 :
  Attribution.mpmathDocumentationReleaseIs130
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ true
mpmathDocumentationReleaseIs130 = refl

cacheArtifactPinned :
  Attribution.exactCacheRepositoryArtifactPinned
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ true
cacheArtifactPinned = refl

cacheMetadataValidationPresent :
  Attribution.executableCacheMetadataValidationPresent
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ true
cacheMetadataValidationPresent = refl

runtimeVersionNotManufacturedByCitation :
  Attribution.exactRuntimePackageVersionIndependentlyReceipted
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ false
runtimeVersionNotManufacturedByCitation = refl

lmfdbIsReferenceNotImportedCache :
  Attribution.cacheValuesImportedFromLMFDB
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ false
lmfdbIsReferenceNotImportedCache = refl

sourceFigureDoesNotSupplyRandomSeed :
  Attribution.sourceFigureSuppliesExactRandomShiftSeed
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ false
sourceFigureDoesNotSupplyRandomSeed = refl

mutualCountIsCanonicalNonDescent :
  Descent.ConsumerNonDescentWitness Figure.mutualPairs Figure.figureLane
mutualCountIsCanonicalNonDescent = Consumer.mutualCountLaneNonDescent

mutualCountCannotPayLaneConsumer :
  Descent.ConsumerSufficient Figure.mutualPairs Figure.figureLane → ⊥
mutualCountCannotPayLaneConsumer = Consumer.mutualCountNotLaneSufficient

primeOnlyCannotPayOrientationConsumer :
  Descent.ConsumerSufficient Replay.primeOnlyObservation Consumer.orientationConsumer → ⊥
primeOnlyCannotPayOrientationConsumer = Consumer.primeOnlyNotOrientationSufficient

unmergedSiblingAuthorityNotImported :
  Attribution.unmergedSiblingTheoremAuthorityImported
    Attribution.canonicalClimbingGymSourceAttributionBoundary
  ≡ false
unmergedSiblingAuthorityNotImported = refl
