module DASHI.Reasoning.Trialectic369Selected3BLinearCoreCompatibilityExact where

------------------------------------------------------------------------
-- HISTORICAL ACQUISITION CORE -> MINIMAL CANONICAL LINEAR CORE
--
-- DASHI CONTRIBUTION
--
-- The source-native acquisition core introduced for compatibility with the
-- historical ActualLinearMultiplicityAcquisition contains strictly more data
-- than the canonical trialectic linear target.
--
-- Every such historical core therefore forgets exactly to the new minimal
-- CanonicalSelected3BLinearCore.  The reverse direction is deliberately not
-- required: literal-VOA linearity/provenance compatibility fields are useful
-- archive/source receipts, but are not inputs to the canonical trialectic
-- multiplicity route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.Trialectic369Selected3BLinearAcquisitionCompletionExact as Historical
import DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact as Canonical
import DASHI.Reasoning.Trialectic369OutgoingLinearAcquisitionBridgeExact as LinearBridge

------------------------------------------------------------------------
-- 1. Exact forgetful compiler.
------------------------------------------------------------------------

canonicalCoreFromHistoricalCore :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K}) →
  Canonical.CanonicalLinearHomSameObjectWeld
    (Historical.linearZetaProducer core)
    (Historical.multiplicityHomSpace core) →
  Canonical.CanonicalSelected3BLinearCore {Monster} {K}
canonicalCoreFromHistoricalCore core homWeld =
  record
    { kernelRecognizedSameElementAttachment =
        Historical.kernelRecognizedSameElementAttachment core
    ; weightTwoLinearBridge =
        Historical.weightTwoLinearBridge core
    ; linearZetaProducer =
        Historical.linearZetaProducer core
    ; compiledProducerIsLinearProducer =
        Historical.compiledProducerIsLinearProducer core
    ; multiplicityHomSpace =
        Historical.multiplicityHomSpace core
    ; homSameObjectWeld = homWeld
    ; constituentCarrierIsSelectedAmbient =
        Historical.weightTwoConstituentCarrierIsSelected3BAmbient core
    ; sourceNativeInertiaSameAction =
        Historical.actualMultiplicityActionIsSourceNativeInertiaAction core
    ; twelveSeventyEightLinearIntertwiner =
        Historical.twelveSeventyEightLinearIntertwiner core
    }

historicalCorePlusHomWeldCompilesCanonicalRoute :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K})
    (homWeld :
      Canonical.CanonicalLinearHomSameObjectWeld
        (Historical.linearZetaProducer core)
        (Historical.multiplicityHomSpace core)) →
  LinearBridge.canonicalLinearRouteFromAcquisition
    (Historical.acquisitionFromCore core)
  ≡
  Canonical.canonicalLinearRoute
    (canonicalCoreFromHistoricalCore core homWeld)
historicalCorePlusHomWeldCompilesCanonicalRoute core homWeld = refl

data HistoricalCoreAloneCreatesHomSameObjectWeld : Set where

historicalCoreAloneDoesNotCreateHomSameObjectWeld :
  HistoricalCoreAloneCreatesHomSameObjectWeld → ⊥
historicalCoreAloneDoesNotCreateHomSameObjectWeld ()

------------------------------------------------------------------------
-- 2. Reverse promotion is intentionally not part of the canonical lane.
------------------------------------------------------------------------

data MinimalCoreAutomaticallyReconstructsHistoricalCompatibility : Set where

minimalCoreDoesNotAutomaticallyReconstructHistoricalCompatibility :
  MinimalCoreAutomaticallyReconstructsHistoricalCompatibility → ⊥
minimalCoreDoesNotAutomaticallyReconstructHistoricalCompatibility ()

------------------------------------------------------------------------
-- 3. Machine-readable boundary.
------------------------------------------------------------------------

record Trialectic369Selected3BLinearCoreCompatibilityBoundary : Set where
  constructor trialectic-369-selected3b-linear-core-compatibility-boundary
  field
    historicalCoreAloneSufficesForCanonicalCore : Bool
    historicalCorePlusHomWeldCompilesCanonicalCore : Bool
    historicalCorePlusHomWeldCompilesSameLinearRoute : Bool
    canonicalCoreRequiresHistoricalReversePromotion : Bool
    historicalExtraFieldsRemainAvailableForProvenance : Bool

canonicalTrialectic369Selected3BLinearCoreCompatibilityBoundary :
  Trialectic369Selected3BLinearCoreCompatibilityBoundary
canonicalTrialectic369Selected3BLinearCoreCompatibilityBoundary =
  trialectic-369-selected3b-linear-core-compatibility-boundary
    false true true false true
