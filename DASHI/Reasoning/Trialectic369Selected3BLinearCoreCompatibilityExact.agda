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
import DASHI.Reasoning.Trialectic369Selected3BConstituentRetractionExact as Retraction
import DASHI.Reasoning.Trialectic369Selected3BProjectedActionMaxCutExact as Projected

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
-- 1b. Historical action equation forgets to the canonical action equation.
------------------------------------------------------------------------

historicalActionToCanonical :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K})
    (homWeld :
      Canonical.CanonicalLinearHomSameObjectWeld
        (Historical.linearZetaProducer core)
        (Historical.multiplicityHomSpace core)) →
  Historical.Selected3BNormalizerActionIntertwiningOnly
    (Historical.scaffoldFromCore core) →
  Canonical.CanonicalSelected3BActionIntertwining
    (canonicalCoreFromHistoricalCore core homWeld)
historicalActionToCanonical core homWeld action =
  record
    { intertwines =
        Historical.normalizerActionIntertwines action
    }

historicalCoreMinCutToCanonicalCompletion :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K})
    (homWeld :
      Canonical.CanonicalLinearHomSameObjectWeld
        (Historical.linearZetaProducer core)
        (Historical.multiplicityHomSpace core))
    (action :
      Historical.Selected3BNormalizerActionIntertwiningOnly
        (Historical.scaffoldFromCore core)) →
  Canonical.CanonicalSelected3BLinearCompletion {Monster} {K}
historicalCoreMinCutToCanonicalCompletion core homWeld action =
  record
    { core = canonicalCoreFromHistoricalCore core homWeld
    ; actionIntertwining =
        historicalActionToCanonical core homWeld action
    }

------------------------------------------------------------------------
-- 1c. Historical action + canonical retraction compiles the projected route.
------------------------------------------------------------------------

historicalActionToProjectedReceipt :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K})
    (homWeld :
      Canonical.CanonicalLinearHomSameObjectWeld
        (Historical.linearZetaProducer core)
        (Historical.multiplicityHomSpace core))
    (retraction :
      Retraction.ConstituentRetraction
        (canonicalCoreFromHistoricalCore core homWeld)) →
  Historical.Selected3BNormalizerActionIntertwiningOnly
    (Historical.scaffoldFromCore core) →
  Projected.SelectedActionIsProjectedFullGrade
    (canonicalCoreFromHistoricalCore core homWeld)
    retraction
historicalActionToProjectedReceipt core homWeld retraction action =
  Projected.projectedActionFromCanonicalIntertwining
    (canonicalCoreFromHistoricalCore core homWeld)
    retraction
    (historicalActionToCanonical core homWeld action)

historicalActionAndRetractionToCanonicalCompletion :
  ∀ {Monster K}
    (core :
      Historical.Selected3BLinearAcquisitionCore {Monster} {K})
    (homWeld :
      Canonical.CanonicalLinearHomSameObjectWeld
        (Historical.linearZetaProducer core)
        (Historical.multiplicityHomSpace core))
    (retraction :
      Retraction.ConstituentRetraction
        (canonicalCoreFromHistoricalCore core homWeld))
    (action :
      Historical.Selected3BNormalizerActionIntertwiningOnly
        (Historical.scaffoldFromCore core)) →
  Canonical.CanonicalSelected3BLinearCompletion {Monster} {K}
historicalActionAndRetractionToCanonicalCompletion
  core homWeld retraction action =
  Projected.canonicalCompletionFromProjectedAction
    (canonicalCoreFromHistoricalCore core homWeld)
    retraction
    (historicalActionToProjectedReceipt
      core homWeld retraction action)

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
    historicalActionEquationCompilesCanonicalAction : Bool
    historicalCoreMinCutCompilesCanonicalCompletion : Bool
    historicalActionPlusRetractionCompilesProjectedReceipt : Bool
    historicalActionPlusRetractionCompilesCanonicalCompletion : Bool
    canonicalCoreRequiresHistoricalReversePromotion : Bool
    historicalExtraFieldsRemainAvailableForProvenance : Bool

canonicalTrialectic369Selected3BLinearCoreCompatibilityBoundary :
  Trialectic369Selected3BLinearCoreCompatibilityBoundary
canonicalTrialectic369Selected3BLinearCoreCompatibilityBoundary =
  trialectic-369-selected3b-linear-core-compatibility-boundary
    false true true true true true true false true
