module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseZhengCui2018AcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCitationNeighbourhoodExact as Atlas

------------------------------------------------------------------------
-- ZHENG-CUI 2018 CITING-SOURCE ACQUISITION
--
-- PubMed/ACS source text pays the following for apo adenylate kinase:
--   * extensive ~50 microsecond explicit-solvent atomistic simulation;
--   * Markov-state analysis;
--   * a closed basin in which the NMP domain remains open while LID closes and
--     rotates toward it;
--   * multiple pathways and time scales for open/close transitions;
--   * similar key pathway/time-scale features across two fixed-charge force fields;
--   * no evidence for a significant degree of local unfolding during transition.
--
-- The authors also state that their computed closed-ensemble properties are
-- consistent with previously reported FRET/PRE measurements while interpreting
-- NMP closure as likely following AMP binding.  DASHI retains this as the
-- Zheng-Cui study's source-local interpretation.  It does not overwrite the
-- Li-Liu-Ji state graph or FRET interpretation, and citation does not import
-- Li-Liu-Ji numeric cells.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Atlas.zhengCui2018Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

record ZhengCuiObservation : Set where
  constructor zheng-cui-observation
  field
    label : String
    sourceLocator : String
    interpretation : String
open ZhengCuiObservation public

samplingObservation : ZhengCuiObservation
samplingObservation = zheng-cui-observation
  "~50 microsecond apo-AdK explicit-solvent atomistic sampling"
  "Zheng-Cui 2018 abstract: extensive (~50 microseconds) explicit solvent atomistic simulations and Markov state analysis"
  "source-paid computational sampling scale and analysis method; not an experimental observation duration"

closedBasinObservation : ZhengCuiObservation
closedBasinObservation = zheng-cui-observation
  "apo closed basin with open NMP and closed/rotated LID"
  "Zheng-Cui 2018 abstract: closed basin of apo AK features an open NMP domain while LID closes and rotates toward it"
  "source-paid basin/domain-state description; 'closed basin' is study-local and is not identified definitionally with Li-Liu-Ji zeta/xi or a fully closed crystal state"

fretPreInterpretation : ZhengCuiObservation
fretPreInterpretation = zheng-cui-observation
  "computed closed-ensemble properties consistent with prior FRET/PRE but NMP closure likely follows AMP binding"
  "Zheng-Cui 2018 abstract"
  "source-local interpretation of prior measurements; consistency is not identity of observables or experiments"

multiplePathwayObservation : ZhengCuiObservation
multiplePathwayObservation = zheng-cui-observation
  "kinetically heterogeneous closed ensemble with multiple pathways and time scales"
  "Zheng-Cui 2018 abstract"
  "source-paid computational heterogeneity; no Li-Liu-Ji edge-rate or route-label transfer"

twoForceFieldObservation : ZhengCuiObservation
twoForceFieldObservation = zheng-cui-observation
  "key transition-pathway features and time scales robust/similar across two fixed-charge force fields"
  "Zheng-Cui 2018 abstract"
  "within-study robustness statement; not a universal force-field-invariance theorem"

localUnfoldingObservation : ZhengCuiObservation
localUnfoldingObservation = zheng-cui-observation
  "no evidence for significant local unfolding during the observed transition"
  "Zheng-Cui 2018 abstract"
  "negative evidence within the sampled/modelled transition ensemble; not proof that local unfolding is impossible in every AdK context"

------------------------------------------------------------------------
-- Cross-source interpretation boundary.
------------------------------------------------------------------------

data CitationImportsLiNumericCells : Set where
data ClosedLabelEqualsLiClosedState : Set where
data SimulationTimescaleEqualsExperimentalKinetics : Set where
data ConsistentWithFretMeansSameObservable : Set where
data TwoForceFieldRobustnessMeansUniversalMechanism : Set where
data NoObservedUnfoldingMeansUnfoldingImpossible : Set where

citationDoesNotImportLiNumericCells : CitationImportsLiNumericCells → ⊥
citationDoesNotImportLiNumericCells ()
closedLabelDoesNotCreateLiStateIdentity : ClosedLabelEqualsLiClosedState → ⊥
closedLabelDoesNotCreateLiStateIdentity ()
simulationTimescaleDoesNotBecomeExperimentalKinetics : SimulationTimescaleEqualsExperimentalKinetics → ⊥
simulationTimescaleDoesNotBecomeExperimentalKinetics ()
fretConsistencyDoesNotCreateSameObservable : ConsistentWithFretMeansSameObservable → ⊥
fretConsistencyDoesNotCreateSameObservable ()
forceFieldRobustnessDoesNotCreateUniversalMechanism : TwoForceFieldRobustnessMeansUniversalMechanism → ⊥
forceFieldRobustnessDoesNotCreateUniversalMechanism ()
noObservedUnfoldingDoesNotMakeUnfoldingImpossible : NoObservedUnfoldingMeansUnfoldingImpossible → ⊥
noObservedUnfoldingDoesNotMakeUnfoldingImpossible ()

record ZhengCui2018AcquisitionBoundary : Set where
  constructor zheng-cui-2018-acquisition-boundary
  field
    approxFiftyMicrosecondSamplingPaid : Bool
    markovStateAnalysisPaid : Bool
    closedBasinOpenNmpLidClosedPaid : Bool
    multiplePathwaysAndTimescalesPaid : Bool
    twoForceFieldRobustnessPaid : Bool
    noSignificantLocalUnfoldingPaid : Bool
    citationImportsLiNumericCells : Bool
    closedLabelEqualsLiClosedState : Bool
    simulationTimescaleEqualsExperimentalKinetics : Bool
    consistentWithFretMeansSameObservable : Bool
    twoForceFieldRobustnessMeansUniversalMechanism : Bool
    noObservedUnfoldingMeansUnfoldingImpossible : Bool
    sourceLocalAttributionRetained : Bool
open ZhengCui2018AcquisitionBoundary public

canonicalZhengCui2018AcquisitionBoundary : ZhengCui2018AcquisitionBoundary
canonicalZhengCui2018AcquisitionBoundary = zheng-cui-2018-acquisition-boundary
  true true true true true true
  false false false false false false
  true
