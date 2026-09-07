module DASHI.Core.PluralEpistemicProgressMethodologyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Salience
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform
import DASHI.Core.ProvenanceQuorumAdequacyBidiExact as Quorum
import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Provenance
import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss

------------------------------------------------------------------------
-- PLURAL EPISTEMIC PROGRESS METHODOLOGY
--
-- Useful epistemic progress is not identified with one mechanism. A consumer
-- may progress by narrowing the live hypothesis set, reformulating the question,
-- establishing provenance independence, or adding genuinely new information
-- after a projection has collapsed a relevant distinction.
------------------------------------------------------------------------

data EpistemicProgressRoute : Set where
  narrowLiveSet : EpistemicProgressRoute
  reformulateQuestion : EpistemicProgressRoute
  establishIndependentProvenance : EpistemicProgressRoute
  addNewCoordinate : EpistemicProgressRoute


record EpistemicProgressReceipt : Set where
  constructor epistemic-progress-receipt
  field
    route : EpistemicProgressRoute
    consumerReference : String
    routeReference : String
    authorityReference : String

open EpistemicProgressReceipt public

salienceRouteHasStrictNarrowing :
  Salience.SalientOn Salience.smallSeparating Salience.toyLive
salienceRouteHasStrictNarrowing = Salience.smallResidualIsSalient

reformulationRouteMayCloseWithoutNarrowing :
  Reform.QuestionClosed Reform.reformulatedQuestion
reformulationRouteMayCloseWithoutNarrowing = Reform.reformulatedQuestionClosed

reformulationRouteMayLeaveFibreDefinitionallySame :
  Reform.fibreAfter ≡ Reform.fibreBefore
reformulationRouteMayLeaveFibreDefinitionallySame = Reform.reformulationLeavesFibreUntouched

headcountRouteDoesNotCreateIndependentProvenance :
  Quorum.IndependentProvenanceQuorumTwo
    Provenance.toyPolicy
    Provenance.targetConsumer
    Provenance.firstReport
    Provenance.secondReport → ⊥
headcountRouteDoesNotCreateIndependentProvenance =
  Quorum.toyHeadcountDoesNotCreateIndependentQuorum

collapsedPairStaysCollapsedUnderDeterministicPostprocessing :
  Loss.toyDownstream (Loss.toyObserve Loss.x)
  ≡ Loss.toyDownstream (Loss.toyObserve Loss.y)
collapsedPairStaysCollapsedUnderDeterministicPostprocessing =
  Loss.toyCollapsedPairNeverRestored

data EveryEpistemicProgressShrinksFibre : Set where
data EveryClosureIsIdentification : Set where
data MoreDocumentsMeanIndependentCorroboration : Set where
data DeterministicPostprocessingRestoresLostDistinction : Set where

epistemicProgressNeedNotShrinkFibre : EveryEpistemicProgressShrinksFibre → ⊥
epistemicProgressNeedNotShrinkFibre ()

closureNeedNotBeIdentification : EveryClosureIsIdentification → ⊥
closureNeedNotBeIdentification ()

documentMultiplicityDoesNotCreateIndependentCorroboration :
  MoreDocumentsMeanIndependentCorroboration → ⊥
documentMultiplicityDoesNotCreateIndependentCorroboration ()

postprocessingDoesNotRestoreLostDistinction :
  DeterministicPostprocessingRestoresLostDistinction → ⊥
postprocessingDoesNotRestoreLostDistinction ()

record PluralEpistemicProgressBoundary : Set where
  constructor plural-epistemic-progress-boundary
  field
    progressMayNarrowLiveSet : Bool
    progressMayReformulateQuestion : Bool
    progressMayClarifyProvenance : Bool
    progressMayRequireNewCoordinate : Bool
    everyProgressRouteShrinksFibre : Bool
    progressCreatesActionAuthority : Bool

canonicalPluralEpistemicProgressBoundary : PluralEpistemicProgressBoundary
canonicalPluralEpistemicProgressBoundary =
  plural-epistemic-progress-boundary true true true true false false
