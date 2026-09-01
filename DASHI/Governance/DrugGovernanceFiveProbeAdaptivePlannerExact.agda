module DASHI.Governance.DrugGovernanceFiveProbeAdaptivePlannerExact where

open import DASHI.Core.Prelude

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five

------------------------------------------------------------------------
-- FIVE-PROBE ADAPTIVE PLANNER
--
-- Every probe now has a real live collision.  A one-shot plan may close the
-- corresponding consumer without identifying the entire fine world.
------------------------------------------------------------------------

Evidence : Set
Evidence = ⊤

allCompatible : Envelope.Compatible Evidence Five.ProbeWorld
allCompatible evidence world = ⊤

------------------------------------------------------------------------
-- Generic fact: if the bundle observes exactly the declared consumer, then
-- observing one outcome closes that consumer on the refined fibre.
------------------------------------------------------------------------

bundleClosesOwnConsumer :
  ∀ {Observation : Set}
    (consumer : Five.ProbeWorld → Observation)
    (bundle : Discriminator.ExperimentBundle Five.ProbeWorld) →
    Discriminator.observe bundle ≡ consumer →
    Discriminator.ProspectivelyClosesConsumer allCompatible consumer bundle
bundleClosesOwnConsumer consumer bundle refl evidence witness compatible left right leftMeasured rightMeasured =
  trans (proj₂ leftMeasured) (sym (proj₂ rightMeasured))

subjectCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible Five.subjectPosition Five.subjectBundle
subjectCloses = bundleClosesOwnConsumer Five.subjectPosition Five.subjectBundle refl

historyCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible Five.historicalPosition Five.historyBundle
historyCloses = bundleClosesOwnConsumer Five.historicalPosition Five.historyBundle refl

authorityCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible Five.authorityPosition Five.authorityBundle
authorityCloses = bundleClosesOwnConsumer Five.authorityPosition Five.authorityBundle refl

materialCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible Five.materialRoute Five.materialBundle
materialCloses = bundleClosesOwnConsumer Five.materialRoute Five.materialBundle refl

sovereigntyCloses :
  Discriminator.ProspectivelyClosesConsumer
    allCompatible Five.sovereigntyPosition Five.sovereigntyBundle
sovereigntyCloses = bundleClosesOwnConsumer Five.sovereigntyPosition Five.sovereigntyBundle refl

subjectPlan : Sequential.SequentialConsumerPlan Five.subjectPosition (allCompatible tt)
subjectPlan = Sequential.oneShotConsumerClosingPlan
  allCompatible Five.subjectPosition tt Five.subjectBundle subjectCloses

historyPlan : Sequential.SequentialConsumerPlan Five.historicalPosition (allCompatible tt)
historyPlan = Sequential.oneShotConsumerClosingPlan
  allCompatible Five.historicalPosition tt Five.historyBundle historyCloses

authorityPlan : Sequential.SequentialConsumerPlan Five.authorityPosition (allCompatible tt)
authorityPlan = Sequential.oneShotConsumerClosingPlan
  allCompatible Five.authorityPosition tt Five.authorityBundle authorityCloses

materialPlan : Sequential.SequentialConsumerPlan Five.materialRoute (allCompatible tt)
materialPlan = Sequential.oneShotConsumerClosingPlan
  allCompatible Five.materialRoute tt Five.materialBundle materialCloses

sovereigntyPlan : Sequential.SequentialConsumerPlan Five.sovereigntyPosition (allCompatible tt)
sovereigntyPlan = Sequential.oneShotConsumerClosingPlan
  allCompatible Five.sovereigntyPosition tt Five.sovereigntyBundle sovereigntyCloses

------------------------------------------------------------------------
-- All five formerly declared/candidate probes now own actual separator receipts.
------------------------------------------------------------------------

record FiveLiveSeparators : Set where
  constructor fiveLiveSeparators
  field
    subject : Discriminator.BundleSeparates Five.subjectBundle Five.baseExternalWorld Five.subjectAuthoredWorld
    history : Discriminator.BundleSeparates Five.historyBundle Five.baseExternalWorld Five.historyRetainedWorld
    authority : Discriminator.BundleSeparates Five.authorityBundle Five.baseExternalWorld Five.authorityRechartedWorld
    material : Discriminator.BundleSeparates Five.materialBundle Five.baseExternalWorld Five.sharedBenefitWorld
    sovereignty : Discriminator.BundleSeparates Five.sovereigntyBundle Five.baseExternalWorld Five.sovereignWorld

canonicalFiveLiveSeparators : FiveLiveSeparators
canonicalFiveLiveSeparators = fiveLiveSeparators
  Five.subjectSeparates
  Five.historySeparates
  Five.authoritySeparates
  Five.materialSeparates
  Five.sovereigntySeparates

------------------------------------------------------------------------
-- Closure stays consumer-indexed.
------------------------------------------------------------------------

data AuthorityClosurePromotesMaterialClosure : Set where

data MaterialClosurePromotesSovereigntyClosure : Set where

data SovereigntyClosurePromotesHistoricalClosure : Set where

data FiveOneShotPlansPromoteOneUniversalOntology : Set where

authorityClosureDoesNotPromoteMaterialClosure : AuthorityClosurePromotesMaterialClosure → ⊥
authorityClosureDoesNotPromoteMaterialClosure ()

materialClosureDoesNotPromoteSovereigntyClosure : MaterialClosurePromotesSovereigntyClosure → ⊥
materialClosureDoesNotPromoteSovereigntyClosure ()

sovereigntyClosureDoesNotPromoteHistory : SovereigntyClosurePromotesHistoricalClosure → ⊥
sovereigntyClosureDoesNotPromoteHistory ()

fivePlansDoNotPromoteUniversalOntology : FiveOneShotPlansPromoteOneUniversalOntology → ⊥
fivePlansDoNotPromoteUniversalOntology ()

record FiveProbeAdaptivePlannerBoundary : Set where
  constructor fiveProbeAdaptivePlannerBoundary
  field
    allFiveProbesOwnLiveSeparatorWitnesses : Bool
    allFiveProbesOwnLiveSeparatorWitnessesIsTrue : allFiveProbesOwnLiveSeparatorWitnesses ≡ true
    eachProbeCanCloseItsOwnDeclaredConsumer : Bool
    eachProbeCanCloseItsOwnDeclaredConsumerIsTrue : eachProbeCanCloseItsOwnDeclaredConsumer ≡ true
    oneProbeClosesAllFiveConsumers : Bool
    oneProbeClosesAllFiveConsumersIsFalse : oneProbeClosesAllFiveConsumers ≡ false
    consumerClosureRequiresWholeWorldIdentity : Bool
    consumerClosureRequiresWholeWorldIdentityIsFalse : consumerClosureRequiresWholeWorldIdentity ≡ false

canonicalFiveProbeAdaptivePlannerBoundary : FiveProbeAdaptivePlannerBoundary
canonicalFiveProbeAdaptivePlannerBoundary =
  fiveProbeAdaptivePlannerBoundary true refl true refl false refl false refl
