module DASHI.Culture.GoodmanSonicWarfareRhythmInterventionExact where

------------------------------------------------------------------------
-- GOODMAN SONIC WARFARE: RHYTHM AND CAUSAL-IDENTIFIABILITY FINITE CUT
--
-- Primary source: Steve Goodman, Sonic Warfare: Sound, Affect, and the
-- Ecology of Fear (MIT Press, 2009), DOI 10.7551/mitpress/7999.001.0001.
-- Chapters 16 (rhythmanalysis), 20 (rhythm/noise), 21 (crowds),
-- 26-32 (circulation, earworm, dub), and 34 (unsound) motivate a
-- distinction between rhythm, passive observation and causal claims.
-- Rhythmanalysis antecedents remain credited to Pinheiro dos Santos,
-- Bachelard and Lefebvre, not invented by Goodman or DASHI.
--
-- The finite theorem proofs below are new DASHI *application*
-- constructions. They reuse the prior generic theorem owners:
--   QueryIndexedProjectionAdequacyExact (Blackwell-informed)
--   IdentifiabilityActiveInformationExact (Beven, Williams et al.)
--   SnowballAttributionProvenanceInvariantExact
--
-- No observation of human listeners, new force, entrainment law,
-- acoustic exposure threshold, clinical effect, or historical
-- deployment is established by these synthetic models.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.IdentifiabilityActiveInformationExact as Ident
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- R1: A fixed event count does not determine onset/phase information.
--
-- The two distinct time-slot arrangements both contain one impulse.
-- 'event count' is a nonphysical categorical measurement here.
------------------------------------------------------------------------

data PulseTrace : Set where
  pulseAtFirstSlot : PulseTrace
  pulseAtSecondSlot : PulseTrace

data PulseCount : Set where
  onePulse : PulseCount

data PulsePhase : Set where
  firstSlot : PulsePhase
  secondSlot : PulsePhase

data PulseQuestion : Set where
  countQuestion : PulseQuestion
  phaseQuestion : PulseQuestion

data PulseAnswer : Set where
  oneCountAnswer : PulseAnswer
  firstPhaseAnswer : PulseAnswer
  secondPhaseAnswer : PulseAnswer

pulseCount : PulseTrace → PulseCount
pulseCount pulseAtFirstSlot = onePulse
pulseCount pulseAtSecondSlot = onePulse

pulsePhase : PulseTrace → PulsePhase
pulsePhase pulseAtFirstSlot = firstSlot
pulsePhase pulseAtSecondSlot = secondSlot

pulseAnswer : PulseQuestion → PulseTrace → PulseAnswer
pulseAnswer countQuestion _ = oneCountAnswer
pulseAnswer phaseQuestion pulseAtFirstSlot = firstPhaseAnswer
pulseAnswer phaseQuestion pulseAtSecondSlot = secondPhaseAnswer

pulseSemantics : Query.QuerySemantics PulseTrace PulseQuestion PulseAnswer
pulseSemantics = Query.querySemantics pulseAnswer

countIsAdequateForCount :
  Query.AdequateFor pulseCount pulseSemantics countQuestion
countIsAdequateForCount =
  Query.factorsForQuery
    {project = pulseCount}
    {semantics = pulseSemantics}
    {query = countQuestion}
    (λ _ → oneCountAnswer)
    (λ _ → refl)

countCollidesOnPhase :
  Query.QueryAdequacyDefect pulseCount pulseSemantics phaseQuestion
countCollidesOnPhase =
  Query.queryAdequacyDefect
    {project = pulseCount}
    {semantics = pulseSemantics}
    {query = phaseQuestion}
    pulseAtFirstSlot pulseAtSecondSlot refl (λ ())

countCannotRecoverPhase :
  Query.AdequateFor pulseCount pulseSemantics phaseQuestion → ⊥
countCannotRecoverPhase =
  Query.queryAdequacyDefectBlocksFactorisation countCollidesOnPhase

phaseIsAdequateForPhase :
  Query.AdequateFor pulsePhase pulseSemantics phaseQuestion
phaseIsAdequateForPhase =
  Query.factorsForQuery
    {project = pulsePhase}
    {semantics = pulseSemantics}
    {query = phaseQuestion}
    (λ { firstSlot → firstPhaseAnswer
       ; secondSlot → secondPhaseAnswer })
    (λ { pulseAtFirstSlot → refl
       ; pulseAtSecondSlot → refl })

------------------------------------------------------------------------
-- I1: Two distinct structural causal response rules are observationally
-- equivalent under a shared driver.
--
-- M_direct: X := U, Y := X.
-- M_common: X := U, Y := U.
-- With passive U=0 and U=1 both models show (X,Y)=(U,U).
-- Under controlled do(X=1), U held fixed at 0:
--   M_direct predicts (X,Y)=(1,1)
--   M_common predicts (X,Y)=(1,0).
--
-- The values are synthetic labels, NOT a real acoustic experiment.
-- The intervention is a logical diagnostic. It is not a recommendation
-- to expose anyone to sound or to use psychological manipulation.
------------------------------------------------------------------------

data SoundCausalModel : Set where
  soundDirectEffect : SoundCausalModel
  commonDriverOnly : SoundCausalModel

data SoundDesign : Set where
  passiveDriverQuiet : SoundDesign
  passiveDriverLoud : SoundDesign
  controlledSourceWithQuietDriver : SoundDesign

data SignalResponsePair : Set where
  quietSignalQuietResponse : SignalResponsePair
  loudSignalLoudResponse : SignalResponsePair
  loudSignalQuietResponse : SignalResponsePair

soundReadout : SoundDesign → SoundCausalModel → SignalResponsePair
soundReadout passiveDriverQuiet soundDirectEffect =
  quietSignalQuietResponse
soundReadout passiveDriverQuiet commonDriverOnly =
  quietSignalQuietResponse
soundReadout passiveDriverLoud soundDirectEffect =
  loudSignalLoudResponse
soundReadout passiveDriverLoud commonDriverOnly =
  loudSignalLoudResponse
soundReadout controlledSourceWithQuietDriver soundDirectEffect =
  loudSignalLoudResponse
soundReadout controlledSourceWithQuietDriver commonDriverOnly =
  loudSignalQuietResponse

soundExperimentSystem :
  Ident.ExperimentSystem SoundCausalModel SoundDesign SignalResponsePair
soundExperimentSystem = Ident.experimentSystem soundReadout

passiveDesign : SoundDesign → Bool
passiveDesign passiveDriverQuiet = true
passiveDesign passiveDriverLoud = true
passiveDesign controlledSourceWithQuietDriver = false

allDesigns : SoundDesign → Bool
allDesigns _ = true

passiveObservationsDoNotIdentifyCausalModel :
  Ident.EquivalentOn soundExperimentSystem passiveDesign
    soundDirectEffect commonDriverOnly
passiveObservationsDoNotIdentifyCausalModel =
  Ident.equivalentOn agreement
  where
    agreement :
      (design : SoundDesign) →
      passiveDesign design ≡ true →
      soundReadout design soundDirectEffect
        ≡ soundReadout design commonDriverOnly
    agreement passiveDriverQuiet _ = refl
    agreement passiveDriverLoud _ = refl
    agreement controlledSourceWithQuietDriver ()

logicalInterventionDistinguishesMechanisms :
  Ident.DistinguishingExperiment soundExperimentSystem
    soundDirectEffect commonDriverOnly
logicalInterventionDistinguishesMechanisms =
  Ident.distinguishingExperiment
    controlledSourceWithQuietDriver
    (λ ())

addingControlledInterventionBreaksEquivalence :
  Ident.EquivalentOn soundExperimentSystem allDesigns
    soundDirectEffect commonDriverOnly → ⊥
addingControlledInterventionBreaksEquivalence =
  Ident.splitterRefutesAnyFamilyContainingIt
    logicalInterventionDistinguishesMechanisms refl

------------------------------------------------------------------------
-- S1: Reuse source snowball attribution firewalls, rather than treating a
-- chain of audio uploads/versions/citations as identification or proof.
------------------------------------------------------------------------

sonicCitationCannotSupplyProof : Snowball.CitationCreatesProof → ⊥
sonicCitationCannotSupplyProof = Snowball.citationDoesNotCreateProof

sonicCitationCannotSupplyDomainAuthority :
  Snowball.CitationCreatesDomainAuthority → ⊥
sonicCitationCannotSupplyDomainAuthority =
  Snowball.citationDoesNotCreateAuthority

sonicCitationMustRetainSourceKind :
  Snowball.SourceKindCanBeDroppedAfterProjection → ⊥
sonicCitationMustRetainSourceKind =
  Snowball.sourceKindMustSnowballWhenRelevant

sonicCitationMustRetainFormalisationRelationship :
  Snowball.FormalisationRelationshipCanBeDroppedAfterProjection → ⊥
sonicCitationMustRetainFormalisationRelationship =
  Snowball.relationshipMustSnowballWhenRelevant

------------------------------------------------------------------------
-- Stop wall:
-- A synthetic pair of structural causal models demonstrates logical
-- nonidentification. It cannot choose a human behavioural mechanism.
-- Physical intervention receipts require new measured evidence and
-- independently justified consent/safety conditions.
------------------------------------------------------------------------
