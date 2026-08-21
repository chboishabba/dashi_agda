module DASHI.Biology.WaveControlledCoalitionBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.ConsciousAccessCoalition as Coalition
import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller
import DASHI.Biology.Levin.CrossFrequencyEffectiveTopologyExact as CrossFrequency
import DASHI.Biology.Levin.WaveInterferenceRecruitmentExact as Interference
import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access

------------------------------------------------------------------------
-- Physical-producer -> existing access-coalition bridge.
--
-- The existing coalition remains the semantics owner.  The Miller lane only
-- supplies a candidate fast producer for time/context-dependent recruitment.
------------------------------------------------------------------------

record WaveSupportedAccessCandidate : Set₁ where
  constructor waveSupportedAccessCandidate
  field
    accessCoalition : Coalition.ConsciousAccessCoalition
    fastAccessField : Access.FastAccessControlField
    movingField :
      DASHI.Biology.Levin.TravelingFieldControl.TravelingFieldSystem
        Miller.Site2 Miller.Tick2 Miller.Phase2
        Agda.Builtin.Nat.Nat Bool
    coalitionCriteriaHold :
      Coalition.criteriaSatisfied (Coalition.criteria accessCoalition) ≡ true
    movingSupportChanges :
      Miller.recruitedAt Miller.firstTick Miller.leftSite
      ≡ Miller.recruitedAt Miller.secondTick Miller.leftSite →
      Data.Empty.⊥
    phaseCanChangeRecruitment :
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.inPhase)
      ≡
      Interference.nonzeroRecruit
        (Interference.combinedAmplitude Interference.one Interference.antiPhase) →
      Data.Empty.⊥
    candidateOnly : Coalition.candidateOnly accessCoalition ≡ true
    accessTheoryOnly : Coalition.accessTheoryOnly accessCoalition ≡ true
    phenomenalIdentityBlocked :
      Coalition.phenomenalIdentityPromoted accessCoalition ≡ false

canonicalWaveSupportedAccessCandidate : WaveSupportedAccessCandidate
canonicalWaveSupportedAccessCandidate =
  waveSupportedAccessCandidate
    Coalition.canonicalConsciousAccessCoalition
    Miller.waveFastAccessField
    Miller.canonicalTravelingField
    Coalition.canonicalCoalitionAccessCriteriaSatisfied
    Miller.movingSupportActuallyChanges
    Interference.phaseDifferenceChangesRecruitment
    (Coalition.candidateOnlyIsTrue Coalition.canonicalConsciousAccessCoalition)
    (Coalition.accessTheoryOnlyIsTrue Coalition.canonicalConsciousAccessCoalition)
    Coalition.canonicalCoalitionPhenomenalIdentityNotPromoted

sameAnatomyStillSupportsStateDependentTopology :
  CrossFrequency.betaLowOpensExistingAnatomicalEdge
  ≡ CrossFrequency.betaLowOpensExistingAnatomicalEdge
sameAnatomyStillSupportsStateDependentTopology = refl

record WaveCoalitionBoundary : Set where
  constructor waveCoalitionBoundary
  field
    waveSupportIsPhenomenalIdentity : Bool
    recurrentCoalitionProvesMillerTheory : Bool
    interferenceWitnessProvesBrainUsesAnalogComputation : Bool

canonicalWaveCoalitionBoundary : WaveCoalitionBoundary
canonicalWaveCoalitionBoundary =
  waveCoalitionBoundary false false false
