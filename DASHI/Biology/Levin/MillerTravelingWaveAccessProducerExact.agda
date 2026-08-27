module DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.TravelingFieldControl as Field
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave
import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- Earl K. Miller, Scott L. Brincat, Jefferson E. Roy,
-- "Analog Cognition and Consciousness" (2026).
-- PsyArXiv preprint DOI: 10.31234/osf.io/z48x7_v3.
-- The Journal of Neuroscience version is the motivating theory; this file does
-- not invent a separate journal DOI where one is not recorded by this atlas.
--
-- Sayak Bhattacharya, Scott L. Brincat, Mikael Lundqvist, Earl K. Miller,
-- "Traveling waves in the prefrontal cortex during working memory" (2022).
-- DOI: 10.1371/journal.pcbi.1009827.
--
-- Mikael Lundqvist, Scott L. Brincat, Jonas Rose, Melissa R. Warden,
-- Timothy J. Buschman, Earl K. Miller, Pawel Herman,
-- "Working memory control dynamics follow principles of spatial computing"
-- (2023). DOI: 10.1038/s41467-023-36555-4.
--
-- The exact finite theorems below are DASHI constructions.  The sources
-- motivate traveling/spatial control; they do not prove these Agda equations.
------------------------------------------------------------------------

data Site2 : Set where leftSite rightSite : Site2
data Tick2 : Set where firstTick secondTick : Tick2
data Phase2 : Set where crestPhase troughPhase : Phase2

data FrequencyBand : Set where betaBand gammaBand : FrequencyBand

phaseAt : Site2 → Tick2 → Phase2
phaseAt leftSite firstTick = crestPhase
phaseAt rightSite firstTick = troughPhase
phaseAt leftSite secondTick = troughPhase
phaseAt rightSite secondTick = crestPhase

amplitudeAt : Site2 → Tick2 → Nat
amplitudeAt leftSite firstTick = suc zero
amplitudeAt rightSite firstTick = zero
amplitudeAt leftSite secondTick = zero
amplitudeAt rightSite secondTick = suc zero

excitabilityAt : Site2 → Tick2 → Bool
excitabilityAt leftSite firstTick = true
excitabilityAt rightSite firstTick = false
excitabilityAt leftSite secondTick = false
excitabilityAt rightSite secondTick = true

canonicalTravelingField :
  Field.TravelingFieldSystem Site2 Tick2 Phase2 Nat Bool
canonicalTravelingField = record
  { Field.phaseAt = phaseAt
  ; Field.amplitudeAt = amplitudeAt
  ; Field.excitabilityAt = excitabilityAt
  ; Field.fieldModulatesSpikeTiming = true
  ; Field.fieldPatternMovesAcrossCarrier = true
  ; Field.contextCanSelectFieldPattern = true
  ; Field.interpretation =
      "finite moving stencil: field-supported excitability moves across a fixed two-site carrier"
  }

recruitedAt : Tick2 → Site2 → Bool
recruitedAt t x = excitabilityAt x t

leftRecruitmentMovesAway :
  recruitedAt firstTick leftSite ≡ true
leftRecruitmentMovesAway = refl

leftRecruitmentLaterClosed :
  recruitedAt secondTick leftSite ≡ false
leftRecruitmentLaterClosed = refl

rightRecruitmentMovesIn :
  recruitedAt firstTick rightSite ≡ false
rightRecruitmentMovesIn = refl

rightRecruitmentLaterOpen :
  recruitedAt secondTick rightSite ≡ true
rightRecruitmentLaterOpen = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

movingSupportActuallyChanges :
  recruitedAt firstTick leftSite ≡ recruitedAt secondTick leftSite → ⊥
movingSupportActuallyChanges = trueNotFalse

waveFastAccessField : Access.FastAccessControlField
waveFastAccessField = record
  { Access.Carrier = Site2
  ; Access.Time = Tick2
  ; Access.Context = FrequencyBand
  ; Access.accessAt = λ t band site → accessByBand band t site
  }
  where
    accessByBand : FrequencyBand → Tick2 → Site2 → Bool
    accessByBand betaBand t site = recruitedAt t site
    accessByBand gammaBand t site = recruitedAt t site

waveRetentionWithoutRewiring :
  Access.RetentionWithoutAccessWitness waveFastAccessField
waveRetentionWithoutRewiring =
  Access.retentionWithoutAccessWitness
    leftSite firstTick secondTick betaBand
    true false refl refl trueNotFalse

canonicalWaveCarrier : Wave.WaveCarrier Site2 Phase2 Nat FrequencyBand
canonicalWaveCarrier = record
  { Wave.phaseAt = λ site → phaseAt site firstTick
  ; Wave.amplitudeAt = λ site → amplitudeAt site firstTick
  ; Wave.frequency = betaBand
  ; Wave.travels = true
  }

record MillerWaveAccessBoundary : Set where
  constructor millerWaveAccessBoundary
  field
    waveProducerIsPNFSemanticRevision : Bool
    travelingWaveAloneIsComputation : Bool
    fieldControlReplacesSynapticStorage : Bool
    consciousnessIdentityPromoted : Bool

canonicalMillerWaveAccessBoundary : MillerWaveAccessBoundary
canonicalMillerWaveAccessBoundary =
  millerWaveAccessBoundary false false false false
