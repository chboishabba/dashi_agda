module DASHI.Governance.EpistemicHistoryResidualPayloadExact where

-- Original DASHI exact source-specific residual/observation instance.
-- Reuses existing three-task history and nonfactorability proof owners.
-- Not a video compression algorithm and not a measured cognitive burden.
-- The reversible payload stores the FULL task history as side information.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Work
import DASHI.Governance.CrossDomainResidualConsumerPreservationExact as Transport

-- The public decision alone is the coarse quotient; recording the
-- original task stream is the explicit correction/side information.
record WorkHistoryPayload : Set where
  constructor work-history-payload
  field
    publicOutcome : Work.PublicDisposition
    sideHistory : List Work.EpistemicTask
open WorkHistoryPayload public

encodeWork : List Work.EpistemicTask → WorkHistoryPayload
encodeWork events = work-history-payload
  (Work.visibleDisposition events) events

decodeWork : WorkHistoryPayload → List Work.EpistemicTask
decodeWork = sideHistory

workRoundTrip :
  (events : List Work.EpistemicTask) →
  decodeWork (encodeWork events) ≡ events
workRoundTrip events = refl

retentionAfterDecode :
  (events : List Work.EpistemicTask) →
  Work.retentionDemand (decodeWork (encodeWork events))
    ≡ Work.retentionDemand events
retentionAfterDecode events = refl

communicationAfterDecode :
  (events : List Work.EpistemicTask) →
  Work.communicationDemand (decodeWork (encodeWork events))
    ≡ Work.communicationDemand events
communicationAfterDecode events = refl

publicAfterEncode :
  (events : List Work.EpistemicTask) →
  publicOutcome (encodeWork events) ≡ Work.visibleDisposition events
publicAfterEncode events = refl

-- Encoding is injective only because the ORIGINAL task stream was
-- retained in the side-information field.
fullPayloadInjective :
  {x y : List Work.EpistemicTask} →
  encodeWork x ≡ encodeWork y →
  x ≡ y
fullPayloadInjective same = cong sideHistory same

-- Dropping the side information destroys the reconstruction guarantee.
-- This is source-level no-decoder, not a psychological diagnosis.
noLosslessDecoderAfterDroppingSideInformation :
  (decoder : Work.PublicDisposition → List Work.EpistemicTask) →
  ((events : List Work.EpistemicTask) →
     decoder (Work.visibleDisposition events) ≡ events) → ⊥
noLosslessDecoderAfterDroppingSideInformation =
  Transport.noDecoderFromPublicDisposition

-- Exact consumer transport instantiated with Unit side information.
-- The full task stream is deliberately carried by the encoded payload:
-- a formal lower bound on information retention, not an MDL victory.
data TrivialSide : Set where unitSide : TrivialSide

workConsumerTransport :
  Transport.ObservableResidualTransport
    (List Work.EpistemicTask)
    WorkHistoryPayload
    TrivialSide
    Work.TaskBurden
workConsumerTransport = record
  { encode = λ events side → encodeWork events
  ; decode = λ payload side → decodeWork payload
  ; sourceObservable = Work.foldTaskHistory
  ; encodedObservable = λ payload side → Work.foldTaskHistory (sideHistory payload)
  ; roundTrip = λ events side → refl
  ; observableCommutes = λ events side → refl
  }

workSelectedObservablePreserved :
  (events : List Work.EpistemicTask) →
  Work.foldTaskHistory
    (Transport.decode workConsumerTransport
      (Transport.encode workConsumerTransport events unitSide)
      unitSide)
    ≡ Work.foldTaskHistory events
workSelectedObservablePreserved events =
  Transport.selectedObservableAfterDecode
    workConsumerTransport events unitSide
