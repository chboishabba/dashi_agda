module DASHI.Governance.CrossDomainResidualConsumerPreservationExact where

-- Exact cross-domain *consumer* requirements; not an identity among
-- video codec residuals, epistemic work or hormone measurements.
-- Source owners: TriadicVideoCodecObservationQuotient, EpistemicPower
-- history, situated assay gluing, IntersectionalNonFactorability.
-- Crenshaw supplies conceptual warning about lost situated relations,
-- not the mathematical proof here.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Combinatorics.TriadicVideoCodecObservationQuotient as Codec
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as Work
import DASHI.Governance.SituatedCortisolAssayGluingExact as Assay

-- A separately selected consumer observable has an explicit commuting
-- transport equation. No assumption that domains share their ontology.
record ObservableResidualTransport
  (Source Encoded Side Observable : Set) : Set₁ where
  field
    encode : Source → Side → Encoded
    decode : Encoded → Side → Source
    sourceObservable : Source → Observable
    encodedObservable : Encoded → Side → Observable
    roundTrip : (s : Source) (side : Side) →
      decode (encode s side) side ≡ s
    observableCommutes : (s : Source) (side : Side) →
      sourceObservable s ≡ encodedObservable (encode s side) side

open ObservableResidualTransport public

-- If the side information and reconstruction are available, the
-- observable computed after decoding is the SAME original observable.
selectedObservableAfterDecode :
  ∀ {Source Encoded Side Observable : Set}
  (T : ObservableResidualTransport Source Encoded Side Observable)
  (s : Source) (side : Side) →
  sourceObservable T (decode T (encode T s side) side)
  ≡ sourceObservable T s
selectedObservableAfterDecode T s side =
  cong (sourceObservable T) (roundTrip T s side)

-- Reversible consumer reconstruction implies injectivity at each chosen
-- side-information coordinate. Quotienting without side information is
-- therefore not automatically a lossless observation of situated history.
losslessEncodingIsInjective :
  ∀ {Source Encoded Side Observable : Set}
  (T : ObservableResidualTransport Source Encoded Side Observable)
  (side : Side) {x y : Source} →
  encode T x side ≡ encode T y side →
  x ≡ y
losslessEncodingIsInjective T side {x} {y} same =
  trans
    (sym (roundTrip T x side))
    (trans (cong (λ e → decode T e side) same)
      (roundTrip T y side))

-- Exact obstruction: publicly retained conclusions do not allow
-- reconstruction of the hidden work spent retaining them.
noDecoderFromPublicDisposition :
  (decode : Work.PublicDisposition →
    List Work.EpistemicTask) →
  ((history : List Work.EpistemicTask) →
    decode (Work.visibleDisposition history) ≡ history) → ⊥
noDecoderFromPublicDisposition decode recovered =
  NF.witnessRulesOutEveryFlatFactorisation
    Work.sameOutcomeDifferentRetentionHistory
    (NF.factorsThrough
      (λ p → Work.retentionDemand (decode p))
      (λ h → sym (cong Work.retentionDemand (recovered h))))

-- In the separate physiological toy owner, an integrated observation
-- cannot determine the early point value, even with arbitrary recharts.
integralDoesNotDetermineAcutePoint :
  NF.FactorsThrough Assay.integratedReadout Assay.earlyReadout → ⊥
integralDoesNotDetermineAcutePoint =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      Assay.earlyPulse Assay.latePulse refl (λ ()))

-- Real codec eligibility is a distinct source-owned receipt. The
-- witness carries an actual decoder reconstruction proposition, while
-- any equality of physical/epistemic variables remains unpaid.
record CodecToSelectedConsumer
  (codec : Codec.TriadicVideoCodecObservationQuotient)
  (ConsumerObservation : Set) : Set₁ where
  field
    codecEvidence : Codec.CodecReuseAdmissibilityWitness codec
    extractFromOriginal : Codec.FrameStream codec → ConsumerObservation
    extractFromDecoded : Codec.DecodedFrameStream codec → ConsumerObservation
    reconstructionPreservesSelectedObservation :
      (w : Codec.CodecReuseAdmissibilityWitness codec) →
      extractFromOriginal (Codec.stream w)
      ≡ extractFromDecoded (Codec.decoded w)

-- No instance identifies codec bpp, hormone concentrations and
-- epistemic cost as equal numerical quantities. Those are different
-- consumers with distinct units, observers and provenance receipts.
