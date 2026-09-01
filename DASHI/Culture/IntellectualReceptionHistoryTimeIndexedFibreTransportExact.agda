module DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreTransportExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.IntellectualReceptionHistoryTimeIndexedFibreExact as Fibre
import DASHI.Culture.IntellectualReceptionTemporalMultiResidueAdmissibilityExact as Temporal

------------------------------------------------------------------------
-- 1. Proof-relevant temporal transport along a fixed history.
------------------------------------------------------------------------

data NextTime : Temporal.ReceptionTime → Temporal.ReceptionTime → Set where
  t01 : NextTime Temporal.t0 Temporal.t1
  t12 : NextTime Temporal.t1 Temporal.t2
  t23 : NextTime Temporal.t2 Temporal.t3

record FibreTransport
    (history : Temporal.TemporalReceptionHistory)
    (from to : Temporal.ReceptionTime) : Set where
  constructor fibre-transport
  field
    temporalStep : NextTime from to
    source : Fibre.HistoryTimeIndexedReceptionFibre
    target : Fibre.HistoryTimeIndexedReceptionFibre
    sourceIsCanonical : source ≡ Fibre.fibreAt history from
    targetIsCanonical : target ≡ Fibre.fibreAt history to

open FibreTransport public

transport01 :
  (history : Temporal.TemporalReceptionHistory) →
  FibreTransport history Temporal.t0 Temporal.t1
transport01 history =
  fibre-transport t01
    (Fibre.fibreAt history Temporal.t0)
    (Fibre.fibreAt history Temporal.t1)
    refl refl

transport12 :
  (history : Temporal.TemporalReceptionHistory) →
  FibreTransport history Temporal.t1 Temporal.t2
transport12 history =
  fibre-transport t12
    (Fibre.fibreAt history Temporal.t1)
    (Fibre.fibreAt history Temporal.t2)
    refl refl

transport23 :
  (history : Temporal.TemporalReceptionHistory) →
  FibreTransport history Temporal.t2 Temporal.t3
transport23 history =
  fibre-transport t23
    (Fibre.fibreAt history Temporal.t2)
    (Fibre.fibreAt history Temporal.t3)
    refl refl

------------------------------------------------------------------------
-- 2. Transport can change the fine fibre while preserving coarse present.
------------------------------------------------------------------------

archiveTransport12 :
  FibreTransport Temporal.archiveTemporalHistory Temporal.t1 Temporal.t2
archiveTransport12 = transport12 Temporal.archiveTemporalHistory

archiveTransportPreservesPresent :
  Fibre.present (source archiveTransport12)
  ≡ Fibre.present (target archiveTransport12)
archiveTransportPreservesPresent = refl

archiveTransportChangesPluralAdmissibility :
  Fibre.pluralEnabled (source archiveTransport12)
  ≡ Fibre.pluralEnabled (target archiveTransport12) → ⊥
archiveTransportChangesPluralAdmissibility ()

archiveTransportChangesFutureCone :
  Fibre.futureCone (source archiveTransport12)
  ≡ Fibre.futureCone (target archiveTransport12) → ⊥
archiveTransportChangesFutureCone ()

------------------------------------------------------------------------
-- 3. Same later coarse endpoint does not reconstruct transported history.
------------------------------------------------------------------------

data ReconstructedEndpointCase : Set where
  transportedEarly reconstructedLate : ReconstructedEndpointCase

data SameLaterCoarseEndpoint : Set where sameT2MovementEndpoint : SameLaterCoarseEndpoint

data TransportHistoryCode : Set where earlyAuthorityTransport lateAuthorityReconstruction : TransportHistoryCode

laterCoarseEndpoint : ReconstructedEndpointCase → SameLaterCoarseEndpoint
laterCoarseEndpoint _ = sameT2MovementEndpoint

transportHistoryCode : ReconstructedEndpointCase → TransportHistoryCode
transportHistoryCode transportedEarly = earlyAuthorityTransport
transportHistoryCode reconstructedLate = lateAuthorityReconstruction

transportHistoryCodesDiffer :
  transportHistoryCode transportedEarly
  ≡ transportHistoryCode reconstructedLate → ⊥
transportHistoryCodesDiffer ()

sameLaterCoarseEndpointCannotRecoverTransportHistory :
  INF.FactorsThrough laterCoarseEndpoint transportHistoryCode → ⊥
sameLaterCoarseEndpointCannotRecoverTransportHistory =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      transportedEarly reconstructedLate refl transportHistoryCodesDiffer)

-- Both histories agree at t2 on present, future cone and authority admissibility,
-- but one reached that fibre by carrying authority from t1 while the other
-- acquired authority only during the t1->t2 transition.

earlyAndLateSamePresentAtT2 :
  Fibre.present (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.present (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyAndLateSamePresentAtT2 = refl

earlyAndLateSameFutureAtT2 :
  Fibre.futureCone (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.futureCone (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyAndLateSameFutureAtT2 = refl

earlyAndLateSameAuthorityAtT2 :
  Fibre.authorityEnabled (Fibre.fibreAt Temporal.movementEarlyAuthorityHistory Temporal.t2)
  ≡ Fibre.authorityEnabled (Fibre.fibreAt Temporal.movementLateAuthorityHistory Temporal.t2)
earlyAndLateSameAuthorityAtT2 = refl

------------------------------------------------------------------------
-- 4. Transport history is finer than endpoint equality.
------------------------------------------------------------------------

data SameEndpointCase : Set where earlyAtT2 lateAtT2 : SameEndpointCase

data EndpointProjectionCode : Set where sameMovementAuthorityEndpoint : EndpointProjectionCode

data IncomingTransportCode : Set where carriedAuthority acquiredAuthorityOnArrival : IncomingTransportCode

endpointProjection : SameEndpointCase → EndpointProjectionCode
endpointProjection _ = sameMovementAuthorityEndpoint

incomingTransport : SameEndpointCase → IncomingTransportCode
incomingTransport earlyAtT2 = carriedAuthority
incomingTransport lateAtT2 = acquiredAuthorityOnArrival

incomingTransportDiffers :
  incomingTransport earlyAtT2 ≡ incomingTransport lateAtT2 → ⊥
incomingTransportDiffers ()

sameEndpointCannotRecoverIncomingTransport :
  INF.FactorsThrough endpointProjection incomingTransport → ⊥
sameEndpointCannotRecoverIncomingTransport =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      earlyAtT2 lateAtT2 refl incomingTransportDiffers)

------------------------------------------------------------------------
-- 5. No-promotion boundaries.
------------------------------------------------------------------------

data FibreTransportPromotesParallelTransport : Set where
data FibreTransportPromotesGaugeConnection : Set where
data EndpointEqualityPromotesTransportEquality : Set where
data TransportPromotesActualHistory : Set where

fibreTransportDoesNotPromoteParallelTransport : FibreTransportPromotesParallelTransport → ⊥
fibreTransportDoesNotPromoteParallelTransport ()

fibreTransportDoesNotPromoteGaugeConnection : FibreTransportPromotesGaugeConnection → ⊥
fibreTransportDoesNotPromoteGaugeConnection ()

endpointEqualityDoesNotPromoteTransportEquality : EndpointEqualityPromotesTransportEquality → ⊥
endpointEqualityDoesNotPromoteTransportEquality ()

transportDoesNotPromoteActualHistory : TransportPromotesActualHistory → ⊥
transportDoesNotPromoteActualHistory ()

------------------------------------------------------------------------
-- 6. Canonical boundary.
------------------------------------------------------------------------

record IntellectualReceptionFibreTransportBoundary : Set where
  constructor intellectual-reception-fibre-transport-boundary
  field
    transportIsProofRelevantAlongHistory : Bool
    transportCanChangeFineFibreWithSamePresent : Bool
    sameLaterEndpointDeterminesIncomingTransport : Bool
    endpointReconstructionEqualsTransportedHistory : Bool
    fibreTransportIsGaugeParallelTransport : Bool
    fibreTransportIsActualHistoricalChronology : Bool
    sourceAttributionBoundarySurvivesTransportReasoning : Bool

canonicalIntellectualReceptionFibreTransportBoundary :
  IntellectualReceptionFibreTransportBoundary
canonicalIntellectualReceptionFibreTransportBoundary =
  intellectual-reception-fibre-transport-boundary
    true true false false false false true
