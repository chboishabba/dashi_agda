module DASHI.Law.MissingnessAssumptionBoundTransportBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.PartialIdentificationMissingnessBoundsExact as Bounds
import DASHI.Law.MissingnessMechanismFibreExact as Mechanism

------------------------------------------------------------------------
-- Bound transport.  Worst-case bounds are always available from unresolved
-- mass.  Narrower bounds require an explicit mechanism receipt.
------------------------------------------------------------------------

data BoundPolicy : Set where
  unrestrictedWorstCase
  independenceConditioned
  observedCovariateConditioned : BoundPolicy

record BoundTransportRequest : Set where
  constructor boundTransportRequest
  field
    rawBounds : Bounds.RatioBounds
    mechanism : Mechanism.MissingnessMechanismFibre
    policy : BoundPolicy
    assumptionReceiptPresent : Bool
    transportReference : String

open BoundTransportRequest public

data BoundTransportStatus : Set where
  worstCaseRetained
  narrowedUnderReceiptedAssumption
  assumptionReceiptMissing
  mechanismIncompatible

transportStatus : BoundTransportRequest → BoundTransportStatus
transportStatus r with policy r
... | unrestrictedWorstCase = worstCaseRetained
... | independenceConditioned with assumptionReceiptPresent r | Mechanism.classifyMechanism (mechanism r)
...   | false | _ = assumptionReceiptMissing
...   | true | Mechanism.observationIndependentMissingness = narrowedUnderReceiptedAssumption
...   | true | _ = mechanismIncompatible
... | observedCovariateConditioned with assumptionReceiptPresent r | Mechanism.classifyMechanism (mechanism r)
...   | false | _ = assumptionReceiptMissing
...   | true | Mechanism.observedCovariateConditionedMissingness = narrowedUnderReceiptedAssumption
...   | true | _ = mechanismIncompatible

------------------------------------------------------------------------
-- BIDI promotion: stronger consumers require mechanism-specific producers.
------------------------------------------------------------------------

data BoundConsumer : Set where
  conservativeIdentifiedSet
  tightenedIdentifiedSet
  completeCasePopulationRate : BoundConsumer

data BoundProducer : Set where
  unresolvedMassBoundsProducer
  explicitMechanismReceiptProducer
  completeCaseTransportProducer : BoundProducer

reverseBoundConsumer : BoundConsumer → BoundProducer
reverseBoundConsumer conservativeIdentifiedSet = unresolvedMassBoundsProducer
reverseBoundConsumer tightenedIdentifiedSet = explicitMechanismReceiptProducer
reverseBoundConsumer completeCasePopulationRate = completeCaseTransportProducer

record BoundTransportCutset : Set where
  constructor boundTransportCutset
  field
    rawBoundsClosed : Bool
    mechanismReceiptClosed : Bool
    completeCaseTransportClosed : Bool
    cutsetReference : String

open BoundTransportCutset public

data BoundTransportResidual : Set where
  rawBoundsResidual mechanismReceiptResidual completeCaseTransportResidual boundTransportClosed : BoundTransportResidual

firstBoundTransportResidual : BoundConsumer → BoundTransportCutset → BoundTransportResidual
firstBoundTransportResidual conservativeIdentifiedSet c with rawBoundsClosed c
... | false = rawBoundsResidual
... | true = boundTransportClosed
firstBoundTransportResidual tightenedIdentifiedSet c with rawBoundsClosed c
... | false = rawBoundsResidual
... | true with mechanismReceiptClosed c
...   | false = mechanismReceiptResidual
...   | true = boundTransportClosed
firstBoundTransportResidual completeCasePopulationRate c with completeCaseTransportClosed c
... | false = completeCaseTransportResidual
... | true = boundTransportClosed

------------------------------------------------------------------------
-- Regressions.
------------------------------------------------------------------------

canonicalRawBounds : Bounds.RatioBounds
canonicalRawBounds = Bounds.ratioBounds 12 18 40 53
  "synthetic raw identified set"
  "derived without missingness-independence assumptions"

canonicalUnrestrictedRequest : BoundTransportRequest
canonicalUnrestrictedRequest = boundTransportRequest
  canonicalRawBounds
  Mechanism.canonicalUnrestrictedMechanism
  unrestrictedWorstCase
  false
  "worst-case transport requires no narrowing assumption"

canonicalUnrestrictedRetained :
  transportStatus canonicalUnrestrictedRequest ≡ worstCaseRetained
canonicalUnrestrictedRetained = refl

canonicalMissingReceiptRequest : BoundTransportRequest
canonicalMissingReceiptRequest = boundTransportRequest
  canonicalRawBounds
  Mechanism.canonicalIndependentMechanism
  independenceConditioned
  false
  "independence-shaped mechanism but no receipt supplied"

canonicalMissingReceiptBlocksNarrowing :
  transportStatus canonicalMissingReceiptRequest ≡ assumptionReceiptMissing
canonicalMissingReceiptBlocksNarrowing = refl

canonicalReceiptedIndependentRequest : BoundTransportRequest
canonicalReceiptedIndependentRequest = boundTransportRequest
  canonicalRawBounds
  Mechanism.canonicalIndependentMechanism
  independenceConditioned
  true
  "synthetic explicit independence receipt"

canonicalReceiptedIndependentAllowsNarrowing :
  transportStatus canonicalReceiptedIndependentRequest ≡ narrowedUnderReceiptedAssumption
canonicalReceiptedIndependentAllowsNarrowing = refl

canonicalOutcomeDependentRejected : BoundTransportRequest
canonicalOutcomeDependentRejected = boundTransportRequest
  canonicalRawBounds
  Mechanism.canonicalOutcomeDependentMechanism
  independenceConditioned
  true
  "receipt cannot override incompatible mechanism fibre"

canonicalOutcomeDependentCannotUseIndependenceNarrowing :
  transportStatus canonicalOutcomeDependentRejected ≡ mechanismIncompatible
canonicalOutcomeDependentCannotUseIndependenceNarrowing = refl

canonicalTighteningOpenAtMechanism :
  firstBoundTransportResidual tightenedIdentifiedSet
    (boundTransportCutset true false false "raw bounds close; mechanism receipt open")
  ≡ mechanismReceiptResidual
canonicalTighteningOpenAtMechanism = refl

record BoundTransportBoundary : Set where
  constructor boundTransportBoundary
  field
    worstCaseBoundsRequireIndependenceAssumption : Bool
    worstCaseBoundsRequireIndependenceAssumptionIsFalse :
      worstCaseBoundsRequireIndependenceAssumption ≡ false
    tightenedBoundsMayOmitAssumptionReceipt : Bool
    tightenedBoundsMayOmitAssumptionReceiptIsFalse :
      tightenedBoundsMayOmitAssumptionReceipt ≡ false
    completeCaseAnalysisAutomaticallyGeneralises : Bool
    completeCaseAnalysisAutomaticallyGeneralisesIsFalse :
      completeCaseAnalysisAutomaticallyGeneralises ≡ false

canonicalBoundTransportBoundary : BoundTransportBoundary
canonicalBoundTransportBoundary = boundTransportBoundary false refl false refl false refl
