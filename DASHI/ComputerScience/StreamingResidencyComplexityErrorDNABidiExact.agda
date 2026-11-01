module DASHI.ComputerScience.StreamingResidencyComplexityErrorDNABidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.ComputerScience.AgdaElaborationResidencyComplexityExact as Residency
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as Wrong
import Ontology.DNA.Supervoxel4Adic as DNA
import Ontology.DNA.CriticallySampledDNA4Transform as Critical
import Ontology.DNA.StreamingEncoderSurface as StreamDNA
import Ontology.DNA.SemanticChecksumAlgebra as Checksum
import Ontology.DNA.ChannelCodingSurface as Channel

------------------------------------------------------------------------
-- STREAMING / RESIDENCY IS A COMPLEXITY COORDINATE, NOT SEMANTICS
--
-- Cross-pollination:
--
-- * FibreProgramComplexityExact already makes complexity consumer-indexed.
-- * AgdaElaborationResidencyComplexityExact keeps live residency/RSS separate
--   from abstract execution-path complexity.
-- * the DNA streaming surface exposes an incremental state/checksum interface.
-- * the critically sampled DNA transform preserves 256 four-state symbols and
--   has exact reconstruction without retaining a redundant leaf copy.
-- * DNA channel coding keeps physical substitution/indel/dropout risk distinct
--   from ideal representation/admissibility.
--
-- Therefore a change in residency strategy can be semantics-preserving, while
-- OOM/resource exhaustion, WrongType, non-factorability, representation error,
-- and physical-channel error remain separate fibres.
------------------------------------------------------------------------

data ResidencyStrategy : Set where
  eagerMaterialisation : ResidencyStrategy
  boundedStreaming : ResidencyStrategy

record ResidencyPlan : Set where
  constructor residency-plan
  field
    sourceDomainCount : Nat
    simultaneouslyResidentDomainArrays : Nat
    persistentAggregateArrays : Nat
    strategy : ResidencyStrategy
open ResidencyPlan public

-- Concrete carrier from the current painted-domain computation: the semantic
-- workset still consists of 46 source domains, but an eager strategy may retain
-- all 46 simultaneously whereas the streaming strategy needs one at a time.
paintedDomainEagerPlan : ResidencyPlan
paintedDomainEagerPlan = residency-plan 46 46 1 eagerMaterialisation

paintedDomainStreamingPlan : ResidencyPlan
paintedDomainStreamingPlan = residency-plan 46 1 1 boundedStreaming

paintedDomainDomainCountPreserved :
  sourceDomainCount paintedDomainEagerPlan
  ≡ sourceDomainCount paintedDomainStreamingPlan
paintedDomainDomainCountPreserved = refl

paintedDomainAggregateCountPreserved :
  persistentAggregateArrays paintedDomainEagerPlan
  ≡ persistentAggregateArrays paintedDomainStreamingPlan
paintedDomainAggregateCountPreserved = refl

eagerAndStreamingResidencyDiffer :
  simultaneouslyResidentDomainArrays paintedDomainEagerPlan
  ≡ simultaneouslyResidentDomainArrays paintedDomainStreamingPlan
  → ⊥
eagerAndStreamingResidencyDiffer ()

------------------------------------------------------------------------
-- SAME SEMANTIC FOLD, DIFFERENT RESIDENCY PLAN
------------------------------------------------------------------------

record SemanticsPreservingResidencyRefactor
    (Input Output : Set) : Set₁ where
  constructor semantics-preserving-residency-refactor
  field
    eager : Input → Output
    streamed : Input → Output
    sameOutcome : ∀ input → eager input ≡ streamed input
    eagerResidency : ResidencyPlan
    streamedResidency : ResidencyPlan
open SemanticsPreservingResidencyRefactor public

------------------------------------------------------------------------
-- ERROR FIBRES
------------------------------------------------------------------------

data ComplexityErrorFibre : Set where
  semanticMismatch : ComplexityErrorFibre
  representationMismatch : ComplexityErrorFibre
  consumerNonFactorability : ComplexityErrorFibre
  resourceEnvelopeExhaustion : ComplexityErrorFibre
  transportFailure : ComplexityErrorFibre
  physicalChannelSubstitution : ComplexityErrorFibre
  physicalChannelIndel : ComplexityErrorFibre
  physicalChannelDropout : ComplexityErrorFibre

-- Reuse the canonical WrongType/FactorsThrough meaning rather than defining a
-- second adequacy relation here.
ConsumerAdequate :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) →
  (State → Outcome) →
  Set₁
ConsumerAdequate = Wrong.ConsumerAdequate

------------------------------------------------------------------------
-- DNA WITNESSES REUSED WITHOUT SEMANTIC OVERREACH
------------------------------------------------------------------------

dnaStreamingSurface : StreamDNA.StreamingEncoderSurface
dnaStreamingSurface = StreamDNA.streamingEncoderSurface

dnaCriticalSamplingCountPreserved :
  Critical.coefficientCount ≡ 256
dnaCriticalSamplingCountPreserved = Critical.coefficientCount-is-256

dnaFourBlockRoundTrip :
  ∀ (xs : DNA.DNA4) →
  Critical.synthesise4 (Critical.analyse4 xs) ≡ xs
dnaFourBlockRoundTrip = Critical.synthesise4-analyse4

dnaChecksumComposition : Checksum.WholeChainChecksumLaw
dnaChecksumComposition = Checksum.singletonCWholeChainChecksumLaw

dnaIntegratedChannel : Channel.IntegratedChannelSurface
dnaIntegratedChannel = Channel.integratedChannelSurface

complexityIsConsumerIndexed : Bool
complexityIsConsumerIndexed =
  Complexity.FibreComplexityBoundary.complexityIsConsumerIndexed
    Complexity.canonicalFibreComplexityBoundary

elaborationResidencyNeedsOwnConsumer : Bool
elaborationResidencyNeedsOwnConsumer =
  Residency.PathElaborationBoundary.elaborationCostNeedsOwnConsumer
    Residency.canonicalPathElaborationBoundary

------------------------------------------------------------------------
-- NON-COLLAPSE REGRESSIONS
------------------------------------------------------------------------

data ResourceExhaustionImpliesSemanticMismatch : Set where
data ResourceExhaustionImpliesWrongType : Set where
data LowResidencyImpliesConsumerAdequacy : Set where
data ExactReconstructionImpliesChannelErrorFree : Set where
data ChecksumAgreementImpliesConsumerAdequacy : Set where
data ChannelRiskImpliesRepresentationMismatch : Set where
data StreamingInterfaceImpliesBoundedResidency : Set where

resourceExhaustionDoesNotNegateSemantics :
  ResourceExhaustionImpliesSemanticMismatch → ⊥
resourceExhaustionDoesNotNegateSemantics ()

resourceExhaustionDoesNotManufactureWrongType :
  ResourceExhaustionImpliesWrongType → ⊥
resourceExhaustionDoesNotManufactureWrongType ()

lowResidencyDoesNotManufactureAdequacy :
  LowResidencyImpliesConsumerAdequacy → ⊥
lowResidencyDoesNotManufactureAdequacy ()

exactReconstructionDoesNotManufactureChannelReliability :
  ExactReconstructionImpliesChannelErrorFree → ⊥
exactReconstructionDoesNotManufactureChannelReliability ()

checksumAgreementDoesNotManufactureAdequacy :
  ChecksumAgreementImpliesConsumerAdequacy → ⊥
checksumAgreementDoesNotManufactureAdequacy ()

channelRiskDoesNotBecomeRepresentationMismatch :
  ChannelRiskImpliesRepresentationMismatch → ⊥
channelRiskDoesNotBecomeRepresentationMismatch ()

-- Important: the concrete DNA streaming state still retains a prefix.  A
-- streaming interface therefore does not by itself prove residency bounded
-- independently of input length.
streamingInterfaceDoesNotProveBoundedResidency :
  StreamingInterfaceImpliesBoundedResidency → ⊥
streamingInterfaceDoesNotProveBoundedResidency ()

------------------------------------------------------------------------
-- CANONICAL BIDI BOUNDARY
------------------------------------------------------------------------

record ComplexityErrorDNABidiBoundary : Set where
  constructor complexity-error-dna-bidi-boundary
  field
    complexityConsumerIndexed : Bool
    residencyNeedsOwnConsumer : Bool
    sameSemanticOutcomeCanUseDifferentResidency : Bool
    criticalSamplingAutomaticallyLossy : Bool
    checksumEqualityCreatesConsumerAdequacy : Bool
    resourceExhaustionNegatesSemantics : Bool
    resourceExhaustionIsWrongType : Bool
    physicalChannelRiskIsRepresentationFailure : Bool
    exactReconstructionIsDistinctFromErrorCorrection : Bool
    streamingInterfaceAloneProvesBoundedResidency : Bool
open ComplexityErrorDNABidiBoundary public

canonicalComplexityErrorDNABidiBoundary : ComplexityErrorDNABidiBoundary
canonicalComplexityErrorDNABidiBoundary =
  complexity-error-dna-bidi-boundary
    complexityIsConsumerIndexed
    elaborationResidencyNeedsOwnConsumer
    true
    false
    false
    false
    false
    false
    true
    false
