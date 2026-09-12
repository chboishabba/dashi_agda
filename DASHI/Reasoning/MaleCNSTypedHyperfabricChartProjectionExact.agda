module DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (length)

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TypedHyperfabricConsumerReductionBridgeExact as SectionReduction

------------------------------------------------------------------------
-- MaleCNS region-level chart incidence.
--
-- This owner instantiates the 26-region vocabulary and a source/target
-- ordered-pair chart carrier. It does NOT identify the complete 26^2 pair
-- carrier with the raw physical synapse hypergraph. The purpose is to make the
-- already-used pairwise NDim chart a projection of compatible
-- TypedHyperfabric GlobalSections.
------------------------------------------------------------------------

data MaleCNSRegion : Set where
  AL AOTU AVLP BU CRE GNG IB ICL IPS LAL LO PED PLP PRW PVLP SAD SCL SIP SLP SMP SPS VES WED alphaL betaL gammaL : MaleCNSRegion

allMaleCNSRegions : List MaleCNSRegion
allMaleCNSRegions =
  AL ∷ AOTU ∷ AVLP ∷ BU ∷ CRE ∷ GNG ∷ IB ∷ ICL ∷ IPS ∷ LAL ∷ LO ∷ PED ∷
  PLP ∷ PRW ∷ PVLP ∷ SAD ∷ SCL ∷ SIP ∷ SLP ∷ SMP ∷ SPS ∷ VES ∷ WED ∷
  alphaL ∷ betaL ∷ gammaL ∷ []

maleCNSRegionCountIs26 : length allMaleCNSRegions ≡ 26
maleCNSRegionCountIs26 = refl

record MaleCNSPair : Set where
  constructor pair
  field
    sourceRegion : MaleCNSRegion
    targetRegion : MaleCNSRegion

open MaleCNSPair public

data MaleCNSPairIncidence : MaleCNSRegion → MaleCNSPair → Set where
  sourceIncidence : ∀ {source target} →
    MaleCNSPairIncidence source (pair source target)
  targetIncidence : ∀ {source target} →
    MaleCNSPairIncidence target (pair source target)

------------------------------------------------------------------------
-- Historical eight-coordinate chart carried on each ordered region pair.
------------------------------------------------------------------------

record LegacyNDimChart8 (Value : Set) : Set where
  constructor chart8
  field
    directForward : Value
    directReverse : Value
    twoHopForward : Value
    twoHopReverse : Value
    commonInput : Value
    commonOutput : Value
    signedForward : Value
    signedReverse : Value

open LegacyNDimChart8 public

record RegionPairChartStalk (Value : Set) : Set where
  constructor region-pair-chart-stalk
  field
    outgoingChart : MaleCNSRegion → LegacyNDimChart8 Value
    incomingChart : MaleCNSRegion → LegacyNDimChart8 Value

open RegionPairChartStalk public

restrictMaleCNSPair :
  ∀ {Value vertex edge} →
  MaleCNSPairIncidence vertex edge →
  RegionPairChartStalk Value →
  LegacyNDimChart8 Value
restrictMaleCNSPair {edge = pair source target} sourceIncidence stalk =
  outgoingChart stalk target
restrictMaleCNSPair {edge = pair source target} targetIncidence stalk =
  incomingChart stalk source

maleCNSRegionPairChartFabric :
  ∀ {Value : Set} →
  Hyperfabric.TypedHyperfabric MaleCNSRegion MaleCNSPair
maleCNSRegionPairChartFabric {Value} = record
  { vertexStalk = λ _ → RegionPairChartStalk Value
  ; edgeStalk = λ _ → LegacyNDimChart8 Value
  ; incidence = MaleCNSPairIncidence
  ; restrict = restrictMaleCNSPair
  ; edgeProvenance = λ _ → "MaleCNS 26-region ordered-pair chart carrier" ∷ []
  ; edgeSalience = λ _ → 1
  ; fabricLabel = "MaleCNS region-pair NDim chart as TypedHyperfabric"
  }

------------------------------------------------------------------------
-- Global-section -> old pair chart projection.
------------------------------------------------------------------------

sectionPairChart :
  ∀ {Value : Set} →
  Hyperfabric.GlobalSection (maleCNSRegionPairChartFabric {Value}) →
  MaleCNSPair →
  LegacyNDimChart8 Value
sectionPairChart section edge = Hyperfabric.edgeValue section edge

sectionOutgoingAgreesWithPairChart :
  ∀ {Value : Set}
    (section : Hyperfabric.GlobalSection (maleCNSRegionPairChartFabric {Value}))
    (source target : MaleCNSRegion) →
  outgoingChart (Hyperfabric.vertexValue section source) target
  ≡ sectionPairChart section (pair source target)
sectionOutgoingAgreesWithPairChart section source target =
  Hyperfabric.compatible section sourceIncidence

sectionIncomingAgreesWithPairChart :
  ∀ {Value : Set}
    (section : Hyperfabric.GlobalSection (maleCNSRegionPairChartFabric {Value}))
    (source target : MaleCNSRegion) →
  incomingChart (Hyperfabric.vertexValue section target) source
  ≡ sectionPairChart section (pair source target)
sectionIncomingAgreesWithPairChart section source target =
  Hyperfabric.compatible section targetIncidence

sourceAndTargetChartsAgreeThroughGlobalSection :
  ∀ {Value : Set}
    (section : Hyperfabric.GlobalSection (maleCNSRegionPairChartFabric {Value}))
    (source target : MaleCNSRegion) →
  outgoingChart (Hyperfabric.vertexValue section source) target
  ≡ incomingChart (Hyperfabric.vertexValue section target) source
sourceAndTargetChartsAgreeThroughGlobalSection section source target =
  trans
    (sectionOutgoingAgreesWithPairChart section source target)
    (sym (sectionIncomingAgreesWithPairChart section source target))

------------------------------------------------------------------------
-- Set-sized selected-section code.
------------------------------------------------------------------------

MaleCNSPairChartCode : Set → Set
MaleCNSPairChartCode Value = MaleCNSPair → LegacyNDimChart8 Value

regionStalkFromPairChart :
  ∀ {Value : Set} →
  MaleCNSPairChartCode Value →
  MaleCNSRegion →
  RegionPairChartStalk Value
regionStalkFromPairChart code region =
  region-pair-chart-stalk
    (λ target → code (pair region target))
    (λ source → code (pair source region))

realizeMaleCNSPairChartCode :
  ∀ {Value : Set} →
  MaleCNSPairChartCode Value →
  Hyperfabric.GlobalSection (maleCNSRegionPairChartFabric {Value})
realizeMaleCNSPairChartCode code = record
  { vertexValue = regionStalkFromPairChart code
  ; edgeValue = code
  ; compatible = λ
      { sourceIncidence → refl
      ; targetIncidence → refl
      }
  ; sectionReceipt = "ordered-pair chart code realized as one compatible MaleCNS chart GlobalSection"
  }

maleCNSSelectedSectionCarrier :
  ∀ {Value : Set} →
  SectionReduction.SelectedSectionCarrier
    (maleCNSRegionPairChartFabric {Value})
maleCNSSelectedSectionCarrier {Value} =
  SectionReduction.selected-section-carrier
    (MaleCNSPairChartCode Value)
    realizeMaleCNSPairChartCode
    "Set-sized MaleCNS complete ordered-pair eight-coordinate chart code"

sectionPairChartRealizationExact :
  ∀ {Value : Set}
    (code : MaleCNSPairChartCode Value)
    (edge : MaleCNSPair) →
  sectionPairChart (realizeMaleCNSPairChartCode code) edge ≡ code edge
sectionPairChartRealizationExact code edge = refl

------------------------------------------------------------------------
-- Executed Python representation receipts.
--
-- These are empirical/runtime coordinates, not kernel proofs. They record that
-- the already-used eight-coordinate chart can be lifted to/projected from the
-- local-hyperfabric runtime without numerical change for the declared consumer.
------------------------------------------------------------------------

record MaleCNSHyperfabricProjectionReceipt : Set where
  constructor malecns-hyperfabric-projection-receipt
  field
    repository : String
    artifactPath : String
    regionCount : Nat
    orderedPairLocalityCount : Nat
    composableBaseIncidenceCount : Nat
    legacyEightCoordinateRoundtripExact : Bool
    originalJoinedLORO : String
    projectedJoinedLORO : String
    absoluteLORODifference : String
    interpretation : String

open MaleCNSHyperfabricProjectionReceipt public

currentMaleCNSHyperfabricProjectionReceipt : MaleCNSHyperfabricProjectionReceipt
currentMaleCNSHyperfabricProjectionReceipt = malecns-hyperfabric-projection-receipt
  "github.com/chboishabba/dashiBRAIN"
  "data/gauthey_lbm/jrc2018_regions_a2_r5/malecns_local_fibre_hyperfabric.json"
  26
  676
  16250
  true
  "0.13639532298659035"
  "0.13639532298659035"
  "0.0"
  "The 26-region local-hyperfabric lift/project route is numerically lossless for the historical eight-coordinate chart and joined-controlled LORO consumer. Base incidence materialization does not itself manufacture fibre transport or gluing."

record SenderGainHyperfabricProjectionReceipt : Set where
  constructor sender-gain-hyperfabric-projection-receipt
  field
    candidate : String
    derivedFromHyperfabricProjection : Bool
    matchesStandaloneCompositionExactly : Bool
    maxAbsDifference : String
    joinedLORO : String
    certifiedConsumerSufficient : Bool
    interpretation : String

open SenderGainHyperfabricProjectionReceipt public

currentSenderGainHyperfabricProjectionReceipt : SenderGainHyperfabricProjectionReceipt
currentSenderGainHyperfabricProjectionReceipt = sender-gain-hyperfabric-projection-receipt
  "m_i * P_ij"
  true
  true
  "0.0"
  "0.13189851095808636"
  false
  "The mP candidate is exactly derivable through the hyperfabric chart projection path. Exact derivability does not promote the candidate to a certified sufficient or minimal carrier."

record MaleCNSPhysicalIncidenceProjectionReceipt : Set where
  constructor malecns-physical-incidence-projection-receipt
  field
    regionCount : Nat
    orderedPairCount : Nat
    nonzeroDirectCouplingPairCount : Nat
    aggregatedDirectSupportCompleteAt26RegionQuotient : Bool
    regeneratedEightCoordinatesExactly : Bool
    regeneratedJoinedLORO : String
    joinedLORODifference : String
    aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraph : Bool
    interpretation : String

open MaleCNSPhysicalIncidenceProjectionReceipt public

currentMaleCNSPhysicalIncidenceProjectionReceipt : MaleCNSPhysicalIncidenceProjectionReceipt
currentMaleCNSPhysicalIncidenceProjectionReceipt = malecns-physical-incidence-projection-receipt
  26
  676
  676
  true
  true
  "0.13639532298659035"
  "0.0"
  false
  "At the declared 26-region aggregation every ordered pair has nonzero direct coupling, and this aggregated support regenerates all eight NDim coordinates exactly. Completeness of the coarse region support does not identify it with the raw neuron/synapse physical hypergraph."

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record MaleCNSHyperfabricChartProjectionBoundary : Set where
  constructor malecns-hyperfabric-chart-projection-boundary
  field
    exactRegionVocabularyCountPaid : Bool
    exactRegionVocabularyCountPaidIsTrue :
      exactRegionVocabularyCountPaid ≡ true

    sourceTargetPairIncidenceRepresented : Bool
    sourceTargetPairIncidenceRepresentedIsTrue :
      sourceTargetPairIncidenceRepresented ≡ true

    chartProjectionComesFromGlobalSectionEdgeValues : Bool
    chartProjectionComesFromGlobalSectionEdgeValuesIsTrue :
      chartProjectionComesFromGlobalSectionEdgeValues ≡ true

    globalSectionForcesSourceTargetChartAgreement : Bool
    globalSectionForcesSourceTargetChartAgreementIsTrue :
      globalSectionForcesSourceTargetChartAgreement ≡ true

    selectedSectionCarrierIsChartCodeNotPhysicalIncidence : Bool
    selectedSectionCarrierIsChartCodeNotPhysicalIncidenceIsTrue :
      selectedSectionCarrierIsChartCodeNotPhysicalIncidence ≡ true

    completePairCarrierEqualsPhysicalNonzeroSynapseHypergraph : Bool
    completePairCarrierEqualsPhysicalNonzeroSynapseHypergraphIsFalse :
      completePairCarrierEqualsPhysicalNonzeroSynapseHypergraph ≡ false

    aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraph : Bool
    aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraphIsFalse :
      aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraph ≡ false

    eightCoordinatesEqualUnderlyingFibreCardinality : Bool
    eightCoordinatesEqualUnderlyingFibreCardinalityIsFalse :
      eightCoordinatesEqualUnderlyingFibreCardinality ≡ false

    empiricalHyperfabricRoundtripLosslessForDeclaredConsumer : Bool
    empiricalHyperfabricRoundtripLosslessForDeclaredConsumerIsTrue :
      empiricalHyperfabricRoundtripLosslessForDeclaredConsumer ≡ true

    empiricalSenderGainProjectionExact : Bool
    empiricalSenderGainProjectionExactIsTrue :
      empiricalSenderGainProjectionExact ≡ true

    exactProjectionPromotesSufficiency : Bool
    exactProjectionPromotesSufficiencyIsFalse :
      exactProjectionPromotesSufficiency ≡ false

open MaleCNSHyperfabricChartProjectionBoundary public

canonicalMaleCNSHyperfabricChartProjectionBoundary :
  MaleCNSHyperfabricChartProjectionBoundary
canonicalMaleCNSHyperfabricChartProjectionBoundary =
  malecns-hyperfabric-chart-projection-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
