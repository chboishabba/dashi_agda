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
-- carrier with the nonzero physical synapse hypergraph: zero/possible pairs are
-- still present. The purpose is to make the already-used pairwise NDim chart a
-- projection of compatible TypedHyperfabric GlobalSections.
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
--
-- A complete ordered-pair chart function is itself Set-sized.  Realization
-- constructs one compatible GlobalSection by using that same pair chart for
-- both the source-facing and target-facing vertex stalk views.  This pays the
-- universe-correct bridge into ConsumerRelativeReduction without identifying
-- the dense chart carrier with the physical nonzero synapse incidence graph.
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

    eightCoordinatesEqualUnderlyingFibreCardinality : Bool
    eightCoordinatesEqualUnderlyingFibreCardinalityIsFalse :
      eightCoordinatesEqualUnderlyingFibreCardinality ≡ false

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
