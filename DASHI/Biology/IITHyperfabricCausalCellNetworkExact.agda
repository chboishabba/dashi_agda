module DASHI.Biology.IITHyperfabricCausalCellNetworkExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITCausalPantsFibreGluingExact as Causal
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact as PantsSeam
import DASHI.Reasoning.IITHyperfabricPartitionBridgeExact as Partition

------------------------------------------------------------------------
-- PATH-INDEXED CAUSAL CELL NETWORK
--
-- A hyperfabric experiment has three separate levels:
--   1. local causal synthesis cell (A,B) -> C,
--   2. output-to-input gluing edges indexed by path/step,
--   3. optional stalk/global-section compatibility carried by TypedHyperfabric.
--
-- IIT's numerical scanner currently evaluates level (2) as a causal-connection
-- partition.  Existing stalk-restriction and global-section partition semantics
-- remain separate theorem surfaces; they are not silently identified with an
-- IIT directional system partition.
------------------------------------------------------------------------

record IndexedCausalFabric (Path : Set) : Set₁ where
  constructor indexedCausalFabric
  field
    fibres : Causal.FibreFamily Path
    localCell : (step : Path) → Causal.LocalSynthesisCell fibres step
    Edge : Set
    source : Edge → Path
    target : Edge → Path
    gluing : (edge : Edge) →
      Causal.OutputInputGluing fibres (source edge) (target edge)
    fabricReceipt : String

open IndexedCausalFabric public

record ClosedPathWitness
    {Path : Set}
    (fabric : IndexedCausalFabric Path) : Set₁ where
  constructor closedPathWitness
  field
    start : Path
    edgePath : List (Edge fabric)
    closureReceipt : String

open ClosedPathWitness public

------------------------------------------------------------------------
-- Existing typed pants seam: compatibility is proof-relevant and does not
-- automatically rewrite incidence.
------------------------------------------------------------------------

typedPantsSeamBoundary : PantsSeam.TypedHyperfabricPantsGluingBoundary
typedPantsSeamBoundary = PantsSeam.canonicalTypedHyperfabricPantsGluingBoundary

pantsSeamDoesNotRewriteIncidence :
  PantsSeam.interfaceMatchAutomaticallyRewritesIncidence
    typedPantsSeamBoundary ≡ false
pantsSeamDoesNotRewriteIncidence =
  PantsSeam.interfaceMatchAutomaticallyRewritesIncidenceIsFalse
    typedPantsSeamBoundary

canonicalExistingSeam : PantsSeam.HyperfabricPantsGluing PantsSeam.seamSection
canonicalExistingSeam = PantsSeam.canonicalPantsGluing

------------------------------------------------------------------------
-- Partition-semantics separation already established by the IIT bridge.
------------------------------------------------------------------------

data ExperimentPartitionSemantics : Set where
  causalGraphConnectionPartition : ExperimentPartitionSemantics
  stalkRestrictionPartition : ExperimentPartitionSemantics
  globalSectionPartition : ExperimentPartitionSemantics

causalGraphNotStalkPartition :
  causalGraphConnectionPartition ≡ stalkRestrictionPartition → ⊥
causalGraphNotStalkPartition ()

stalkNotGlobalSectionPartition :
  stalkRestrictionPartition ≡ globalSectionPartition → ⊥
stalkNotGlobalSectionPartition ()

existingPartitionBoundary : Partition.HyperfabricPartitionBoundary
existingPartitionBoundary = Partition.canonicalHyperfabricPartitionBoundary

------------------------------------------------------------------------
-- Executable finite fixture receipt.
------------------------------------------------------------------------

record HyperfabricFixtureReceipt : Set where
  constructor hyperfabricFixtureReceipt
  field
    openXorPath2023 : String
    closedXorCycle2023 : String
    xorGrid2x2_2023 : String
    closedTriXorCycle2023 : String
    deterministic2026Receipt : String
    scanner : String

open HyperfabricFixtureReceipt public

currentHyperfabricFixtureReceipt : HyperfabricFixtureReceipt
currentHyperfabricFixtureReceipt =
  hyperfabricFixtureReceipt
    "open XOR path: phi_s=0"
    "closed recurrent XOR three-cell fabric: phi_s=2 on all eight states"
    "2x2 XOR fabric: phi_s in {0,0.5}; twelve of sixteen states zero"
    "closed recurrent triXor three-cell fabric: phi_s=log2(9) on all twenty-seven states"
    "all deterministic fixtures have phi_s=0 under IIT_4_0_2026"
    "scripts/iit_hyperfabric_fixture_scan.py"

record IITHyperfabricCausalBoundary : Set where
  constructor iitHyperfabricCausalBoundary
  field
    localGateSeparatedFromGluing : Bool
    pathIndexedGluingExplicit : Bool
    typedSeamRequiresInterfaceMatch : Bool
    typedSeamAutomaticallyRewritesIncidence : Bool
    causalGraphStalkAndSectionPartitionsCollapsed : Bool
    numericScannerCurrentlyEvaluatesCausalGraphCuts : Bool
    globalSectionRequiresCompatibilityWitness : Bool
    numericReceiptEqualsKernelProof : Bool

open IITHyperfabricCausalBoundary public

canonicalIITHyperfabricCausalBoundary : IITHyperfabricCausalBoundary
canonicalIITHyperfabricCausalBoundary =
  iitHyperfabricCausalBoundary true true true false false true true false

partitionSemanticsRemainSeparate :
  causalGraphStalkAndSectionPartitionsCollapsed
    canonicalIITHyperfabricCausalBoundary ≡ false
partitionSemanticsRemainSeparate = refl

numericReceiptDoesNotSelfPromote :
  numericReceiptEqualsKernelProof canonicalIITHyperfabricCausalBoundary ≡ false
numericReceiptDoesNotSelfPromote = refl
