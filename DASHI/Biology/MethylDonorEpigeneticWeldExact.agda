module DASHI.Biology.MethylDonorEpigeneticWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.OneCarbonHistamineMethylationNetworkExact as Network
import DASHI.Biology.EpigeneticBodyMemoryBridge as Epigenetic
import DASHI.Biology.EpigeneticTemporalRegulationBridge as Temporal

------------------------------------------------------------------------
-- METHYL-DONOR -> EPIGENETIC OBSERVATION WELD
--
-- The biochemical branch reaches a DNMT/SAM-dependent methylation process.
-- Existing epigenetic owners retain the observation/proxy and temporal
-- interpretation boundary.  The weld does not equate methyl-donor supply with
-- a particular genomic methylation state.
------------------------------------------------------------------------

record MethylDonorEpigeneticWeld : Set where
  constructor methylDonorEpigeneticWeld
  field
    biochemicalDNMTEdge : Network.BiochemicalEdge
    epigeneticMark : Epigenetic.EpigeneticMarkKind
    temporalMethylationRow : Temporal.MethylationRowKind
    sharedReading : String
    samSupplyDeterminesMark : Bool
    samSupplyDeterminesMarkIsFalse : samSupplyDeterminesMark ≡ false
    globalMethylationStateRecovered : Bool
    globalMethylationStateRecoveredIsFalse :
      globalMethylationStateRecovered ≡ false

open MethylDonorEpigeneticWeld public

canonicalMethylDonorEpigeneticWeld : MethylDonorEpigeneticWeld
canonicalMethylDonorEpigeneticWeld =
  methylDonorEpigeneticWeld
    Network.dnmtGenomicEdge
    Epigenetic.dnaMethylationCandidate
    Temporal.dnaMethylationProxyRowKind
    "DNMT-family methylation and DNA-methylation observations are connected as a candidate biochemical-to-epigenetic lane; locus, tissue, timing, chromatin context and competing regulation remain explicit."
    false refl
    false refl

data SAMEqualsDNAMethylationState : Set where
data DNMTEdgeEqualsGlobalEpigeneticState : Set where
data OneLocusMethylationEqualsPersonWideMethylation : Set where

samDoesNotEqualDNAMethylationState :
  SAMEqualsDNAMethylationState → ⊥
samDoesNotEqualDNAMethylationState ()

dnmtEdgeDoesNotEqualGlobalEpigeneticState :
  DNMTEdgeEqualsGlobalEpigeneticState → ⊥
dnmtEdgeDoesNotEqualGlobalEpigeneticState ()

oneLocusDoesNotDefinePersonWideMethylation :
  OneLocusMethylationEqualsPersonWideMethylation → ⊥
oneLocusDoesNotDefinePersonWideMethylation ()
