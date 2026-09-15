module DASHI.Biology.Protein.TRPA1ThermalAdaptationValidation where

-- Focused import root for the Feng et al. TRPA1 thermal-adaptation tranche.
-- This deliberately avoids widening DASHI.Biology.Everything merely to obtain
-- a certification target: the production owner, its regression contract, and
-- the pre-existing protein-function / Allium protein-thiol parents are checked
-- together here.

import DASHI.Biology.Protein.ProteinFunctionProjection
import DASHI.Biology.Protein.AlliumThiolProteinInteractionExact
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationRegression

-- Repository-native source attribution continuation: DOI/PMID/PMCID/canonical
-- Science link are stable provenance coordinates around the already-formalised
-- Feng biology.  Exact article QID remains explicitly unresolved.
import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact
import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeValidation

-- Source-bounded acquisition continuation: cross-pollinates only the reusable
-- information architecture from the AdK calibration tranche.  Feng et al.'s
-- residue/gating biology and Li-Liu-Ji's numeric dynamics remain source-local;
-- neither source gains authorship or authority over the other's propositions.
import DASHI.Biology.Protein.TRPA1AdKSourceBoundedAcquisitionCrossPollinationExact
import DASHI.Biology.Protein.TRPA1AdKSourceBoundedAcquisitionCrossPollinationValidation
