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
