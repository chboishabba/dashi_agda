module DASHI.Physics.YangMills.BalabanP0OriginalSourceConvergence20261114 where

------------------------------------------------------------------------
-- YM P0 ORIGINAL-SOURCE INTEGRATION: FOCUSED ACCEPTANCE ROOT.
--
-- Original contributors: Wilson lattice action; Faddeev--Popov ghosts;
-- Haar compact-group integration; Bałaban multiscale RG;
-- original sources are separately attributed in the donor modules.
-- DASHI source donor #1498:
-- 2c4204914d933aff95aa4a046a6237e42ac3eeeb.
--
-- Nine original semantic/analytic modules are co-located by exact blob
-- SHA on the all-lane PR #1499; 7 original P0 owners + 2 source
-- dependencies not already present. All their direct DASHI imports
-- have source files on this integration branch.
--
-- This DOES NOT assert an inhabited original Wilson+FP+Haar mixed
-- scalar, a physical Ward cancellation, an all-box integral bound,
-- cutoff-uniform RG inequalities, interacting E1 continuum or D2 gap.
--
-- Agda 2.9 local source/kernel check and transitive postulate audit
-- remain required. Particularly, legacy RealAnalysisAxioms modules
-- cannot be claimed safe merely from an import-only root.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact
import DASHI.Physics.YangMills.BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact

import DASHI.Physics.YangMills.BalabanP0LiteralDiagramTopologyFromSourceExact
import DASHI.Physics.YangMills.BalabanP0LiteralIndexedTensorWardSourceExact
import DASHI.Physics.YangMills.BalabanP0FourOriginalDiagramMixedTwoJetWeldExact
import DASHI.Physics.YangMills.BalabanP0PhysicalReducedGhostFiniteLogTailWeldExact
import DASHI.Physics.YangMills.BalabanP0HaarSmallAdjointChartRationalBudgetExact
import DASHI.Physics.YangMills.BalabanP0FreeGhostWilsonPositiveWeldExact
import DASHI.Physics.YangMills.BalabanP0TransverseTensorNotAutomaticallyScalarProjectorExact
