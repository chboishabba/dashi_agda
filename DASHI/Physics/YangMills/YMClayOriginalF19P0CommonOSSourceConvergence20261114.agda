module DASHI.Physics.YangMills.YMClayOriginalF19P0CommonOSSourceConvergence20261114 where

------------------------------------------------------------------------
-- CLAY YANG--MILLS ORIGINAL WILSON/F19 + T4/P0 + STRESS/OS SOURCE ROOT.
--
-- Original mathematical attributions: Wilson lattice gauge action,
-- Faddeev--Popov ghost determinant, compact-group Haar integration,
-- Bałaban renormalization, Osterwalder--Schrader reconstruction;
-- original author's precise provenance and source/implementation
-- priority are preserved in each imported theorem module and
-- Docs/SourceAttributionPolicy.md.
--
-- Donor PR #1444 exact head (Wilson original source and CMP119 stress):
--   06e9a257df0d5fd9996ba7092b19713f74101f5c
-- Donor PR #1498 exact head (physical P0 source):
--   2c4204914d933aff95aa4a046a6237e42ac3eeeb
--
-- This root co-locates the genuine 1024-link fine Wilson source,
-- original 64-pair + 896 spectator marked effective partition,
-- reduced ghost/Haar diagrams, and same-source stress/common-core
-- conditional semigroup-closure algebra on the ORIGINAL #1444 tree.
--
-- CRITICAL: it neither constructs the source Wilson cubic/ghost
-- loop coefficients nor proves their Ward contraction. Finite
-- partition equality does not give physical 3-moment cutoff-uniform
-- RG errors or the same-density heat/Doob Hessian bound. The
-- physical stress charge Q=T00 and OS H have not been identified.
--
-- Legacy RealAnalysisAxioms contains postulates; DO NOT claim
-- --safe, postulate-free, universal G1, E1, D1/D2 or Clay endpoint.
--
-- Focused Agda local and golden Nix kernel/axiom admission pending.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YMClayOriginalWilsonPhysicalF19PartitionExact
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact
import DASHI.Physics.YangMills.YMClayP0BishopToOriginalWilsonRealWeldExact

import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact
import DASHI.Physics.YangMills.BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact
import DASHI.Physics.YangMills.BalabanP0LiteralDiagramTopologyFromSourceExact
import DASHI.Physics.YangMills.BalabanP0LiteralIndexedTensorWardSourceExact
import DASHI.Physics.YangMills.BalabanP0FourOriginalDiagramMixedTwoJetWeldExact
import DASHI.Physics.YangMills.BalabanP0PhysicalReducedGhostFiniteLogTailWeldExact
import DASHI.Physics.YangMills.BalabanP0HaarSmallAdjointChartRationalBudgetExact
import DASHI.Physics.YangMills.BalabanP0FreeGhostWilsonPositiveWeldExact
import DASHI.Physics.YangMills.BalabanP0TransverseTensorNotAutomaticallyScalarProjectorExact

import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact
import DASHI.Physics.YangMills.YangMillsStressOSSourceFirstSemigroupCoreToClosureExact
