module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound58FrontierCutsetValidation where

------------------------------------------------------------------------
-- ROUND 58 FOCUSED VALIDATION ROOT
--
-- This root extends the Round57 physical-semantics tranche only with theorem-
-- bearing cutset reductions.  It intentionally does not promote unresolved
-- continuum/OS terminal claims.
--
-- Primary source metadata remains attached to the imported producer modules.
-- The Round58 files cite Bałaban CMP99/CMP102/CMP109/CMP119/CMP122, Rota,
-- Penrose, Daumas--Lester--Muñoz, Ahlfors, Wilson, Gross--Wilczek and
-- Politzer with title/author/DOI information where a DOI exists.
------------------------------------------------------------------------

-- Full Round57 finite/source-specific foundation.
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57PhysicalSemanticsValidation

-- G2: literal subset/KKT/Möbius authority -> exact cardinality-layer formulas
-- -> four source/four defect degree vectors -> sixteen Green blocks as one
-- common pseudoinverse bilinear family -> one region-wide grouped endpoint and
-- one charge floor.
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusDegreeLayerExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintMobiusDegreeLayerExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerDegreeEnvelopeExact

-- L4: no direct r=g^4 q input.  Expansion through cubic order plus explicit
-- cancellations constructs the fourth-order factorization and global beta
-- lower bound.
import DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCancellationToFourthOrderExact

-- G1 source-calculus reduction retained explicitly: Dlog=inverse-dexp is
-- already derived from local inverse + chain rule; only literal SU(2)
-- chart/product-trivialization realization remains.
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogFrechetFromLocalInverseExact
import DASHI.Physics.YangMills.BalabanCMP109LiteralPrincipalLogFrechetReductionExact

-- Compact-simple-group dependence is introduced at the perturbative producer,
-- not bolted onto the terminal reconstruction theorem.  Once the physical
-- Wilson/ghost/Haar colour algebra proves C_A factorization, the exact four-
-- orbit Bishop sum and any certified lower bound are reused group-independently.
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact
import DASHI.Physics.YangMills.BalabanCompactSimpleWilsonOneLoopOrbitAdapterExact

-- CMP119/CMP122: raw source objects do not carry all-scale Section-2
-- preservation as fields.  The raw state is constructed OVER the finite beta
-- history, so runningCoupling = History.couplingAt definitionally.  The
-- published active-scale Theorem-1 witness then constructs the same raw
-- E/R/B/background/complete-density predicates with no coupling equality
-- receipt.
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact
import DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact

-- Source audit boundary: CMP122 II is imported as the published completion of
-- four-dimensional ultraviolet stability.  That does NOT promote continuum
-- Schwinger construction, OS axioms, non-Gaussian survival, or cutoff-uniform
-- physical exponential clustering; those remain explicit conditional leaves.
import DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact
