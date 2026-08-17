module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound58FrontierCutsetValidation where

------------------------------------------------------------------------
-- ROUND 58 FOCUSED VALIDATION ROOT
--
-- This root extends the Round57 physical-semantics tranche only with theorem-
-- bearing cutset reductions.  It intentionally does not import continuum/OS
-- terminal claims and does not promote unresolved physical estimates.
--
-- Primary source metadata remains attached to the imported producer modules.
-- The new Round58 files cite Bałaban CMP99/CMP102/CMP109/CMP119/CMP122, Rota,
-- Penrose, Daumas--Lester--Muñoz and Ahlfors with title/author/DOI information
-- where a DOI exists.
------------------------------------------------------------------------

-- Full Round57 finite/source-specific foundation.
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57PhysicalSemanticsValidation

-- G2: same literal subset/KKT/Möbius authority -> same 4+16 degree blocks;
-- one region-wide grouped endpoint and one charge floor close the selector.
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

-- Source-native CMP119 state and active-scale CMP122 bridge retained as the RG
-- side of the finite cutset.  Round58 does not replace them with a second
-- generic invariant record.
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact
