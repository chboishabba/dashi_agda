module DASHI.Physics.YangMills.BalabanCMP109CompactSimpleColourReductionSourceExact where

------------------------------------------------------------------------
-- ROUND84: CMP109 WARD REDUCTION + SIMPLE LIE THEORY -> ONE COLOUR SCALAR
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Anthony W. Knapp,
-- "Lie Groups Beyond an Introduction", second edition, Birkhauser, 2002.
-- DOI: 10.1007/978-1-4757-2453-0.
--
-- N. Bourbaki,
-- "Lie Groups and Lie Algebras, Chapters 4--6", Springer, 2002.
-- No DOI assigned for the cited edition.
--
-- SOURCE BOUNDARY
--
-- CMP109 Sect. 4 derives Ward--Takahashi constraints on the two-field tensor.
-- Around (4.33), after identifying the tensor with a bilinear form on the Lie
-- algebra, Bałaban states that under the group assumptions the Ward identity
-- holds iff the colour matrix is proportional to the identity:
--
--       E_ab = E delta_ab,
--
-- equivalently <E,A tensor B> = E tr(AB).
--
-- Thus the polarization colour structure is already reduced to ONE scalar by
-- the source Ward analysis.  For a compact simple Lie algebra, the invariant
-- symmetric bilinear form is unique up to scale; in the long-root-squared-two
-- normalization the adjoint contraction is the dual-Coxeter/adjoint-Casimir
-- scalar C_A.
--
-- CONSEQUENCE FOR THE CLAY FRONTIER
--
-- One does not need separate A/B/C/D/E/F/G diagram enumerations.  The genuinely
-- new L1 calculation is the universal scalar produced by the SAME constrained
-- Wilson + reduced-FP + Haar finite-cutoff object, together with its uniform
-- same-step remainder and exact normalization to the classified C_A carrier.
--
-- This module is deliberately a trust-boundary module: it records source and
-- standard theorems, rather than pretending a generic record with an invariant
-- form proves the physical Ward identity by itself.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact

-- CMP109 Sect. 4 Ward theorem: the physical colour two-tensor descends to a
-- scalar invariant bilinear form on each simple colour factor.
cmp109WardColourTensorIsScalarLevel : ProofLevel
cmp109WardColourTensorIsScalarLevel = standardImported

-- Standard simple-Lie theorem: invariant symmetric bilinear forms are
-- one-dimensional; the adjoint two-bracket contraction is C_A times the chosen
-- invariant metric.
compactSimpleInvariantBilinearUniquenessLevel : ProofLevel
compactSimpleInvariantBilinearUniquenessLevel = standardImported

compactSimpleAdjointContractionIsCasimirLevel : ProofLevel
compactSimpleAdjointContractionIsCasimirLevel = standardImported

-- The classification-to-positive-C_A carrier is theorem-bearing in-repo.
classifiedAdjointCasimirCarrierLevel : ProofLevel
classifiedAdjointCasimirCarrierLevel = machineChecked

-- Still physical/new: prove that the literal finite-cutoff Wilson/FP/Haar scalar
-- uses the same invariant-metric normalization and evaluates to the universal
-- 11/24 coefficient plus a uniformly small same-step remainder.  Source Ward
-- reduction does not supply that number; CMP109 explicitly defers the full
-- perturbative beta-trajectory calculation.
literalOneLoopScalarNormalizationAndRemainderLevel : ProofLevel
literalOneLoopScalarNormalizationAndRemainderLevel = conditional
