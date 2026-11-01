module DASHI.Physics.YangMills.BalabanReducedGhostPrincipalLogDetSourceExact where

------------------------------------------------------------------------
-- ROUND83: FINITE REDUCED GHOST LOG-DET IS STANDARD MATRIX ANALYSIS
--
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- SOURCE THEOREM BOUNDARY
--
-- For a finite matrix R with spectral radius rho(R)<1, the principal matrix
-- logarithm of I+R exists and is represented by the absolutely convergent
-- power series
--
--   log(I+R) = sum_{n>=1} (-1)^(n+1) R^n / n.
--
-- On the same finite matrix,
--
--   Tr(log(I+R)) = log(det(I+R))
--
-- on the principal branch.  A subordinate norm bound ||R||<1 is sufficient
-- for rho(R)<1.
--
-- These are ordinary finite-dimensional matrix-function theorems.  They do not
-- depend on a Yang--Mills RG estimate once the literal reduced matrix and its
-- contraction have been constructed.
--
-- DASHI STATUS
--
-- The Round61 reduced-ghost lane already constructs the SAME anchored physical
-- matrix R_A and proves rowMass(R_A)<1/5.  It also constructs the signed finite
-- matrix-log tails and a canonical FastCauchy completion.  Therefore the
-- principal-log/determinant identity is source-owned rather than a new physical
-- YM lemma.
--
-- The still-new physical work is upstream/downstream identification:
--   * the Bishop background path really has the constructed finite jets with a
--     uniform fifth-order remainder;
--   * the resulting ghost coefficient is combined on the SAME Wilson/FP/Haar
--     polarization scalar and matched to the classified C_A normalization.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact
import DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact
import DASHI.Physics.YangMills.BalabanReducedGhostTraceFastCauchyCompletionExact

finitePrincipalMatrixLogSeriesLevel : ProofLevel
finitePrincipalMatrixLogSeriesLevel = standardImported

finiteTracePrincipalLogEqualsLogDetLevel : ProofLevel
finiteTracePrincipalLogEqualsLogDetLevel = standardImported

subordinateNormContractionImpliesPrincipalLogDomainLevel : ProofLevel
subordinateNormContractionImpliesPrincipalLogDomainLevel = standardImported

-- The literal anchored reduced ghost matrix and strict row contraction are
-- theorem-bearing in-repo, not imported assumptions.
literalReducedGhostMatrixContractionLevel : ProofLevel
literalReducedGhostMatrixContractionLevel = machineChecked

literalReducedGhostSignedTailAndFastCauchyLevel : ProofLevel
literalReducedGhostSignedTailAndFastCauchyLevel = machineChecked

-- Physical remainder: represent the actual Bishop-real background path by the
-- constructed rational jets with a uniform O(g^5) remainder.  This is the
-- source-native analytic seam; finite matrix-log functional calculus is not.
physicalReducedGhostBishopJetRemainderLevel : ProofLevel
physicalReducedGhostBishopJetRemainderLevel = conditional
