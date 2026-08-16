module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the source-faithful characteristic-11 classical
-- correspondence / Brandt / Aristotle-Hecke cross-pollination.
--
-- The stack now contains:
--
-- * the actual ell=2 modular-polynomial correspondence;
-- * corrected spectral vocabulary: Laplacian eigenvalue 5 vs adjacency gap 1;
-- * a source-certified geometric supersingular carrier {j=0,j=1728=1 mod11};
-- * reduced automorphism orders 3 and 2 and derived reciprocal Brandt weights
--   2 and 3;
-- * prime Brandt generators B_11(2), B_11(3), B_11(5) with Ramanujan-square
--   certificates;
-- * their exact commuting coprime products;
-- * prime-square Brandt operators at 4,9,25 satisfying the weight-two Hecke
--   recurrence, including the independently checked Phi_4(cyclic)+I correction
--   for full T_4.
--
-- Equality of the B_11(5) two-state matrix with the cyclic Phi_4 matrix is kept
-- explicitly weaker than equality of the underlying geometric correspondences.
-- The representation-side joint-Hecke intertwiner remains the next frontier.
------------------------------------------------------------------------

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact
import DASHI.Moonshine.P11AristotleHeckeSquareCrossPollinationExact
import DASHI.Moonshine.P11Phi4CyclicVsFullHeckeExact
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact
