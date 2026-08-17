module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the characteristic-11 arithmetic Brandt algebra plus the
-- representation-side lift/falsifier tranche.
--
-- Arithmetic side:
-- * independent Phi_2, Phi_3 and Phi_5 modular-polynomial reductions;
-- * corrected spectral vocabulary: Laplacian eigenvalue 5 vs adjacency gap 1;
-- * source-certified geometric supersingular carrier {j=0,j=1728=1 mod11};
-- * automorphism-derived reciprocal Brandt weights 2 and 3;
-- * arbitrary-vector weighted self-adjointness for B_11(2);
-- * B_11(2), B_11(3), B_11(5), their coprime products and prime squares.
--
-- Representation-side falsifier:
-- * p=11 gives j=5 and six actual matched-dihedral sectors;
-- * an explicit split 6->2 test lens mechanically lifts every Brandt operator;
-- * the lift is lossy and has explicit kernel freedom;
-- * even a full unital joint Hecke algebra can be engineered by putting a
--   compatible scalar Hecke character on the kernel;
-- * that completion has a literal negative coefficient on an actual rho_2
--   basis state;
-- * stronger: the natural singlet-vs-five-doublet quotient admits NO
--   nonnegative unital B_11(2) lift satisfying R2^2=R4+2I, by a constructive
--   five-vs-three pigeonhole/diagonal argument.
--
-- Therefore the next producer is not "some intertwiner" or even "some joint
-- Hecke algebra": it must be a different source-native positive representation
-- correspondence/quotient invariant genuinely realizing the Brandt system.
------------------------------------------------------------------------

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact
import DASHI.Moonshine.P11BrandtAutomorphismWeightExact
import DASHI.Moonshine.P11BrandtWeightedSelfAdjointExact
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact
import DASHI.Moonshine.P11Phi3Phi5IndependentBrandtExact
import DASHI.Moonshine.P11AristotleHeckeSquareCrossPollinationExact
import DASHI.Moonshine.P11Phi4CyclicVsFullHeckeExact
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact
import DASHI.Moonshine.P11BrandtPrimePowerHeckeExact
import DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact
import DASHI.Moonshine.P11MatchedDihedralSixSectorBasisExact
import DASHI.Moonshine.P11MatchedDihedralLiftKernelFreedomExact
import DASHI.Moonshine.P11MatchedDihedralUnitalHeckeCompletionExact
import DASHI.Moonshine.P11MatchedDihedralPositiveHeckeNoGoExact
