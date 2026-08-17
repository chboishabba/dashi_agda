module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the characteristic-11 Brandt algebra, representation
-- falsifiers, and the first surviving positive fine geometry.
--
-- Arithmetic side:
-- * source-certified supersingular carrier {j=0,j=1728=1 mod11};
-- * independent Phi_2/Phi_3/Phi_5 neighbour systems;
-- * automorphism-derived Brandt weights, weighted self-adjointness;
-- * commuting B_11(2), B_11(3), B_11(5) and prime-square relations;
-- * cyclic/full Phi_4 correction and positive T2^2 path-count realization.
--
-- Falsifier side:
-- * the six matched-dihedral sectors admit cheap section-generated lifts;
-- * even a full unital Hecke algebra can be engineered through kernel freedom;
-- * the natural one-vs-five positive lift is impossible;
-- * more strongly, NO unweighted symmetric binary equitable quotient of either
--   six sector vertices or eleven raw weight vertices can produce B_11(2),
--   because 3|F0|=2|F1| forces total fibre size divisible by five.
--
-- Positive producer side:
-- * generic arbitrary-arity positive neighbour systems;
-- * labelled positive quotient descent plus equitable graph quotient descent;
-- * generic inverse-closed Schreier producer;
-- * minimal five-state 2+3 fine carrier suggested by Brandt balance;
-- * positive ell=2,3,5 neighbour systems quotienting to the verified Brandt
--   operators;
-- * inverse-closed permutation-generator realizations of all three primes;
-- * pairwise commuting prime adjacency operators;
-- * literal positive R4,R9,R25 neighbour systems of arities 7,13,31;
-- * prime-square path-count laws with the TRUE five-state identity.
--
-- The five-state carrier remains a candidate finite geometry.  It is NOT yet
-- identified with quaternion ideal classes, Gamma\G/U, Bruhat--Tits geometry,
-- PR #558's ternary pants action, or the SO(3) matched-dihedral carrier.
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
import DASHI.Moonshine.P11SixSectorSymmetricSchreierNoGoExact
import DASHI.Moonshine.P11ElevenStateSymmetricSchreierNoGoExact

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact
import DASHI.Moonshine.PositiveNeighbourQuotientDescentExact
import DASHI.Moonshine.EquitablePositiveQuotientExact
import DASHI.Moonshine.PositiveSchreierNeighbourSystemExact
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact
import DASHI.Moonshine.P11PositiveHeckeSquarePathCountsExact
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact
import DASHI.Moonshine.P11FiveStateEquitableBrandtQuotientExact
import DASHI.Moonshine.P11FiveStatePositiveHeckeAlgebraExact
import DASHI.Moonshine.P11FiveStatePositivePrimeSquareNeighboursExact
import DASHI.Moonshine.P11FiveStatePermutationHeckeProducerExact
import DASHI.Moonshine.P11PositiveGeometryHighestAlphaRegression
