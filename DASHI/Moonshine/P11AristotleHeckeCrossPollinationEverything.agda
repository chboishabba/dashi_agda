module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the characteristic-11 Brandt algebra, representation
-- falsifiers, surviving positive fine geometry, and cross-prime stack controls.
--
-- Arithmetic side:
-- * source-certified supersingular carrier {j=0,j=1728=1 mod11};
-- * independent Phi_2/Phi_3/Phi_5 neighbour systems;
-- * automorphism-derived Brandt weights, weighted self-adjointness;
-- * commuting B_11(2), B_11(3), B_11(5) and prime-square relations;
-- * cyclic/full Phi_4 correction and positive T2^2 path-count realization.
--
-- Representation falsifiers:
-- * six matched-dihedral sectors admit cheap section-generated lifts;
-- * even a full unital Hecke algebra can be engineered through kernel freedom;
-- * the natural one-vs-five positive lift is impossible;
-- * no ordinary unweighted symmetric binary quotient on six sectors or eleven
--   raw weights can produce B_11(2), because the 2:3 edge-balance ratio forces
--   total fibre cardinality divisible by five.
--
-- Positive p=11 producer:
-- * generic positive neighbour / equitable quotient / Schreier APIs;
-- * five-state 2+3 fine carrier;
-- * positive ell=2,3,5 systems and inverse-closed permutation realizations;
-- * commuting prime operators;
-- * literal positive R4,R9,R25 systems and true-identity prime-square laws.
--
-- Stack-unweighting advance:
-- * monodromy/stabilizer weights are separated from reciprocal sheet counts;
-- * p=11 geometric weights (3,2) canonically clear to sheets (2,3), so the
--   five-state CARDINALITY pattern is now derived from Eichler--Deuring stack
--   data rather than discovered graph fitting;
-- * same prescription gives p=37 sheets (1,1,1), total 3;
-- * same prescription gives p=43 sheets (1,2,2,2), total 7, despite its
--   monodromy-weight sum also being 5;
-- * source p=37 T2 is a positive three-state system and admits a literal
--   positive R4 with R2^2 = R4 + 2I, so the first positivity package is
--   formally refuted as an Ogg selector.
--
-- Remaining frontier:
-- derive a SIMULTANEOUS source-native double-coset/quaternion/rigidified-moduli
-- producer for the full Hecke family and compare its joint Hecke +
-- Frobenius/Fricke structure across Ogg and non-Ogg controls.  The particular
-- p=11 permutation generators are not derived from the mass formula alone.
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

import DASHI.Moonshine.BrandtStackUnweightingExact
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact
import DASHI.Moonshine.BrandtStackUnweightingControlsExact
import DASHI.Moonshine.P37NonOggPositiveHeckeControlExact
import DASHI.Moonshine.P37NonOggPositivePrimeSquareNeighboursExact
import DASHI.Moonshine.BrandtStackCrossPrimeSelectorCutsetExact
