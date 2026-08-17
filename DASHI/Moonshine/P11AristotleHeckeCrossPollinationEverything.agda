module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the characteristic-11 Brandt algebra, representation
-- falsifiers, positive fine geometry, stack controls, and the new source-native
-- full-level-2 / Legendre rigidification.
--
-- Arithmetic side:
-- * source-certified supersingular carrier {j=0,j=1728=1 mod11};
-- * independent Phi_2/Phi_3/Phi_5 neighbour systems;
-- * automorphism-derived Brandt weights, weighted self-adjointness;
-- * commuting B_11(2), B_11(3), B_11(5) and prime-square relations;
-- * cyclic/full Phi_4 correction and positive T2^2 path-count realization.
--
-- Representation falsifiers:
-- * cheap section-generated lifts and kernel nonuniqueness;
-- * even a full unital Hecke algebra can be engineered algebraically;
-- * natural six-sector positive lift impossible;
-- * six-sector and eleven-weight ordinary symmetric binary quotients ruled out.
--
-- Positive p=11 producer:
-- * generic positive neighbour / equitable quotient / Schreier APIs;
-- * five-state 2+3 fine carrier;
-- * positive ell=2,3,5 systems and inverse-closed permutation realizations;
-- * commuting prime operators;
-- * literal positive R4,R9,R25 systems and true-identity prime-square laws.
--
-- Stack / control layer:
-- * monodromy weights separated from reciprocal sheet multiplicities;
-- * p=11 weights (3,2) -> sheets (2,3);
-- * p=37 sheets 3 and positive T2/T4 control;
-- * p=43 reciprocal sheet count 7;
-- * positive stack-unweighted T2-square geometry formally refuted as Ogg selector.
--
-- Full-level-2 arithmetic geometry:
-- * one explicit six-frame regular S3 torsor with genuine S3 relations;
-- * reduced order-3/order-2 stabilizer quotients give exactly 2+3 sheets;
-- * exact bijection with the existing A0,A1,B0,B1,B2 carrier;
-- * right deck S3 derived from the frame torsor;
-- * existing odd-prime R3/R5 aggregate correspondences are deck-equivariant;
-- * H_11 Legendre/Deuring factor pattern gives five supersingular X(2)
--   parameters: three F_11 roots over j=1728 and one quadratic pair over j=0;
-- * Legendre anharmonic S3 equals the frame-torsor deck S3 on those five points.
--
-- Remaining highest-alpha producer:
-- derive the INDIVIDUAL odd-prime Hecke edges on this explicit supersingular
-- Legendre/full-level-2 carrier from the lambda modular equation, quaternion
-- ideal-class correspondence, or an equivalent source-native double-coset
-- construction.  For ell=2, keep the level-dividing operator separate from the
-- prime-to-level T_ell story.  Then run the same joint Hecke/deck/Frobenius/
-- Fricke construction on non-Ogg controls.
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
import DASHI.Moonshine.BrandtStackUnweightingHighestAlphaRegression

import DASHI.Moonshine.P11FullLevel2RigidificationExact
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact
import DASHI.Moonshine.P11SupersingularLegendreLevel2ChartExact
import DASHI.Moonshine.P11LegendreAnharmonicDeckExact
import DASHI.Moonshine.P11Level2ArithmeticGeometryHighestAlphaRegression
