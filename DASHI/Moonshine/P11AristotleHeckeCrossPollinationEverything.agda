module DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Aggregate for the characteristic-11 Brandt algebra, representation
-- falsifiers, positive fine geometry, stack controls, and source-native marked
-- full-level-2 / quaternion Hecke reconstruction.
--
-- Coarse arithmetic:
-- * geometric p=11 supersingular carrier {j=0,j=1728=1 mod11};
-- * independently checked B_11(2),B_11(3),B_11(5);
-- * automorphism-derived Brandt weights / weighted self-adjointness;
-- * coarse joint Hecke products and prime-square relations;
-- * cyclic/full Phi_4 distinction.
--
-- Representation falsifiers:
-- * section-generated intertwining and kernel completion are too weak;
-- * even a full unital algebra can be engineered linearly;
-- * natural six-sector positive lift impossible;
-- * six-sector / eleven-weight unweighted symmetric quotients ruled out.
--
-- Carrier reconstruction:
-- * Eichler--Deuring weights force the 2+3 sheet pattern;
-- * full level 2 gives C3\S3 disjoint-union C2\S3;
-- * H_11 Legendre/Deuring polynomial gives the same five X(2) points;
-- * frame deck S3 equals the anharmonic lambda S3.
--
-- Marked quaternion reconstruction:
-- * Voight's nonprincipal ideal gives the actual j=0 left order in the SAME
--   B=(-1,-11/Q) quaternion algebra;
-- * its trace-Gram determinant is derived entrywise as -121=-11^2;
-- * definite norm/congruence enumeration gives raw theta cells
--       j=0:    (ell3,ell5)=(2,0)
--       j=1728: (ell3,ell5)=(0,4);
-- * the norm-reduced six-case domains are exhaustively classified rather than
--   promoted to a generic unbounded lattice-enumerator claim;
-- * quotienting the free +/- kernel pairing gives marked identity-orbital counts
--       j=0:    (T3,T5)=(1,0)
--       j=1728: (T3,T5)=(0,2);
-- * therefore the ACTUAL marked orbital fingerprints are
--       T3^X(2)=(1,0,1,1,0,1)
--       T5^X(2)=(0,3,1,1,2,1),
--   correcting BOTH old hand-built edge distributions;
-- * corrected marked T3,T5 remain positive, commute, and admit positive T9,T25
--   with the true fine identity;
-- * corrected marked Hecke is Frobenius/Fricke equivariant;
-- * a second refined-theta tally path independently recovers the four cells.
--
-- Representation decomposition of the TRUE marked carrier:
--
--   Z[X(2)_ss] over Q = 2*1 + sgn + std
--
-- and corrected (T3,T5,F) fingerprints are
--   constant       ( 4, 6,+1)
--   Brandt newform (-1, 1,+1)
--   sign           ( 1,-3,-1)
--   standard       (-1, 1,+1).
--
-- Thus Brandt-newform and deck-standard sectors collide under the current joint
-- Hecke+Frobenius observation: deck S3 type is genuine extra information.
--
-- Non-Ogg control port:
-- * same full-level-2/Deuring front end at p=37 gives 3 coarse classes with six
--   frames each = 18 marked states;
-- * H_37 has nine nonsquare-discriminant quadratic factors, hence marked
--   Frobenius has 0 fixed points and 9 pairs;
-- * exact p=37 T3/T5 quaternion-order theta counts are NOT fabricated here and
--   remain the next cross-prime arithmetic leaves.
--
-- Current highest-alpha frontier:
-- 1. compute the three p=37 endomorphism orders / marked ell=3,5 theta cells
--    using the same Kohel/Kirschmer--Voight producer;
-- 2. reconstruct p=37 marked T3,T5 and compare the full deck-Hecke-Frobenius-
--    Fricke representation package against p=11;
-- 3. only then test an Ogg/Monster selector and reconnect #565/#558.
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
import DASHI.Moonshine.P11Level2DeckHeckeRigidityExact
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact
import DASHI.Moonshine.P11Level2T5QuaternionLoopFalsifierExact
import DASHI.Moonshine.P11Level2ArithmeticGeometryHighestAlphaRegression

import DASHI.Moonshine.P11VoightNonprincipalLeftOrderExact
import DASHI.Moonshine.P11VoightLeftOrderDiscriminantDerivedExact
import DASHI.Moonshine.P11MarkedQuaternionThetaExact
import DASHI.Moonshine.P11MarkedThetaBoundedCompletenessExact
import DASHI.Moonshine.P11MarkedRefinedThetaCrossCheckExact
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact
import DASHI.Moonshine.P11MarkedX2HeckeAlgebraExact
import DASHI.Moonshine.P11MarkedX2PrimeSquareNeighboursExact
import DASHI.Moonshine.P11MarkedX2FrobeniusFrickeExact
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact
import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact
import DASHI.Moonshine.P11MarkedQuaternionHeckeHighestAlphaRegression
