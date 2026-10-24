module DASHI.Moonshine.Monster3BJFineD4CandidateMultiplicityExact where

------------------------------------------------------------------------
-- FOLLOW-UP AFTER THE GEOMETRIC D4 INVOLUTION CHARACTER NO-GO
--
-- Existing owners:
--   Monster3BJFineGeometricD4InvolutionNoGoExact -- original exclusion.
--   Monster3BFiniteHeisenberg* -- finite H_6, Weyl/Schrodinger laws.
--   IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact --
--     a Fin90 index is not the source-normalizer linear 90-module.
--   Trialectic369MonomialMultiplicityBasisSpecialisationExact --
--     optional signed/phase-bearing basis route.
--
-- New exact D4 character prescription on a 90-DIMENSIONAL LINEAR space.
-- It does NOT assert a source-selected D4 embedding or the 6.Suz action.
-- Only dimensions, traces and class consistency are proved here;
-- the signed-permutation generator implementation/check is in
-- scripts/jfine_3b_linear_multiplicity_d4_repair.py .
--
-- Primary attribution: Conway--Norton (1979), Ford--McKay--Norton
-- (1994), Breuer--Magaard--Wilson (2026), and the ATLAS Monster
-- power maps. q^1 McKay-Thompson transcripts: OEIS A007247 (4B),
-- A058485 (12G), A007257 (6D).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

multiplicityA1 : Nat
multiplicityA1 = 23

multiplicityA2 : Nat
multiplicityA2 = 5

multiplicityB1 : Nat
multiplicityB1 = 13

multiplicityB2 : Nat
multiplicityB2 = 13

multiplicityE2 : Nat
multiplicityE2 = 18

-- The two-dimensional irreducible E2 contributes twice its count.
ninetyIsIrreducibleDimensionSum :
  23 + 5 + 13 + 13 + 2 * 18 ≡ 90
ninetyIsIrreducibleDimensionSum = refl

-- In D4, r^2 acts as +1 on all 1D irreducibles and -I_2 on E2.
halfTurnCharacterIs18 :
  23 + 5 + 13 + 13 ≡ 18 + 2 * 18
halfTurnCharacterIs18 = refl

-- r acts +1 on A1,A2, -1 on B1,B2 and trace zero on E2.
quarterTurnCharacterIs2 :
  23 + 5 ≡ 2 + 13 + 13
quarterTurnCharacterIs2 = refl

-- Both geometric reflection classes have multiplicity trace 18.
axisReflectionCharacterIs18 :
  23 + 13 ≡ 18 + 5 + 13
axisReflectionCharacterIs18 = refl

diagonalReflectionCharacterIs18 :
  23 + 13 ≡ 18 + 5 + 13
diagonalReflectionCharacterIs18 = refl

-- Existing honest geometric six-trit fibre lift has character
-- [729,81,9,81,81] in D4 class order [e,r^2,r,r*s,s].
fibreTensorIdentity : 729 * 90 ≡ 65610
fibreTensorIdentity = refl

fibreTensorHalfTurn : 81 * 18 ≡ 1458
fibreTensorHalfTurn = refl

fibreTensorQuarterTurn : 9 * 2 ≡ 18
fibreTensorQuarterTurn = refl

fibreTensorReflections : 81 * 18 ≡ 1458
fibreTensorReflections = refl

-- Monster SOURCE character values (NOT derived from this Agda module).
-- For 2A and 6D: 4371 and -3; tr(W_zeta, inv)=1458.
sourceTwoAAndSixDPermitHalfTurn :
  4371 + 3 ≡ 3 * 1458
sourceTwoAAndSixDPermitHalfTurn = refl

-- For 4B and 12G: 51 and -3; tr(W_zeta, quarter)=18.
sourceFourBAndTwelveGPermitQuarter :
  51 + 3 ≡ 3 * 18
sourceFourBAndTwelveGPermitQuarter = refl

-- Necessary source-class pattern, NOT evidence that a D4 with these
-- classes actually embeds in the Monster 3B phase-preserving centralizer.
-- 6D has third power 2A and square 3B; 12G has third power 4B
-- and fourth power 3B, while 4B squares to 2A (ATLAS).
--
-- The source-normalizer full 6.Suz multiplicity action and the actual
-- phase-resolved Hom/cocycle remain owned by existing generic interfaces.
