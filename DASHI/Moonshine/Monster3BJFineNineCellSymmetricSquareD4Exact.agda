module DASHI.Moonshine.Monster3BJFineNineCellSymmetricSquareD4Exact where

------------------------------------------------------------------------
-- PRIOR-ART REUSE / ATTRIBUTION
--   DASHI.Biology.TernaryMonsterSymmetryCandidateExact owns raw nine-cell D4
--       representation: 3A1 + B1 + B2 + 2E.
--   DASHI.Foundations.D4SO3NineIrrepRestrictionExact owns distinct j=4:
--       2A1 + A2 + B1 + B2 + 2E = 1 + Reg(D4).
--   DASHI.Moonshine.Monster3BNormalizerBridge owns 90=12+78 dimensions.
--   DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact
--       owns kernel/phase constraints for actual 6.Suz to N(3B).
--
-- FINITE D4 CONSTRUCTION ONLY:
-- U12 = V9 ⊕ A1 ⊕ B1 ⊕ B2 = 4A1+2B1+2B2+2E.
-- Sym² U12 has D4 character (78,14,2,14,14).
-- U12 ⊕ Sym² U12 has D4 character (90,18,2,18,18).
--
-- The symmetric-square character identity is classical representation theory
-- (see Serre). The natural 6.Suz degree12 and 78 symmetrizations are discussed
-- in Gabriele Nebe, Symmetrizations of quadratic and Hermitian forms\n-- (2025), DOI 10.1007/s10801-025-01399-2, section 6.\n-- The actual selected Monster 3B 6.Suz 78 need not equal
-- Sym² of its 12; quotient kernel/central phases require source matching.
--
-- This module has no postulate, no Monster intertwiner axiom, and no
-- asserted Agda typecheck receipt for this exact head.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4
import DASHI.Moonshine.Monster3BNormalizerBridge as Monster

-- Original nine-cell module, not the SO3 j=4 module.
nineA1 : D4.rawNineMultiplicity D4.A1 ≡ 3
nineA1 = refl
nineA2 : D4.rawNineMultiplicity D4.A2 ≡ 0
nineA2 = D4.rawA2MultiplicityIsZero
nineB1 : D4.rawNineMultiplicity D4.B1 ≡ 1
nineB1 = refl
nineB2 : D4.rawNineMultiplicity D4.B2 ≡ 1
nineB2 = refl
nineE2 : D4.rawNineMultiplicity D4.E2 ≡ 2
nineE2 = refl

-- Nine position vectors plus three signed one-dimensional sectors.
u12A1 : Nat
u12A1 = 4
u12A2 : Nat
u12A2 = 0
u12B1 : Nat
u12B1 = 2
u12B2 : Nat
u12B2 = 2
u12E2 : Nat
u12E2 = 2

ninePlusThreeTwelve : 9 + 3 ≡ Monster.naturalSuzukiDegree
ninePlusThreeTwelve = refl

twelveCharacterDegree :
  u12A1 + u12A2 + u12B1 + u12B2 + 2 * u12E2 ≡ 12
twelveCharacterDegree = refl

-- D4 class order: 1, r², {r,r^-1}, axis reflections, diagonal reflections.
-- Character(U12) = (12,4,0,4,4).
-- 2 χ_Sym²(g) = χ_U(g)^2 + χ_U(g²).
symSquareDegree : 12 * 13 ≡ 2 * 78
symSquareDegree = refl

symSquareHalfTrace : 4 * 4 + 12 ≡ 2 * 14
symSquareHalfTrace = refl

symSquareQuarterTrace : 0 * 0 + 4 ≡ 2 * 2
symSquareQuarterTrace = refl

symSquareReflectionsTrace : 4 * 4 + 12 ≡ 2 * 14
symSquareReflectionsTrace = refl

twelvePlusSeventyEightIsNinety :
  Monster.naturalSuzukiDegree + Monster.symmetricSquareDualDegree ≡ 90
twelvePlusSeventyEightIsNinety = Monster.multiplicity-degree-is-90

signedRepairIdentity : 12 + 78 ≡ 90
signedRepairIdentity = refl

signedRepairHalf : 4 + 14 ≡ 18
signedRepairHalf = refl

signedRepairQuarter : 0 + 2 ≡ 2
signedRepairQuarter = refl

signedRepairReflection : 4 + 14 ≡ 18
signedRepairReflection = refl

fibreTensorSelectedPhase : 729 * 90 ≡ 65610
fibreTensorSelectedPhase = refl

sourceNecessaryHalfTurn : 81 * 18 ≡ 1458
sourceNecessaryHalfTurn = refl

sourceNecessaryQuarterTurn : 9 * 2 ≡ 18
sourceNecessaryQuarterTurn = refl

-- Actual faithful 6.Suz U12 has central involution acting by -I.
-- Its symmetric square has central sign (-1)^2=+1, so cannot be a
-- faithful 78 of full 6.Suz. This finite sign algebra is proved
-- independently of choosing actual central-character labels.
data CentralSign : Set where
  positive negative : CentralSign

infixl 7 _*sign_
_*sign_ : CentralSign → CentralSign → CentralSign
positive *sign y = y
negative *sign positive = negative
negative *sign negative = positive

faithfulCentralMinusSquaresToPlus :
  negative *sign_ negative ≡ positive
faithfulCentralMinusSquaresToPlus = refl

centralPlusIsNotMinus : positive ≡ negative → ⊥
centralPlusIsNotMinus ()

-- Constructor-elimination proof that a faithful central-minus 78
-- CANNOT equal the symmetric square central-plus carrier.
symmetricSquareCannotHaveFaithfulCentralMinus :
  negative *sign_ negative ≡ negative → ⊥
symmetricSquareCannotHaveFaithfulCentralMinus ()

-- Epistemic separation: the source 12+78 *dimension* does not assert
-- that the specific quotient-descending 78 is the actual symmetric square.
-- D4-model equivalence is instead produced in the local Python consumer.
