module DASHI.Moonshine.Monster3BJFineGeometricD4InvolutionNoGoExact where

------------------------------------------------------------------------
-- SELECTED MONSTER 3B: SOURCE-CHARACTER OBSTRUCTION TO THE SPECIFIED
-- GEOMETRIC D4 ACTION ON THE 65,610-DIMENSIONAL JFine zeta sector.
--
-- Mathematical sources (retain original attribution):
-- Conway--Norton, Monstrous Moonshine (1979).
-- Ford--McKay--Norton, More on replicable functions (1994).
-- Breuer--Magaard--Wilson, Verification of the conjugacy classes
-- and ordinary character table of the Monster, J. Algebra (2026).
-- Character values at 2A/2B and 6A..6F follow their verified first
-- Monster character row; OEIS A007254--A007259 transcribes the q^1
-- McKay--Thompson series coefficients.
--
-- IMPORTANT.  q^1(T_g) = 1 + chi_196883(g). We do NOT confuse the
-- q^0 constant coefficient with the first actual character coefficient.
-- Ordinary character values:
--   2A=4371; 2B=275.
--   6A=78; 6B=77; 6C=14; 6D=-3; 6E=5; 6F=27.
--
-- If g has order 2 and centralizes the chosen Monster z (3B), then
-- zg has order 6 and (zg)^-1=z²g. The rational ordinary character
-- has chi(zg)=chi(z²g), hence on the selected zeta sector
--       tr(g|W_zeta)=(chi(g)-chi(zg))/3.
-- Any source-compatible finite Monster class pair must obey the
-- equational condition below. Exhaustive constructor elimination proves
-- no such pair can attain either geometric D4 involution trace 810
-- (half-turn) or 2430 (reflection).
--
-- This is NOT a no-go for abstract E module equivalence or other,
-- genuinely linear/projective N(3B) extensions.  This file also does
-- not claim a kernel typecheck or independent proof of source tables.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

data MonsterInvolutionClass : Set where
  twoA twoB : MonsterInvolutionClass

data MonsterSixClass : Set where
  sixA sixB sixC sixD sixE sixF : MonsterSixClass

data GeometricD4Involution : Set where
  halfTurn reflection : GeometricD4Involution

sourceTwoTrace : MonsterInvolutionClass → Nat
sourceTwoTrace twoA = 4371
sourceTwoTrace twoB = 275

-- Signed order-six values are encoded exactly as
-- signedSix = positiveSix - negativeSix, keeping Nat equations.
positiveSixTrace : MonsterSixClass → Nat
positiveSixTrace sixA = 78
positiveSixTrace sixB = 77
positiveSixTrace sixC = 14
positiveSixTrace sixD = 0
positiveSixTrace sixE = 5
positiveSixTrace sixF = 27

negativeSixTrace : MonsterSixClass → Nat
negativeSixTrace sixA = 0
negativeSixTrace sixB = 0
negativeSixTrace sixC = 0
negativeSixTrace sixD = 3
negativeSixTrace sixE = 0
negativeSixTrace sixF = 0

geometricTrace : GeometricD4Involution → Nat
geometricTrace halfTurn = 810
geometricTrace reflection = 2430

-- Rearrangement of chi_2 - chi_6 = 3*chi_zeta:
-- chi_2 + negativeSix = 3*geometricTrace + positiveSix.
SourceCompatibleTrace :
  MonsterInvolutionClass → MonsterSixClass →
  GeometricD4Involution → Set
SourceCompatibleTrace inv six desired =
  sourceTwoTrace inv + negativeSixTrace six
  ≡ (3 * geometricTrace desired) + positiveSixTrace six

-- These are impossibility proofs, not postulates, example booleans, or
-- quoted character decomposition assertions.
noGeometricD4InvolutionTrace :
  (inv : MonsterInvolutionClass) →
  (six : MonsterSixClass) →
  (desired : GeometricD4Involution) →
  SourceCompatibleTrace inv six desired → ⊥
noGeometricD4InvolutionTrace twoA sixA halfTurn ()
noGeometricD4InvolutionTrace twoA sixA reflection ()
noGeometricD4InvolutionTrace twoA sixB halfTurn ()
noGeometricD4InvolutionTrace twoA sixB reflection ()
noGeometricD4InvolutionTrace twoA sixC halfTurn ()
noGeometricD4InvolutionTrace twoA sixC reflection ()
noGeometricD4InvolutionTrace twoA sixD halfTurn ()
noGeometricD4InvolutionTrace twoA sixD reflection ()
noGeometricD4InvolutionTrace twoA sixE halfTurn ()
noGeometricD4InvolutionTrace twoA sixE reflection ()
noGeometricD4InvolutionTrace twoA sixF halfTurn ()
noGeometricD4InvolutionTrace twoA sixF reflection ()
noGeometricD4InvolutionTrace twoB sixA halfTurn ()
noGeometricD4InvolutionTrace twoB sixA reflection ()
noGeometricD4InvolutionTrace twoB sixB halfTurn ()
noGeometricD4InvolutionTrace twoB sixB reflection ()
noGeometricD4InvolutionTrace twoB sixC halfTurn ()
noGeometricD4InvolutionTrace twoB sixC reflection ()
noGeometricD4InvolutionTrace twoB sixD halfTurn ()
noGeometricD4InvolutionTrace twoB sixD reflection ()
noGeometricD4InvolutionTrace twoB sixE halfTurn ()
noGeometricD4InvolutionTrace twoB sixE reflection ()
noGeometricD4InvolutionTrace twoB sixF halfTurn ()
noGeometricD4InvolutionTrace twoB sixF reflection ()

-- Any claimed D4 intertwiner on W_zeta must, at its half-turn,
-- produce one of the 2A/2B and 6A..6F source character pairs.
-- Those exact finite possibilities are already eliminated above.
record GeometricD4HalfTurnSourceWitness : Set where
  field
    involutionClass : MonsterInvolutionClass
    productOrderSixClass : MonsterSixClass
    halfTurnCharacterEquation :
      SourceCompatibleTrace involutionClass productOrderSixClass halfTurn
open GeometricD4HalfTurnSourceWitness public

noSelectedMonster3BGeometricD4HalfTurn :
  GeometricD4HalfTurnSourceWitness → ⊥
noSelectedMonster3BGeometricD4HalfTurn witness =
  noGeometricD4InvolutionTrace
    (involutionClass witness)
    (productOrderSixClass witness)
    halfTurn
    (halfTurnCharacterEquation witness)
