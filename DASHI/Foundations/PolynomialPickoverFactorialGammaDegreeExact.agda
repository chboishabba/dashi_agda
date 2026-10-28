module DASHI.Foundations.PolynomialPickoverFactorialGammaDegreeExact where

------------------------------------------------------------------------
-- POLYNOMIAL VIDEO / GAMMA / PICKOVER / DEGREE-PHASE MAX-CUT
--
-- SOURCES: Euler (1729/1738) on factorial interpolation; Legendre (1811)
-- capital Gamma notation; NIST DLMF chapter 5 Gamma function;
-- classical Euler formula e^(i theta) = cos theta + i sin theta.
-- Prior DASHI owner: PR #1260 factorial CRT, phase and Machin checks.
--
-- Gamma (capital G) is NOT theta (angle).  Gamma(n+1)=n! is a
-- classical theorem. Here the exact elementary NATURAL factorial
-- and integer powering are reused. The analytic interpolation and
-- the radian sine sign remain explicitly conditional / outstanding.
--
-- Import nothing from PR #1260 because it is an independent DRAFT
-- branch. This is a typed consumer, not copy-pasted producer proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat.Base using (_!; _^_; _%_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)

-- Actual factorial, not a new duplicate factorial implementation.
factorialBaseCase : zero ! ≡ 1
factorialBaseCase = refl

factorialRecurrence : (n : Nat) →
  (suc n) ! ≡ suc n * (n !)
factorialRecurrence n = refl

factorialIndex9999 : Nat
factorialIndex9999 = 9999 !

pickoverInteger : Nat
pickoverInteger = 99 ^ factorialIndex9999

factorialRecurrenceAt9999 :
  (10000 !) ≡ 10000 * (9999 !)
factorialRecurrenceAt9999 = refl

-- Note the shifted indexing:
-- Gamma(10000)=9999!, not Gamma(9999)=9999!.
record GammaIntegerInterpolation : Set₁ where
  field
    Value : Set
    embedNatural : Nat → Value
    gammaNatural : Nat → Value
    gammaAtSuccessor :
      (n : Nat) →
      gammaNatural (suc n) ≡ embedNatural (n !)
open GammaIntegerInterpolation public

gammaAt10000Is9999Factorial :
  (G : GammaIntegerInterpolation) →
  gammaNatural G 10000 ≡ embedNatural G factorialIndex9999
gammaAt10000Is9999Factorial G =
  gammaAtSuccessor G 9999

-- The original Pickover expression is a POWER of the factorial-indexed
-- exponent, NOT the factorial of a power or a factorial tower.
data PickoverExpression : Set where
  powerOfFactorial
    factorialOfPower
    factorialTower : PickoverExpression

canonicalPickoverExpression : PickoverExpression
canonicalPickoverExpression = powerOfFactorial

notFactorialOfPower :
  canonicalPickoverExpression ≡ factorialOfPower → ⊥
notFactorialOfPower ()

notFactorialTower :
  canonicalPickoverExpression ≡ factorialTower → ⊥
notFactorialTower ()

-- Exact small modular cycle:
-- 99^1 mod 360 = 99; 99^2 mod 360 = 81;
-- multiplying the even/odd residues by 99 swaps them.
-- The mathematical induction for all exponents uses the ordinary
-- compatibility of modular multiplication. The separate Python
-- replay checks the WHOLE exponent 9999! exactly.
ninetyNineSquaredMod360 : ((99 * 99) % 360) ≡ 81
ninetyNineSquaredMod360 = refl

eightyOneTimesNinetyNineMod360 :
  ((81 * 99) % 360) ≡ 99
eightyOneTimesNinetyNineMod360 = refl

ninetyNineTimesEightyOneMod360 :
  ((99 * 81) % 360) ≡ 99
ninetyNineTimesEightyOneMod360 = refl

-- Valid finite-state recurrence of the pair (99,81); this abstracts
-- the degree residues without evaluating any astronomically large power.
data PositiveDegreePowerResidue : Set where
  oddPower99 evenPower81 : PositiveDegreePowerResidue

nextDegreePowerResidue :
  PositiveDegreePowerResidue → PositiveDegreePowerResidue
nextDegreePowerResidue oddPower99 = evenPower81
nextDegreePowerResidue evenPower81 = oddPower99

nextDegreePowerResidueInvolutive :
  (r : PositiveDegreePowerResidue) →
  nextDegreePowerResidue (nextDegreePowerResidue r) ≡ r
nextDegreePowerResidueInvolutive oddPower99 = refl
nextDegreePowerResidueInvolutive evenPower81 = refl

degreePowerResidue : Nat → PositiveDegreePowerResidue
degreePowerResidue zero = oddPower99
degreePowerResidue (suc n) =
  nextDegreePowerResidue (degreePowerResidue n)

-- The *seed* zero here represents power 99^1, not 99^0.
-- Even positive exponents therefore correspond to step counts odd.
twoMoreKeepsDegreeResidue :
  (n : Nat) →
  degreePowerResidue (suc (suc n)) ≡ degreePowerResidue n
twoMoreKeepsDegreeResidue n =
  nextDegreePowerResidueInvolutive (degreePowerResidue n)

doubleIndex : Nat → Nat
doubleIndex zero = zero
doubleIndex (suc n) = suc (suc (doubleIndex n))

degreeResidueAtEvenPositivePower :
  (n : Nat) →
  degreePowerResidue (suc (doubleIndex n)) ≡ evenPower81
degreeResidueAtEvenPositivePower zero = refl
degreeResidueAtEvenPositivePower (suc n) =
  trans
    (twoMoreKeepsDegreeResidue (suc (doubleIndex n)))
    (degreeResidueAtEvenPositivePower n)

data AngleUnit : Set where
  radians degrees : AngleUnit

data PhaseSign : Set where
  positive negative unknown : PhaseSign

-- One OFFICIAL scoped result and one unsolved original problem.
-- Source math: sin(81 degrees)>0. Source tool replay:
-- pow(99, factorial(9999), 360)==81.
isDegreeAngleSolved : Bool
isDegreeAngleSolved = true

isRadianAngleSolvedHere : Bool
isRadianAngleSolvedHere = false

radianPickoverSignIsNotProved :
  isRadianAngleSolvedHere ≡ false
radianPickoverSignIsNotProved = refl

-- Theta is a variable naming the angle of the complex exponential;
-- it is NOT being redefined as Euler's Gamma/factorial function.
record AnalyticPhaseAuthority : Set₁ where
  field
    Real : Set
    theta : Real
    sine : Real → Real
    phaseInteger : Nat → Real
    degreeAngle : Nat → Real
    degreeAngleSignProof : Set
    radianSineSignCertificate : Set
