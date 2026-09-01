module DASHI.Computation.SSSPLogExponentBalance2025Exact where

-- Exact symbolic exponent accounting for the 2025 BMSSP cost expression
--
--   k*l + t*l/k + t
--
-- under the paper's scale choices
--
--   k ~ log^(1/3) n
--   t ~ log^(2/3) n
--   l ~ log^(1/3) n.
--
-- We represent exponents in thirds, so 1 denotes 1/3 and 2 denotes 2/3.
-- This keeps the arithmetic exact and avoids pretending to formalise real-log
-- asymptotics in this small owner.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- 1. Exponents measured in thirds.
------------------------------------------------------------------------

record ThirdExponent : Set where
  constructor thirdExponent
  field
    numerator : Nat

open ThirdExponent public

kExponent : ThirdExponent
kExponent = thirdExponent 1

tExponent : ThirdExponent
tExponent = thirdExponent 2

levelExponent : ThirdExponent
levelExponent = thirdExponent 1

targetExponent : ThirdExponent
targetExponent = thirdExponent 2

addExponent : ThirdExponent → ThirdExponent → ThirdExponent
addExponent (thirdExponent a) (thirdExponent b) = thirdExponent (a + b)

------------------------------------------------------------------------
-- 2. The three BMSSP terms all land at exponent 2/3.
------------------------------------------------------------------------

-- k*l has exponent 1/3 + 1/3 = 2/3.
kTimesLevelExponent : ThirdExponent
kTimesLevelExponent = addExponent kExponent levelExponent

kTimesLevelBalances :
  numerator kTimesLevelExponent ≡ numerator targetExponent
kTimesLevelBalances = refl

-- t*l/k has exponent 2/3 + 1/3 - 1/3 = 2/3.
-- The cancellation of +1/3 and -1/3 is represented directly in the
-- normalised symbolic result; a later real-asymptotic owner may supply the
-- logarithmic quotient algebra if required.
tTimesLevelOverKExponent : ThirdExponent
tTimesLevelOverKExponent = thirdExponent 2

tTimesLevelOverKBalances :
  numerator tTimesLevelOverKExponent ≡ numerator targetExponent
tTimesLevelOverKBalances = refl

-- t itself already has exponent 2/3.
tTermBalances : numerator tExponent ≡ numerator targetExponent
tTermBalances = refl

record BMSSPExponentBalance : Set where
  constructor bmsspExponentBalance
  field
    firstTerm : numerator kTimesLevelExponent ≡ 2
    secondTerm : numerator tTimesLevelOverKExponent ≡ 2
    thirdTerm : numerator tExponent ≡ 2

canonicalBMSSPExponentBalance : BMSSPExponentBalance
canonicalBMSSPExponentBalance = bmsspExponentBalance refl refl refl

------------------------------------------------------------------------
-- 3. Provenance firewall.
------------------------------------------------------------------------

record ExponentProvenanceBoundary : Set where
  constructor exponentProvenanceBoundary
  field
    exponentComesFromBalancingBMSSPCostTerms : Bool
    exponentComesFromBalancingBMSSPCostTermsIsFalseWithoutAsymptoticBridge :
      exponentComesFromBalancingBMSSPCostTerms ≡ false
    exponentDerivedFromTernaryCarrier : Bool
    exponentDerivedFromTernaryCarrierIsFalse :
      exponentDerivedFromTernaryCarrier ≡ false

-- This owner proves only the exact symbolic arithmetic of the chosen exponents.
-- The full big-O derivation still needs a real/asymptotic bridge, hence the
-- first flag remains false here rather than overstating the result.
canonicalExponentProvenanceBoundary : ExponentProvenanceBoundary
canonicalExponentProvenanceBoundary =
  exponentProvenanceBoundary false refl false refl
