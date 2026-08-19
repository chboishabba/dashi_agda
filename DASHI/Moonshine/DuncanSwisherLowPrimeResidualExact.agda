module DASHI.Moonshine.DuncanSwisherLowPrimeResidualExact where

------------------------------------------------------------------------
-- LOW-PRIME EXCEPTIONAL RESIDUALS: WORK BACKWARDS FROM THE SOURCE GAP
--
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Remark 1.3 records that, although the two Duncan--Swisher right-hand sides
-- agree at p=2 and p=3, their methods do not recover the Monster exponents:
--
--   p=2: common RHS = 36,  v_2(|M|)=46;
--   p=3: common RHS = 18,  v_3(|M|)=20.
--
-- The authors explicitly leave p=2,3 to future work.
--
-- DASHI CONTRIBUTION
--
-- Do not extend the p>3 theorem by wishful implication.  Instead isolate the
-- exact unexplained residual
--
--   v_p(|M|) = commonDuncanSwisherRHS(p) + lowPrimeResidual(p)
--
-- with residuals 10 and 2.  Because the modular-function and supersingular
-- right-hand sides already agree at these low primes, the missing phenomenon is
-- common to both source formulas rather than a disagreement between the two
-- observers.  This is the precise backwards frontier to explain.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

data DuncanSwisherLowPrime : Set where
  low2 low3 : DuncanSwisherLowPrime

lowPrimeLane : DuncanSwisherLowPrime → Lane.MonsterPrimeLane
lowPrimeLane low2 = Lane.p2
lowPrimeLane low3 = Lane.p3

commonDuncanSwisherRHS : DuncanSwisherLowPrime → Nat
commonDuncanSwisherRHS low2 = 36
commonDuncanSwisherRHS low3 = 18

modularFormulaRHS : DuncanSwisherLowPrime → Nat
modularFormulaRHS = commonDuncanSwisherRHS

supersingularFormulaRHS : DuncanSwisherLowPrime → Nat
supersingularFormulaRHS = commonDuncanSwisherRHS

actualMonsterExponent : DuncanSwisherLowPrime → Nat
actualMonsterExponent prime =
  Exponent.monsterOrderExponent (lowPrimeLane prime)

lowPrimeResidual : DuncanSwisherLowPrime → Nat
lowPrimeResidual low2 = 10
lowPrimeResidual low3 = 2

modularAndSupersingularRHSAgree :
  (prime : DuncanSwisherLowPrime) →
  modularFormulaRHS prime ≡ supersingularFormulaRHS prime
modularAndSupersingularRHSAgree low2 = refl
modularAndSupersingularRHSAgree low3 = refl

actualExponentReconstructsFromRHSPlusResidual :
  (prime : DuncanSwisherLowPrime) →
  actualMonsterExponent prime
  ≡ commonDuncanSwisherRHS prime + lowPrimeResidual prime
actualExponentReconstructsFromRHSPlusResidual low2 = refl
actualExponentReconstructsFromRHSPlusResidual low3 = refl

p2ResidualIsTen : lowPrimeResidual low2 ≡ 10
p2ResidualIsTen = refl

p3ResidualIsTwo : lowPrimeResidual low3 ≡ 2
p3ResidualIsTwo = refl

p2ResidualNonzero : lowPrimeResidual low2 ≡ 0 → ⊥
p2ResidualNonzero ()

p3ResidualNonzero : lowPrimeResidual low3 ≡ 0 → ⊥
p3ResidualNonzero ()

p2PublishedRHSMatchesExistingCorrection :
  commonDuncanSwisherRHS low2
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p2
p2PublishedRHSMatchesExistingCorrection = refl

p3PublishedRHSMatchesExistingCorrection :
  commonDuncanSwisherRHS low3
  ≡ Exponent.duncanSwisherExceptionalRHS Lane.p3
p3PublishedRHSMatchesExistingCorrection = refl

record DuncanSwisherLowPrimeResidualBoundary : Set where
  constructor duncanSwisherLowPrimeResidualBoundary
  field
    theorem11And12RHSAgreeAtTwoAndThree : Bool
    p2GapIsTen : Bool
    p3GapIsTwo : Bool
    pGreaterThanThreeTheoremExtendedHere : Bool
    lowPrimeResidualMechanismExplainedHere : Bool
    nextLowPrimeFrontierIsResidualMechanism : Bool

canonicalDuncanSwisherLowPrimeResidualBoundary :
  DuncanSwisherLowPrimeResidualBoundary
canonicalDuncanSwisherLowPrimeResidualBoundary =
  duncanSwisherLowPrimeResidualBoundary
    true true true false false true
