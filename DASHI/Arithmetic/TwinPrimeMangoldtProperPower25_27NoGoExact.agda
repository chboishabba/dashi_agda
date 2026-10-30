module DASHI.Arithmetic.TwinPrimeMangoldtProperPower25_27NoGoExact where

------------------------------------------------------------------------
-- M14 NO-GO: THE GAP-2 PAIR (25,27) CONSISTS OF PROPER POWERS.
--
-- 25=5^2, 27=3^3. Both are proper powers of actual primes,
-- but both are composite. Hence a finite Mangoldt correlation
-- cannot be interpreted as a sum over genuine prime pairs
-- without explicitly subtracting proper-prime-power terms.
--
-- Uses original Nat primality/refutation and factorable-lift
-- proof owner. This does NOT claim any analytic lower bound.
-- Source-written, Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Nat.Primality as Prime
open import Relation.Nullary.Decidable.Core using (from-yes)
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact as Factors
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

fiveSquaredIs25 : Power.natPow 5 2 ≡ 25
fiveSquaredIs25 = refl

threeCubedIs27 : Power.natPow 3 3 ≡ 27
threeCubedIs27 = refl

gapTwoBetweenPowers : 25 + Twin.two ≡ 27
gapTwoBetweenPowers = refl

bothAreProperPowerValues :
  (Power.natPow 5 2 ≡ 25)
  × (Power.natPow 3 3 ≡ 27)
bothAreProperPowerValues = fiveSquaredIs25 , threeCubedIs27

twentyFiveHasNontrivialFactors :
  Factors.TwoNontrivialFactors 25
twentyFiveHasNontrivialFactors =
  Factors.twoNontrivialFactors 3 3 refl

twentySevenHasNontrivialFactors :
  Factors.TwoNontrivialFactors 27
twentySevenHasNontrivialFactors =
  Factors.twoNontrivialFactors 1 7 refl

twentyFiveIsComposite : Prime.Composite 25
twentyFiveIsComposite =
  Factors.twoNontrivialFactorsAreComposite 25
    twentyFiveHasNontrivialFactors

twentySevenIsComposite : Prime.Composite 27
twentySevenIsComposite =
  Factors.twoNontrivialFactorsAreComposite 27
    twentySevenHasNontrivialFactors

notTwinAtTwentyFive : Twin.TwinPrimeAt 25 → ⊥
notTwinAtTwentyFive pair =
  Factors.twoNontrivialFactorsRefutePrime
    25 twentyFiveHasNontrivialFactors (proj₁ pair)

-- This example refutes the tempting shortcut
-- "nonzero Lambda(n)*Lambda(n+2) always implies twin primes".
-- A fully formal nonzero statement additionally requires a
-- concrete scalar with log(3),log(5)>0, which this module
-- intentionally does not assume or fabricate.

------------------------------------------------------------------------
-- CT15 PARITY-COLLISION ADVERSARY: 103 IS A TRUE PRIME,
-- BUT 103+2=105=3*5*7 HAS ODD SQUAREFREE PRIME FACTOR COUNT.
--
-- In contrast, 3+2=5 is itself prime. Both partners therefore have
-- negative Mobius sign, but only the first (3,5) is a twin pair.
--
-- The tagged evidence below covers precisely the 1- and 3-factor
-- cases, NOT all odd squarefree factorisations or a full Mobius
-- oracle. A proof refuting universal promotion from this SUBSET
-- already refutes any inference based only on negative sign.
-- Original Mobius arithmetic, Nat.Primality and FactorableLift owners
-- retain priority. No signed correlation lower bound is claimed.
------------------------------------------------------------------------

threeIsCertifiedPrime : Prime.Prime 3
threeIsCertifiedPrime = from-yes (Prime.prime? 3)

fiveIsCertifiedPrime : Prime.Prime 5
fiveIsCertifiedPrime = from-yes (Prime.prime? 5)

sevenIsCertifiedPrime : Prime.Prime 7
sevenIsCertifiedPrime = from-yes (Prime.prime? 7)

hundredThreeIsCertifiedPrime : Prime.Prime 103
hundredThreeIsCertifiedPrime = from-yes (Prime.prime? 103)

record ThreeDistinctPrimeFactors (n : Nat) : Set where
  constructor three-distinct
  field
    factorA : Nat
    factorB : Nat
    factorC : Nat
    aPrime : Prime.Prime factorA
    bPrime : Prime.Prime factorB
    cPrime : Prime.Prime factorC
    aDifferentB : factorA ≡ factorB → ⊥
    aDifferentC : factorA ≡ factorC → ⊥
    bDifferentC : factorB ≡ factorC → ⊥
    productIsValue : n ≡ factorA * (factorB * factorC)

open ThreeDistinctPrimeFactors public

hundredFiveThreeDistinctPrimeFactors : ThreeDistinctPrimeFactors 105
hundredFiveThreeDistinctPrimeFactors =
  three-distinct
    3 5 7
    threeIsCertifiedPrime
    fiveIsCertifiedPrime
    sevenIsCertifiedPrime
    (λ ())
    (λ ())
    (λ ())
    refl

hundredFiveHasNontrivialFactors : Factors.TwoNontrivialFactors 105
hundredFiveHasNontrivialFactors =
  Factors.twoNontrivialFactors 1 33 refl

hundredFiveIsNotPrime : Prime.Prime 105 → ⊥
hundredFiveIsNotPrime =
  Factors.twoNontrivialFactorsRefutePrime
    105 hundredFiveHasNontrivialFactors

threeStartsGenuineTwin : Twin.TwinPrimeAt 3
threeStartsGenuineTwin =
  threeIsCertifiedPrime , fiveIsCertifiedPrime

hundredThreeDoesNotStartTwin : Twin.TwinPrimeAt 103 → ⊥
hundredThreeDoesNotStartTwin pair =
  hundredFiveIsNotPrime (proj₂ pair)

-- The two explicitly certified ODD squarefree shapes required for
-- the parity counterexample. No existential choice, fake source
-- factorisation or appeal to a QID is used.
data OddSquarefreePartnerShape (n : Nat) : Set where
  singletonPrime :
    Prime.Prime n → OddSquarefreePartnerShape n
  triplePrime :
    ThreeDistinctPrimeFactors n → OddSquarefreePartnerShape n

oddSquarefreeGenuinePartnerFive :
  OddSquarefreePartnerShape (3 + Twin.two)
oddSquarefreeGenuinePartnerFive =
  singletonPrime fiveIsCertifiedPrime

oddSquarefreeCounterfeit103 :
  OddSquarefreePartnerShape (103 + Twin.two)
oddSquarefreeCounterfeit103 =
  triplePrime hundredFiveThreeDistinctPrimeFactors

-- A universal assertion that *negative-sign-compatible* shapes
-- force genuine twin primes is constructively refuted by 103.
-- In fact the false inference fails already in the 1-or-3-factor
-- sublanguage; adding 5,7,... factor shapes cannot rescue it.
negativeMobiusShapeCannotForceTwin :
  ((n : Nat) →
    Prime.Prime n →
    OddSquarefreePartnerShape (n + Twin.two) →
    Twin.TwinPrimeAt n) →
  ⊥
negativeMobiusShapeCannotForceTwin inferred =
  hundredThreeDoesNotStartTwin
    (inferred 103 hundredThreeIsCertifiedPrime
      oddSquarefreeCounterfeit103)
