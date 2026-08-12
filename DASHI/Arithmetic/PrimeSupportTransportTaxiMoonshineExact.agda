module DASHI.Arithmetic.PrimeSupportTransportTaxiMoonshineExact where

------------------------------------------------------------------------
-- PRIME-SUPPORT TRANSPORT: 1729 -> 196883
--
-- This file formalises the arithmetic transport itself and keeps the semantic
-- boundary explicit: reaching the integer 196883 does not by itself construct
-- a Monster representation or a moonshine theorem.
--
-- Representation/moonshine provenance:
-- J. H. Conway and S. P. Norton, "Monstrous Moonshine", Bulletin of the London
-- Mathematical Society 11 (1979), 308-339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Robert L. Griess Jr. and Stephen D. Smith,
-- "Minimal dimensions for modular representations of the monster",
-- Communications in Algebra 22 (1994), 6279-6294.
-- DOI: 10.1080/00927879408825189.
--
-- Historical taxicab provenance:
-- Srinivasa Ramanujan / G. H. Hardy: 1729 is the least positive integer
-- expressible as a sum of two positive cubes in two distinct ways.
-- No DOI is asserted for the historical anecdote.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_; _*_)
open import Data.Empty using (⊥)

cube : Nat → Nat
cube n = n * n * n

taxiProduct : Nat
taxiProduct = 7 * 13 * 19

taxiProductIs1729 : taxiProduct ≡ 1729
taxiProductIs1729 = refl

taxicabSumOne : cube 1 + cube 12 ≡ 1729
taxicabSumOne = refl

taxicabSumTwo : cube 9 + cube 10 ≡ 1729
taxicabSumTwo = refl

------------------------------------------------------------------------
-- FRACTRAN-like replacement step with an explicit multiplicative witness.
-- A rule n/d is applicable when before = d*rest and yields after = n*rest.
------------------------------------------------------------------------

record PrimeReplacementStep
    (denominator numerator before after : Nat) : Set where
  constructor primeReplacementStep
  field
    rest : Nat
    beforeFactorisation : before ≡ denominator * rest
    afterFactorisation : after ≡ numerator * rest

open PrimeReplacementStep public

step47over7 : PrimeReplacementStep 7 47 1729 11609
step47over7 = primeReplacementStep 247 refl refl

step59over13 : PrimeReplacementStep 13 59 11609 52687
step59over13 = primeReplacementStep 893 refl refl

step71over19 : PrimeReplacementStep 19 71 52687 196883
step71over19 = primeReplacementStep 2773 refl refl

record ThreeStepPrimeTransport : Set where
  constructor threeStepPrimeTransport
  field
    start state1 state2 target : Nat
    firstDen firstNum secondDen secondNum thirdDen thirdNum : Nat
    first : PrimeReplacementStep firstDen firstNum start state1
    second : PrimeReplacementStep secondDen secondNum state1 state2
    third : PrimeReplacementStep thirdDen thirdNum state2 target

open ThreeStepPrimeTransport public

taxiEarns196883 : ThreeStepPrimeTransport
taxiEarns196883 =
  threeStepPrimeTransport
    1729 11609 52687 196883
    7 47 13 59 19 71
    step47over7 step59over13 step71over19

targetPrimeProduct : 47 * 59 * 71 ≡ 196883
targetPrimeProduct = refl

------------------------------------------------------------------------
-- Exact combinatorial cardinality behind C(12,3)=220.
-- This proves the count independently of any particular list of twelve
-- denominators.  A concrete imported enumeration can reuse this cardinality
-- theorem without guessing its twelve-element source set here.
------------------------------------------------------------------------

choose : Nat → Nat → Nat
choose n zero = 1
choose zero (suc k) = zero
choose (suc n) (suc k) = choose n k + choose n (suc k)

chooseTwelveThreeIs220 : choose 12 3 ≡ 220
chooseTwelveThreeIs220 = refl

------------------------------------------------------------------------
-- Semantic-promotion boundary.
------------------------------------------------------------------------

data ArithmeticLandingAuthority : Set where
  arithmeticLandingOnly : ArithmeticLandingAuthority

data MoonshinePromotion : ArithmeticLandingAuthority → Set where

arithmeticLandingDoesNotConstructMoonshine :
  MoonshinePromotion arithmeticLandingOnly → ⊥
arithmeticLandingDoesNotConstructMoonshine ()

record TaxiMoonshineBoundary : Set where
  constructor taxiMoonshineBoundary
  field
    arithmeticTraceVerified : Bool
    arithmeticTraceVerifiedIsTrue : arithmeticTraceVerified ≡ true
    endpointAlonePromotesMoonshine : Bool
    endpointAlonePromotesMoonshineIsFalse : endpointAlonePromotesMoonshine ≡ false

canonicalTaxiMoonshineBoundary : TaxiMoonshineBoundary
canonicalTaxiMoonshineBoundary = taxiMoonshineBoundary true refl false refl
