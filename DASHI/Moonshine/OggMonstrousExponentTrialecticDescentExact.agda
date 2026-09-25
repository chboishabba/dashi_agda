module DASHI.Moonshine.OggMonstrousExponentTrialecticDescentExact where

------------------------------------------------------------------------
-- OGG / MONSTROUS-EXPONENT ARITHMETIC TRIALECTIC
--
-- ATTRIBUTION
--
-- External theorem-bearing input:
--   John F. R. Duncan and Holly Swisher,
--   "Modular Functions and the Monstrous Exponents" (2026),
--   arXiv:2602.09135, DOI 10.48550/arXiv.2602.09135.
--
-- The exact p>3 three-source valuation decomposition is consumed through
-- MonsterOrderExponentCorrectionExact.  DASHI contributes only the typed
-- three-chart/descent packaging below and the downstream representation
-- firewall.
--
-- This owner is intentionally upstream of any 369 / T^9 encoding:
--
--   exact arithmetic
--      -> typed (A_p,B_p,C_p)
--      -> exact sum e_p
--      -> optional downstream coarse representation.
--
-- It therefore does NOT derive the arithmetic triple from a ternary cube.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source

------------------------------------------------------------------------
-- 1. Three externally theorem-bearing contribution roles.
------------------------------------------------------------------------

data ModularContributionRole : Set where
  frickeComparison : ModularContributionRole
  levelPComparison : ModularContributionRole
  levelP2Comparison : ModularContributionRole

record ArithmeticTrialectic
  (prime : Lane.MonsterPrimeLane) : Set where
  constructor arithmetic-trialectic
  field
    aboveThree : Exponent.PrimeAboveThree prime
    contribution : Exponent.ModularValuationContribution prime

open ArithmeticTrialectic public

canonicalArithmeticTrialectic :
  (prime : Lane.MonsterPrimeLane) ->
  (proof : Exponent.PrimeAboveThree prime) ->
  ArithmeticTrialectic prime
canonicalArithmeticTrialectic prime proof =
  arithmetic-trialectic proof (Exponent.modularContribution prime proof)

A :
  {prime : Lane.MonsterPrimeLane} ->
  ArithmeticTrialectic prime ->
  Nat
A trial = Exponent.frickeLevel (contribution trial)

B :
  {prime : Lane.MonsterPrimeLane} ->
  ArithmeticTrialectic prime ->
  Nat
B trial = Exponent.primeLevel (contribution trial)

C :
  {prime : Lane.MonsterPrimeLane} ->
  ArithmeticTrialectic prime ->
  Nat
C trial = Exponent.squareLevel (contribution trial)

roleMultiplicity :
  {prime : Lane.MonsterPrimeLane} ->
  ArithmeticTrialectic prime ->
  ModularContributionRole ->
  Nat
roleMultiplicity trial frickeComparison = A trial
roleMultiplicity trial levelPComparison = B trial
roleMultiplicity trial levelP2Comparison = C trial

------------------------------------------------------------------------
-- 2. Exact descent/aggregation theorem.
------------------------------------------------------------------------

arithmeticTrialecticReconstructsMonsterExponent :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : ArithmeticTrialectic prime) ->
  A trial + B trial + C trial
  ≡ Exponent.monsterOrderExponent prime
arithmeticTrialecticReconstructsMonsterExponent trial =
  Exponent.reconstructsExponent (contribution trial)

------------------------------------------------------------------------
-- 3. The multiplicity fibre is a disjoint union of the three source fibres.
--
-- This is the typed version of
--
--   Fin(A_p) ⊔ Fin(B_p) ⊔ Fin(C_p).
------------------------------------------------------------------------

ArithmeticMultiplicitySlot :
  {prime : Lane.MonsterPrimeLane} ->
  ArithmeticTrialectic prime ->
  Set
ArithmeticMultiplicitySlot trial =
  Fin (A trial) ⊎ (Fin (B trial) ⊎ Fin (C trial))

data SlotRole
  {prime : Lane.MonsterPrimeLane}
  (trial : ArithmeticTrialectic prime) :
  ArithmeticMultiplicitySlot trial ->
  ModularContributionRole ->
  Set where

  frickeSlotRole :
    (slot : Fin (A trial)) ->
    SlotRole trial (inj₁ slot) frickeComparison

  levelPSlotRole :
    (slot : Fin (B trial)) ->
    SlotRole trial (inj₂ (inj₁ slot)) levelPComparison

  levelP2SlotRole :
    (slot : Fin (C trial)) ->
    SlotRole trial (inj₂ (inj₂ slot)) levelP2Comparison

------------------------------------------------------------------------
-- 4. Concrete regression points from the attributed theorem reconstruction.
------------------------------------------------------------------------

p5Trialectic : ArithmeticTrialectic Lane.p5
p5Trialectic =
  canonicalArithmeticTrialectic Lane.p5 Exponent.p5AboveThree

p7Trialectic : ArithmeticTrialectic Lane.p7
p7Trialectic =
  canonicalArithmeticTrialectic Lane.p7 Exponent.p7AboveThree

p11Trialectic : ArithmeticTrialectic Lane.p11
p11Trialectic =
  canonicalArithmeticTrialectic Lane.p11 Exponent.p11AboveThree

p13Trialectic : ArithmeticTrialectic Lane.p13
p13Trialectic =
  canonicalArithmeticTrialectic Lane.p13 Exponent.p13AboveThree

p5Triple : A p5Trialectic ≡ 3
          × B p5Trialectic ≡ 5
          × C p5Trialectic ≡ 1
p5Triple = refl , refl , refl

p7Triple : A p7Trialectic ≡ 2
          × B p7Trialectic ≡ 4
          × C p7Trialectic ≡ 0
p7Triple = refl , refl , refl

p11Triple : A p11Trialectic ≡ 2
           × B p11Trialectic ≡ 0
           × C p11Trialectic ≡ 0
p11Triple = refl , refl , refl

p13Triple : A p13Trialectic ≡ 1
           × B p13Trialectic ≡ 2
           × C p13Trialectic ≡ 0
p13Triple = refl , refl , refl

p5ReconstructsNine :
  A p5Trialectic + B p5Trialectic + C p5Trialectic ≡ 9
p5ReconstructsNine = refl

p7ReconstructsSix :
  A p7Trialectic + B p7Trialectic + C p7Trialectic ≡ 6
p7ReconstructsSix = refl

------------------------------------------------------------------------
-- 5. Attribution and representation firewalls.
------------------------------------------------------------------------

arithmeticTrialecticClaimOrigin : Source.ClaimOrigin
arithmeticTrialecticClaimOrigin =
  Source.repositoryFormalReconstruction

data ArithmeticTripleIs369Hypercube : Set where
data ArithmeticTripleIsRelationalABCSubjectTriangle : Set where
data ThreeTermsCreateCechCocycle : Set where
data EqualSumCreatesSameCarrier : Set where

arithmeticTripleIsNotAutomatically369Hypercube :
  ArithmeticTripleIs369Hypercube -> ⊥
arithmeticTripleIsNotAutomatically369Hypercube ()

arithmeticTripleIsNotAutomaticallyRelationalABCSubjectTriangle :
  ArithmeticTripleIsRelationalABCSubjectTriangle -> ⊥
arithmeticTripleIsNotAutomaticallyRelationalABCSubjectTriangle ()

threeValuationTermsDoNotCreateCechCocycle :
  ThreeTermsCreateCechCocycle -> ⊥
threeValuationTermsDoNotCreateCechCocycle ()

equalSumDoesNotCreateSameCarrier :
  EqualSumCreatesSameCarrier -> ⊥
equalSumDoesNotCreateSameCarrier ()

record Optional369CoarseRepresentation
  (prime : Lane.MonsterPrimeLane)
  (trial : ArithmeticTrialectic prime)
  (Code : Set) : Set1 where
  field
    encodeRole : ModularContributionRole -> Code
    encodeSlot : ArithmeticMultiplicitySlot trial -> Code
    lossDeclared : Bool
    arithmeticRecoveryFromCodeProved : Bool

record OggMonstrousExponentTrialecticBoundary : Set where
  constructor ogg-monstrous-exponent-trialectic-boundary
  field
    pAboveThreeHasThreeAttributedValuationContributions : Bool
    threeContributionsReconstructMonsterExponent : Bool
    multiplicityFibreRetainsContributionProvenance : Bool
    arithmeticTripleDefinitionallyIs369Cube : Bool
    arithmeticTripleDefinitionallyIsRelationalSubjectTriangle : Bool
    threeTermsByThemselvesFormCechCocycle : Bool
    downstream369EncodingMustDeclareLoss : Bool
    smallCharacteristicResidualHandledHere : Bool

canonicalOggMonstrousExponentTrialecticBoundary :
  OggMonstrousExponentTrialecticBoundary
canonicalOggMonstrousExponentTrialecticBoundary =
  ogg-monstrous-exponent-trialectic-boundary
    true true true
    false false false
    true false
