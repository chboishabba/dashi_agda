module DASHI.Statistics.ZipfFamilyFiniteExact where

-- 27 separately typed subjects. Definitions and finite proofs only; no
-- empirical universality, analytic zeta continuation or NSE theorem.
-- Historical authors retain their priority. Source-written formal cut:
-- Johl Brown with OpenAI ChatGPT assistance (2026-10-27).
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base as Nat using (NonZero; _^_)
import Data.Nat.Properties as NatP
-- Reuse the canonical exact finite numerator/denominator carrier.
-- We do not invoke rational division on a symbolic natural denominator
-- until the separate nonzero proof obligation has been discharged.
import DASHI.Core.FiniteUniformProbabilityNormalizationExact as Exact

data Authority : Set where
  mathematicalIdentity : Authority
  modelFamily : Authority
  empiricalDiagnostic : Authority
  unverifiedHypothesis : Authority
  dataRepresentation : Authority
  historicalProvenance : Authority

data Family : Set where
  zipf : Family
  onePercentParticipation : Family
  benford : Family
  bradford : Family
  brevity : Family
  demographicGravitation : Family
  wordList : Family
  gibrat : Family
  hapax : Family
  heaps : Family
  hilberg : Family
  historicalRecurrence : Family
  kingEffect : Family
  longTail : Family
  lorenz : Family
  lotka : Family
  menzerathAltmann : Family
  paretoDistribution : Family
  paretoPrinciple : Family
  priceSquareRoot : Family
  leastEffort : Family
  rankSize : Family
  stiglerEponymy : Family
  letterFrequency : Family
  mostCommonEnglish : Family
  zipfMandelbrot : Family
  hurwitzZeta : Family

authority : Family → Authority
authority zipf = modelFamily
authority onePercentParticipation = unverifiedHypothesis
authority benford = modelFamily
authority bradford = empiricalDiagnostic
authority brevity = empiricalDiagnostic
authority demographicGravitation = modelFamily
authority wordList = dataRepresentation
authority gibrat = unverifiedHypothesis
authority hapax = mathematicalIdentity
authority heaps = empiricalDiagnostic
authority hilberg = unverifiedHypothesis
authority historicalRecurrence = unverifiedHypothesis
authority kingEffect = empiricalDiagnostic
authority longTail = dataRepresentation
authority lorenz = mathematicalIdentity
authority lotka = empiricalDiagnostic
authority menzerathAltmann = empiricalDiagnostic
authority paretoDistribution = modelFamily
authority paretoPrinciple = empiricalDiagnostic
authority priceSquareRoot = unverifiedHypothesis
authority leastEffort = unverifiedHypothesis
authority rankSize = dataRepresentation
authority stiglerEponymy = historicalProvenance
authority letterFrequency = dataRepresentation
authority mostCommonEnglish = dataRepresentation
authority zipfMandelbrot = modelFamily
authority hurwitzZeta = mathematicalIdentity

record AttributedObservation : Set where
  constructor attributedObservation
  field
    family : Family
    sourceRoot : String
    originalAuthorReference : String
    sampleOrCarrierIdentity : String
    claimText : String
    independentlyReplicated : Bool
    proofKernelVerified : Bool

-- Finite rational subfamily. The rank index r=0 denotes rank one.
-- A real exponent, a proof of symbolic denominator positivity,
-- an equality-normalized PMF/CDF, and complex Hurwitz continuation
-- are separate proof obligations. The finite fraction owner is reused.
power : Nat → Nat → Nat
power base zero = suc zero
power base (suc exponent) = base * power base exponent

-- The private power agrees definitionally with the standard-library
-- natural exponentiation. NonZero is the *actual* denominator constraint,
-- not a Boolean flag, synthetic receipt, or assumed rational division.
powerMatchesNat : ∀ base exponent →
  power base exponent ≡ Nat._^_ base exponent
powerMatchesNat base exponent = refl

zipfDenominator : Nat → Nat → Nat
zipfDenominator r exponent = power (suc r) exponent

mandelbrotDenominator : Nat → Nat → Nat → Nat
mandelbrotDenominator r shift exponent =
  power (suc r + shift) exponent

-- Nonzero-denominator witness for each source-ranked positive term.
-- Positive base is definitionally suc (r + shift), so the library's
-- actual exponentiation theorem applies.
mandelbrotDenominatorNonZero : ∀ r shift exponent →
  Nat.NonZero (mandelbrotDenominator r shift exponent)
mandelbrotDenominatorNonZero r shift exponent =
  NatP.m^n≢0 (suc r + shift) exponent

zipfIsZeroShift : ∀ r exponent →
  mandelbrotDenominator r zero exponent ≡ zipfDenominator r exponent
zipfIsZeroShift r exponent = refl

-- Fractions here are unreduced exact numerator/denominator pairs.
-- Every listed term's mathematical denominator is a positive power of
-- suc r + shift, but this module does NOT pretend to have built the
-- rational NonZero typeclass proof. This reuse avoids a duplicate carrier.
Fraction = Exact.FiniteFraction

zeroFraction : Fraction
zeroFraction = Exact.finiteFraction zero (suc zero)

oneFraction : Fraction
oneFraction = Exact.finiteFraction (suc zero) (suc zero)

addFraction : Fraction → Fraction → Fraction
addFraction a b =
  Exact.finiteFraction
    (Exact.numerator a * Exact.denominator b
      + Exact.numerator b * Exact.denominator a)
    (Exact.denominator a * Exact.denominator b)

finiteMandelbrotTerm : Nat → Nat → Nat → Fraction
finiteMandelbrotTerm r shift exponent =
  Exact.finiteFraction (suc zero)
    (mandelbrotDenominator r shift exponent)

sumFirst : (Nat → Fraction) → Nat → Fraction
sumFirst f zero = zeroFraction
sumFirst f (suc n) = addFraction (sumFirst f n) (f n)

-- All exact finite-fraction sums have nonzero product denominators.
-- This lemma is a constructive precondition for later ℚ interpretation;
-- it does not by itself prove PMF normalization, nonnegative numerators,
-- analytic continuation, or any empirical Zipf law.
sumFirstDenominatorNonZero :
  (f : Nat → Fraction) (count : Nat) →
  ((r : Nat) → Nat.NonZero (Exact.denominator (f r))) →
  Nat.NonZero (Exact.denominator (sumFirst f count))
sumFirstDenominatorNonZero f zero each = _
sumFirstDenominatorNonZero f (suc n) each =
  NatP.m*n≢0
    (Exact.denominator (sumFirst f n))
    (Exact.denominator (f n))
    {{sumFirstDenominatorNonZero f n each}} {{each n}}

finiteHurwitz : Nat → Nat → Nat → Fraction
finiteHurwitz count shift exponent =
  sumFirst (λ r → finiteMandelbrotTerm r shift exponent) count

finiteHurwitzDenominatorNonZero : ∀ count shift exponent →
  Nat.NonZero (Exact.denominator (finiteHurwitz count shift exponent))
finiteHurwitzDenominatorNonZero count shift exponent =
  sumFirstDenominatorNonZero
    (λ r → finiteMandelbrotTerm r shift exponent) count
    (λ r → mandelbrotDenominatorNonZero r shift exponent)

finiteZipfNormalizer : Nat → Nat → Fraction
finiteZipfNormalizer count exponent = finiteHurwitz count zero exponent

finiteZeroShiftIsZipf : ∀ count exponent →
  sumFirst (λ r → finiteMandelbrotTerm r zero exponent) count
  ≡ finiteZipfNormalizer count exponent
finiteZeroShiftIsZipf count exponent = refl


countIf : ∀ {A : Set} → (A → Bool) → List A → Nat
countIf predicate [] = zero
countIf predicate (x ∷ xs) with predicate x
... | true = suc (countIf predicate xs)
... | false = countIf predicate xs

infixr 5 _+++_
_+++_ : ∀ {A : Set} → List A → List A → List A
[] +++ ys = ys
(x ∷ xs) +++ ys = x ∷ (xs +++ ys)

countAppend : ∀ {A : Set} (predicate : A → Bool) xs ys →
  countIf predicate (xs +++ ys) ≡ countIf predicate xs + countIf predicate ys
countAppend predicate [] ys = refl
countAppend predicate (x ∷ xs) ys with predicate x
... | true rewrite countAppend predicate xs ys = refl
... | false = countAppend predicate xs ys

Hapax : ∀ {A : Set} → (A → A → Bool) → A → List A → Set
Hapax matches token corpus = countIf (matches token) corpus ≡ suc zero

data ⊥ : Set where

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl yz = yz

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

sameRank : Bool → Nat
sameRank true = suc (suc zero)
sameRank false = suc (suc zero)

phaseOrAttribution : Bool → Bool
phaseOrAttribution phase = phase

ranksCollide : sameRank true ≡ sameRank false
ranksCollide = refl

rankCannotRecoverPhase :
  (infer : Nat → Bool) →
  ((b : Bool) → infer (sameRank b) ≡ phaseOrAttribution b) → ⊥
rankCannotRecoverPhase infer recovery =
  trueNotFalse
    (transEq (symEq (recovery true)) (recovery false))

allActiveTwo : countIf (λ b → b) (true ∷ true ∷ []) ≡ suc (suc zero)
allActiveTwo = refl

noneActiveTwo : countIf (λ b → b) (false ∷ false ∷ []) ≡ zero
noneActiveTwo = refl

onePercentIsNotAutomatic : authority onePercentParticipation ≡ unverifiedHypothesis
onePercentIsNotAutomatic = refl

stiglerIsProvenanceNotUniversalTheorem : authority stiglerEponymy ≡ historicalProvenance
stiglerIsProvenanceNotUniversalTheorem = refl

hilbergRequiresSeparateEntropyTheorem : authority hilberg ≡ unverifiedHypothesis
hilbergRequiresSeparateEntropyTheorem = refl
