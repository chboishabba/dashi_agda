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
open import Data.Rational.Base using (ℚ; 0ℚ)
import Data.Rational.Base as Rat
open import Data.Rational as R using (_/_)
open import Data.Integer using (+_)

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
-- A real exponent, positive mass theorem, normalised PMF/CDF and complex
-- Hurwitz continuation are further analytic/mass proof obligations.
power : Nat → Nat → Nat
power base zero = suc zero
power base (suc exponent) = base * power base exponent

zipfDenominator : Nat → Nat → Nat
zipfDenominator r exponent = power (suc r) exponent

mandelbrotDenominator : Nat → Nat → Nat → Nat
mandelbrotDenominator r shift exponent =
  power (suc r + shift) exponent

zipfIsZeroShift : ∀ r exponent →
  mandelbrotDenominator r zero exponent ≡ zipfDenominator r exponent
zipfIsZeroShift r exponent = refl

finiteMandelbrotTerm : Nat → Nat → Nat → ℚ
finiteMandelbrotTerm r shift exponent =
  (+ 1) R./ mandelbrotDenominator r shift exponent

sumFirst : (Nat → ℚ) → Nat → ℚ
sumFirst f zero = 0ℚ
sumFirst f (suc n) = Rat._+_ (sumFirst f n) (f n)

finiteHurwitz : Nat → Nat → Nat → ℚ
finiteHurwitz count shift exponent =
  sumFirst (λ r → finiteMandelbrotTerm r shift exponent) count

finiteZipfNormalizer : Nat → Nat → ℚ
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
