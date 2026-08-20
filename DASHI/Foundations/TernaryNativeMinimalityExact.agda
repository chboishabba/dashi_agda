module DASHI.Foundations.TernaryNativeMinimalityExact where

------------------------------------------------------------------------
-- SOURCE / METHOD CALIBRATION
--
-- Thomas M. Cover and Joy A. Thomas,
-- "Elements of Information Theory", second edition, Wiley, 2006.
-- DOI: 10.1002/047174882X.
--
-- The finite no-injection and round-trip proofs below are local DASHI proofs;
-- the citation is only standard coding/information-theory calibration.
--
-- DASHI CONTRIBUTION
--
-- Make exact the binary-versus-native-ternary distinction:
--
--   * {-1,0,+1} is the smallest local carrier with a nontrivial antipodal pair
--     and a distinct fixed centre;
--   * no one-bit observer can be injective on those three states;
--   * the common positive-only Boolean observer collapses -1 with 0;
--   * binary can retain the information by using two bits, but then it is a
--     simulation codec with an unused codeword and an explicit invariant.
--
-- Thus binary physical storage is possible without making the semantic
-- geometry Boolean: the exact choice is collapse or simulate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

negativeNotZero : SSP.sspNegOne ≢ SSP.sspZero
negativeNotZero ()

negativeNotPositive : SSP.sspNegOne ≢ SSP.sspPosOne
negativeNotPositive ()

zeroNotPositive : SSP.sspZero ≢ SSP.sspPosOne
zeroNotPositive ()

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

noOneBitInjection :
  (f : SSP.SSPTrit → Bool) →
  Injective f →
  ⊥
noOneBitInjection f injective
  with f SSP.sspNegOne | f SSP.sspZero | f SSP.sspPosOne
... | false | false | p = negativeNotZero (injective refl)
... | false | true  | false = negativeNotPositive (injective refl)
... | false | true  | true = zeroNotPositive (injective refl)
... | true  | false | false = zeroNotPositive (injective refl)
... | true  | false | true = negativeNotPositive (injective refl)
... | true  | true  | p = negativeNotZero (injective refl)

------------------------------------------------------------------------
-- The James-style positive-membership projection: `not true` is not inverse.
------------------------------------------------------------------------

positiveOnly : SSP.SSPTrit → Bool
positiveOnly SSP.sspNegOne = false
positiveOnly SSP.sspZero = false
positiveOnly SSP.sspPosOne = true

positiveOnlyCollapsesNegativeAndCentre :
  positiveOnly SSP.sspNegOne ≡ positiveOnly SSP.sspZero
positiveOnlyCollapsesNegativeAndCentre = refl

positiveOnlyFalseDoesNotIdentifyInverse :
  positiveOnly SSP.sspZero ≡ false
positiveOnlyFalseDoesNotIdentifyInverse = refl

record ExactPositiveOnlyReconstruction : Set where
  constructor exactPositiveOnlyReconstruction
  field
    decode : Bool → SSP.SSPTrit
    exact : (x : SSP.SSPTrit) → decode (positiveOnly x) ≡ x

open ExactPositiveOnlyReconstruction public

noExactPositiveOnlyReconstruction : ExactPositiveOnlyReconstruction → ⊥
noExactPositiveOnlyReconstruction reconstruction =
  negativeNotZero
    (trans
      (sym (exact reconstruction SSP.sspNegOne))
      (exact reconstruction SSP.sspZero))

------------------------------------------------------------------------
-- Lossless binary simulation: two bits rebuild the same three-state geometry.
------------------------------------------------------------------------

TwoBit : Set
TwoBit = Bool × Bool

encodeBinary : SSP.SSPTrit → TwoBit
encodeBinary SSP.sspNegOne = false , false
encodeBinary SSP.sspZero = false , true
encodeBinary SSP.sspPosOne = true , false

decodeBinary : TwoBit → SSP.SSPTrit
decodeBinary (false , false) = SSP.sspNegOne
decodeBinary (false , true) = SSP.sspZero
decodeBinary (true , false) = SSP.sspPosOne
-- Totalisation outside the semantic image; this codeword is proved unused.
decodeBinary (true , true) = SSP.sspZero

binarySimulationRoundTrip :
  (x : SSP.SSPTrit) → decodeBinary (encodeBinary x) ≡ x
binarySimulationRoundTrip SSP.sspNegOne = refl
binarySimulationRoundTrip SSP.sspZero = refl
binarySimulationRoundTrip SSP.sspPosOne = refl

unusedBinaryCodeword :
  (x : SSP.SSPTrit) → encodeBinary x ≡ (true , true) → ⊥
unusedBinaryCodeword SSP.sspNegOne ()
unusedBinaryCodeword SSP.sspZero ()
unusedBinaryCodeword SSP.sspPosOne ()

binaryAntipode : TwoBit → TwoBit
binaryAntipode (false , false) = true , false
binaryAntipode (false , true) = false , true
binaryAntipode (true , false) = false , false
binaryAntipode (true , true) = true , true

binarySimulationPreservesAntipode :
  (x : SSP.SSPTrit) →
  encodeBinary (Orbit.strictAntipode x) ≡ binaryAntipode (encodeBinary x)
binarySimulationPreservesAntipode SSP.sspNegOne = refl
binarySimulationPreservesAntipode SSP.sspZero = refl
binarySimulationPreservesAntipode SSP.sspPosOne = refl

binarySimulationPreservesFixedCentre :
  binaryAntipode (encodeBinary SSP.sspZero) ≡ encodeBinary SSP.sspZero
binarySimulationPreservesFixedCentre = refl

record TernaryNativeMinimalityBoundary : Set where
  constructor ternaryNativeMinimalityBoundary
  field
    oneBitCanInjectivelyEncodeStrictSignedCentre : Bool
    positiveOnlyFalseDeterminesStrictInverse : Bool
    exactBinarySimulationPossibleWithAuxiliaryState : Bool
    twoBitSimulationHasUnusedCodeword : Bool
    simulatedAntipodeRequiresExplicitCodecInvariant : Bool

canonicalTernaryNativeMinimalityBoundary : TernaryNativeMinimalityBoundary
canonicalTernaryNativeMinimalityBoundary =
  ternaryNativeMinimalityBoundary false false true true true
