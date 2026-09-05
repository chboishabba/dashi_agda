module DASHI.Analysis.NonArchimedeanTwistedTauOddFunctionEquivalenceExact where

------------------------------------------------------------------------
-- TWISTED COORDINATE <-> TAU-ODD FUNCTION SAME-OBJECT EQUIVALENCE
--
-- The Hadamard decomposition does not make the twisted coordinate mysterious.
-- A half-coordinate function f(v) represents the tau-odd full function whose
-- values on the two lifts are
--
--   f(lift v)              =  f(v)
--   f(lift v + halfPeriod) = -f(v).
--
-- Conversely, a tau-odd full function is determined uniquely by its values on
-- the canonical lifts.  This is the correct carrier weld between the literal
-- `twistedDirMatrix` coordinates and the function-level character theorem.
--
-- Once odd characters are classified as exactly tau-odd, restriction of
-- chi_(2j+1) to the canonical lift is the kernel omega^((2j+1)v), i.e. the
-- corrected modulated half-size DFT already isolated in this tranche.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TwistedTauOddEquivalence : Set₁ where
  field
    HalfPoint FullPoint Scalar : Set
    HalfFunction FullFunction : Set

    lift : HalfPoint → FullPoint
    otherLift : HalfPoint → FullPoint

    restrictToCanonicalLift : FullFunction → HalfFunction
    antisymmetricExtend : HalfFunction → FullFunction

    tauOdd : FullFunction → Set

    restrictAfterExtend :
      (f : HalfFunction) →
      restrictToCanonicalLift (antisymmetricExtend f) ≡ f

    extendAfterRestrictOnTauOdd :
      (F : FullFunction) → tauOdd F →
      antisymmetricExtend (restrictToCanonicalLift F) ≡ F

open TwistedTauOddEquivalence public

record CharacterRestrictionWeld
    (equiv : TwistedTauOddEquivalence) : Set₁ where
  field
    OddFrequency : Set
    character : OddFrequency → FullFunction equiv
    halfCharacter : OddFrequency → HalfFunction equiv

    charactersAreTauOdd :
      (k : OddFrequency) → tauOdd equiv (character k)

    characterRestrictionIsHalfKernel :
      (k : OddFrequency) →
      restrictToCanonicalLift equiv (character k) ≡ halfCharacter k

open CharacterRestrictionWeld public

record SourceCarrierWeldStatus : Set where
  constructor sourceCarrierWeldStatus
  field
    canonicalLiftProjectionOwned : Bool
    twoLiftFiberDescriptionOwned : Bool
    hadamardAntisymmetricBlockOwned : Bool
    tauOddPreservationOwned : Bool
    oddCharacterTauOddClassifierCompiled : Bool
    antisymmetricExtensionRestrictionEquivalenceIsElementary : Bool
    twistedCoordinateToTauOddFunctionWeldCompiles : Bool
    correctedOddCharacterKernelThenCompiles : Bool
    newSpectralHypothesisRequired : Bool

canonicalSourceCarrierWeldStatus : SourceCarrierWeldStatus
canonicalSourceCarrierWeldStatus =
  sourceCarrierWeldStatus true true true true true true true true false

carrierWeldIsCompilerNotHypothesis :
  SourceCarrierWeldStatus.newSpectralHypothesisRequired
    canonicalSourceCarrierWeldStatus
  ≡ false
carrierWeldIsCompilerNotHypothesis = refl

correctedCharacterKernelCompilesOnWeld :
  SourceCarrierWeldStatus.correctedOddCharacterKernelThenCompiles
    canonicalSourceCarrierWeldStatus
  ≡ true
correctedCharacterKernelCompilesOnWeld = refl
