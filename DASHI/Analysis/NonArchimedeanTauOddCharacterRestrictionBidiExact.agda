module DASHI.Analysis.NonArchimedeanTauOddCharacterRestrictionBidiExact where

------------------------------------------------------------------------
-- TAU-ODD CHARACTER RESTRICTION FRONTIER
--
-- Source `DirectedSpectrum.lean` already proves:
--   * D_n preserves the tau-odd subspace;
--   * D_n chi_k = (1 + zeta^(-k)) chi_(3k).
--
-- Paper prose additionally identifies the tau-odd subspace with odd Fourier
-- frequencies.  The located Lean source does not expose that iff as a theorem
-- type.  This owner isolates precisely the missing semantic restriction weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)


data TauOddCharacterObligation : Set where
  proveOddFrequencyImpliesTauOdd : TauOddCharacterObligation
  proveTauOddCharacterImpliesOddFrequency : TauOddCharacterObligation
  identifyTwistedBlockCoordinatesWithTauOddFunctions : TauOddCharacterObligation
  restrictCharacterActionToOddFrequencies : TauOddCharacterObligation
  rebuildCharacterActionFormula : TauOddCharacterObligation
  rebuildTauOddPreservation : TauOddCharacterObligation


data TauOddDisposition : Set where
  live : TauOddDisposition
  downstream : TauOddDisposition
  pruned : TauOddDisposition

obligationDisposition : TauOddCharacterObligation → TauOddDisposition
obligationDisposition proveOddFrequencyImpliesTauOdd = live
obligationDisposition proveTauOddCharacterImpliesOddFrequency = live
obligationDisposition identifyTwistedBlockCoordinatesWithTauOddFunctions = live
obligationDisposition restrictCharacterActionToOddFrequencies = downstream
obligationDisposition rebuildCharacterActionFormula = pruned
obligationDisposition rebuildTauOddPreservation = pruned

record TauOddCharacterRestriction : Set₁ where
  field
    Frequency : Set
    Function : Set

    oddFrequency : Frequency → Set
    tauOdd : Function → Set
    character : Frequency → Function

    oddImpliesTauOdd :
      (k : Frequency) → oddFrequency k → tauOdd (character k)

    tauOddCharacterImpliesOdd :
      (k : Frequency) → tauOdd (character k) → oddFrequency k

open TauOddCharacterRestriction public

record TwistedCoordinateRestriction
    (restriction : TauOddCharacterRestriction) : Set₁ where
  field
    TwistedCoordinate : Set
    coordinateToFrequency : TwistedCoordinate → Frequency restriction
    frequencyToCoordinate : Frequency restriction → TwistedCoordinate

    coordinateRoundTrip :
      (x : TwistedCoordinate) →
      frequencyToCoordinate (coordinateToFrequency x) ≡ x

    frequencyRoundTrip :
      (k : Frequency restriction) →
      coordinateToFrequency (frequencyToCoordinate k) ≡ k

    coordinateLandsInOddFrequency :
      (x : TwistedCoordinate) →
      oddFrequency restriction (coordinateToFrequency x)

open TwistedCoordinateRestriction public

record SourceTauOddStatus : Set where
  constructor sourceTauOddStatus
  field
    DnPreservesTauOddOwned : Bool
    functionLevelCharacterActionOwned : Bool
    oddFrequencyIffTauOddCharacterOwnedInLocatedLeanType : Bool
    concreteTwistedCoordinateToTauOddCharacterWeldOwned : Bool

canonicalSourceTauOddStatus : SourceTauOddStatus
canonicalSourceTauOddStatus = sourceTauOddStatus true true false false

highestAlphaTauOddPath : List TauOddCharacterObligation
highestAlphaTauOddPath =
  proveOddFrequencyImpliesTauOdd ∷
  proveTauOddCharacterImpliesOddFrequency ∷
  identifyTwistedBlockCoordinatesWithTauOddFunctions ∷
  restrictCharacterActionToOddFrequencies ∷
  []

sourceCharacterFormulaMustNotBeRebuilt :
  obligationDisposition rebuildCharacterActionFormula ≡ pruned
sourceCharacterFormulaMustNotBeRebuilt = refl
