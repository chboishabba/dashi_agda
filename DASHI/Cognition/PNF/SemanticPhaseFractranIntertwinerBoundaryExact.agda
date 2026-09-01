module DASHI.Cognition.PNF.SemanticPhaseFractranIntertwinerBoundaryExact where

-- Conditional authority boundary for the final semantic phase -> FRACTRAN
-- arithmetic weld discussed in the thread.
--
-- A relation-sheet phase bridge is not enough.  To interpret phase inversion
-- arithmetically one must additionally supply a transport whose reciprocal
-- operation intertwines the phase involution.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

------------------------------------------------------------------------
-- 1. Abstract phase/arithmetic intertwiner.
------------------------------------------------------------------------

record PhaseFractranIntertwiner
  (Phase Arithmetic : Set)
  (invertPhase : Phase → Phase)
  (reciprocal : Arithmetic → Arithmetic)
  : Set₁ where
  constructor phaseFractranIntertwiner
  field
    transport : Phase → Arithmetic
    inversionIntertwinesReciprocal :
      (phase : Phase) →
      transport (invertPhase phase) ≡ reciprocal (transport phase)

open PhaseFractranIntertwiner public

------------------------------------------------------------------------
-- 2. BIDI scope boundary.
------------------------------------------------------------------------

record PhaseFractranBoundary : Set where
  constructor phaseFractranBoundary
  field
    explicitIntertwinerRequired : Bool
    explicitIntertwinerRequiredIsTrue :
      explicitIntertwinerRequired ≡ true
    phaseCardinalityAloneDeterminesPrimeTransport : Bool
    phaseCardinalityAloneDeterminesPrimeTransportIsFalse :
      phaseCardinalityAloneDeterminesPrimeTransport ≡ false
    permutationSymmetryAloneDeterminesReciprocalTransport : Bool
    permutationSymmetryAloneDeterminesReciprocalTransportIsFalse :
      permutationSymmetryAloneDeterminesReciprocalTransport ≡ false

canonicalPhaseFractranBoundary : PhaseFractranBoundary
canonicalPhaseFractranBoundary =
  phaseFractranBoundary true refl false refl false refl
