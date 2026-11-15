module DASHI.Moonshine.Monster3BSchrodingerFormalTraceBridgeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BSchrodingerFormalTraceBridgeExact as Target

open Target

traceTyped : formalDeltaBasisTraceTyped canonicalBoundary ≡ true
traceTyped = refl

orthogonalityAvailable : modulationOrthogonalityAvailable canonicalBoundary ≡ true
orthogonalityAvailable = refl

translationLeafOpen : nonzeroTranslationDiagonalVanishingPaid canonicalBoundary ≡ false
translationLeafOpen = refl

factorizationLeafOpen : diagonalTraceFactorizationPaid canonicalBoundary ≡ false
factorizationLeafOpen = refl

fullTraceStillOpen : fullLiteralCharacterKernelPaid canonicalBoundary ≡ false
fullTraceStillOpen = refl
