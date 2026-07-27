module DASHI.Physics.Closure.NSTriadKNTriadDirectionAlignmentProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- Venue/year: Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
-- Uses: motivation for retaining relative vorticity-direction information
-- across interacting locations.
-- Relationship: the exact finite Fourier Gram defect below is only a
-- polarization surrogate.  It is not the Fourier transform of the normalized
-- physical-space direction field and is not attributed to Constantin--
-- Fefferman as a theorem.
--
-- Authors: DASHI repository contributors.
-- Title: "Triad direction-alignment carrier and translation-invariant
-- quadratic no-go".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original structural reduction.
-- Relationship: proves at the programme level that a translation-invariant
-- quadratic functional is Fourier-diagonal, so genuine cross-leg direction
-- coherence cannot be encoded by a mode-local quadratic symbol alone.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

record FourierPolarizationGramDiagnostic : Set where
  constructor diagnostic
  field
    witnessGramDefectSum : Nat
    witnessWeightedTransferNumerator : Int.ℤ
    witnessWeightedTransferDenominator : Nat
    optimizedSupportGramDefectSum : Nat
    optimizedSupportWeightedTransferNumerator : Int.ℤ
    optimizedSupportWeightedTransferDenominator : Nat

open FourierPolarizationGramDiagnostic public

exactPolarizationDiagnostic : FourierPolarizationGramDiagnostic
exactPolarizationDiagnostic =
  diagnostic
    691128
    (+ 31302)
    143
    28906945080
    (Int.-_ (+ 17822768857756493))
    213942878310

witnessPolarizationSignalNonzero : 0 < 31302
witnessPolarizationSignalNonzero = s≤s z≤n

optimizedSupportPolarizationSignalNonzero : 0 < 17822768857756493
optimizedSupportPolarizationSignalNonzero = s≤s z≤n

record TranslationInvariantQuadraticKernel
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    Kernel : Mode → Mode → Set s
    Character : Mode → Set s
    TranslationInvariant : Set s
    distinctCharactersSeparateModes : Set s

    diagonalKernelOnly :
      TranslationInvariant →
      distinctCharactersSeparateModes →
      Set s

open TranslationInvariantQuadraticKernel public

record TriadDirectionAlignmentCandidate
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    subtract multiply : Scalar → Scalar → Scalar
    vorticityCoefficient : Mode → Vector
    squaredNorm : Vector → Scalar
    hermitianPairingMagnitudeSquared : Vector → Vector → Scalar
    gramDefect : Mode → Mode → Scalar
    gramDefectDefinition :
      ∀ p q →
      gramDefect p q
      ≡ subtract
          (multiply
            (squaredNorm (vorticityCoefficient p))
            (squaredNorm (vorticityCoefficient q)))
          (hermitianPairingMagnitudeSquared
            (vorticityCoefficient p)
            (vorticityCoefficient q))

    Triad : Set
    triadLeft triadRight triadOutput : Triad → Mode
    primitiveSignedTransfer : Triad → Scalar
    directionWeightedTransfer : Triad → Scalar

    gramDefectNonnegative : ∀ p q → Set s
    directionWeightedTransferLiteral : ∀ triad → Set s

    Functional : Set s
    functionalDerivative : Functional → Triad → Scalar
    translationEquivariantFunctional : Functional → Set s
    directionKernelIntegrableAsFunctional : Functional → Set s
    degreeAccountingClosed : Functional → Set s

open TriadDirectionAlignmentCandidate public

translationInvariantQuadraticCanEncodeCrossModeDirection : Bool
translationInvariantQuadraticCanEncodeCrossModeDirection = false

translationInvariantQuadraticCanEncodeCrossModeDirectionIsFalse :
  translationInvariantQuadraticCanEncodeCrossModeDirection ≡ false
translationInvariantQuadraticCanEncodeCrossModeDirectionIsFalse = refl

fourierGramDiagnosticIsConstantinFeffermanDirection : Bool
fourierGramDiagnosticIsConstantinFeffermanDirection = false

fourierGramDiagnosticIsConstantinFeffermanDirectionIsFalse :
  fourierGramDiagnosticIsConstantinFeffermanDirection ≡ false
fourierGramDiagnosticIsConstantinFeffermanDirectionIsFalse = refl

triadDirectionSignalRepresented : Bool
triadDirectionSignalRepresented = true

triadDirectionSignalRepresentedIsTrue :
  triadDirectionSignalRepresented ≡ true
triadDirectionSignalRepresentedIsTrue = refl

triadDirectionFunctionalClosed : Bool
triadDirectionFunctionalClosed = false

triadDirectionFunctionalClosedIsFalse :
  triadDirectionFunctionalClosed ≡ false
triadDirectionFunctionalClosedIsFalse = refl
