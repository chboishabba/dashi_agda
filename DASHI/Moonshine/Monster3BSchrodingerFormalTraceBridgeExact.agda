module DASHI.Moonshine.Monster3BSchrodingerFormalTraceBridgeExact where

------------------------------------------------------------------------
-- LITERAL SCHRODINGER CHARACTER: KERNEL-FACING TRACE BRIDGE
--
-- The executable all-coordinate audit already computes the character exactly.
-- The Agda source also already proves the six-coordinate additive-character
-- orthogonality.  What was still implicit is the bridge from the actual
-- delta-basis action to that factorized finite Fourier sum.
--
-- This owner defines the literal diagonal coefficient and finite delta-basis
-- trace on the SAME Schrodinger action.  It then types the two exact algebraic
-- leaves required to compile the canonical four-value character:
--
--   A. if the translation coordinate is nonzero, every delta-basis diagonal
--      coefficient vanishes (no translated basis point is fixed);
--   B. if translation is zero, the recursive 729-term diagonal trace factors
--      as the already-proved six-coordinate modulation character, times the
--      central phase.
--
-- Once A and B are inhabited, the existing additive-character orthogonality
-- supplies the noncentral modulation vanishing and the central values.  The
-- executable receipt remains an independent regression, not proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerBooleanDeltaExact as Delta
import DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact as Action
import DASHI.Moonshine.Monster3BFiniteSchrodingerHilbertLiftExact as Hilbert
import DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact as Orthogonality
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Executable

------------------------------------------------------------------------
-- 1. Literal delta-basis diagonal coefficient and trace.
------------------------------------------------------------------------

diagonalCoefficient : H.Heisenberg6 → G.X6 → C3.Cyclotomic3
diagonalCoefficient g y = Action.heisenbergAction g (Delta.booleanDelta y) y

literalDeltaBasisTrace : H.Heisenberg6 → C3.Cyclotomic3
literalDeltaBasisTrace g = Hilbert.sumX6 (diagonalCoefficient g)

------------------------------------------------------------------------
-- 2. Exact remaining algebraic payments.
------------------------------------------------------------------------

record NonzeroTranslationDiagonalVanishing : Set where
  field
    TranslationNonzero : G.X6 → Set
    everyDiagonalCoefficientVanishes :
      (g : H.Heisenberg6) →
      TranslationNonzero (H.translationPart (H.quotient g)) →
      (y : G.X6) → diagonalCoefficient g y ≡ C3.zero
open NonzeroTranslationDiagonalVanishing public

record ZeroTranslationTraceFactorization : Set where
  field
    translationIsZero : H.Heisenberg6 → Set
    traceFactorization :
      (g : H.Heisenberg6) →
      translationIsZero g →
      literalDeltaBasisTrace g
      ≡ C3.multiply
          (V.phase (H.centralPhase g))
          (Orthogonality.factorizedModulationCharacter
            (H.modulationPart (H.quotient g)))
open ZeroTranslationTraceFactorization public

------------------------------------------------------------------------
-- 3. Terminal theorem compiler target.
------------------------------------------------------------------------

record LiteralCharacterKernelPayment : Set where
  field
    translationVanishing : NonzeroTranslationDiagonalVanishing
    zeroTranslationFactorization : ZeroTranslationTraceFactorization

    canonicalFourClassCharacter :
      (g : H.Heisenberg6) →
      Set

    canonicalFourClassCharacter_paid :
      (g : H.Heisenberg6) → canonicalFourClassCharacter g

------------------------------------------------------------------------
-- 4. Current max-cut boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    formalDeltaBasisTraceTyped : Bool
    literalActionConsumed : Bool
    literalDeltaBasisConsumed : Bool
    finite729SumConsumed : Bool
    modulationOrthogonalityAvailable : Bool
    exhaustiveExecutableCrossCheckAvailable : Bool

    nonzeroTranslationDiagonalVanishingPaid : Bool
    diagonalTraceFactorizationPaid : Bool
    fullLiteralCharacterKernelPaid : Bool
    executableReceiptCountsAsKernelProof : Bool

    firstOpenTraceLeaf : String
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true true
  false false false false
  "Prove translated delta basis points have zero diagonal coefficient for every nonzero translation, then prove the zero-translation 729-term recursive trace factors into the six one-coordinate additive-character sums already owned by the orthogonality module."
