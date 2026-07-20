module DASHI.Algebra.TriadicDepthOneCharacters where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (neg; zer; pos; []; _∷_)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicFiniteIrrep as Irrep

open Arithmetic.TriadicArithmeticLawReceipt
  using (associativity; commutative)
open Irrep.PhaseRing
  using
    ( Phase; oneᵖ; _∙ᵖ_; conjugateᵖ
    ; oneMultiplyOne; phaseAssociative
    )
open Irrep.AdditiveCharacter
  using (frequency; evaluate; evaluateZero; additiveLaw)

------------------------------------------------------------------------
-- The three residues modulo 3.

rNeg rZero rPos : Q.Residue3Pow Q.one
rNeg = neg ∷ []
rZero = zer ∷ []
rPos = pos ∷ []

------------------------------------------------------------------------
-- Exact finite-group laws at depth one.

commutativeDepthOne :
  (x y : Q.Residue3Pow Q.one) →
  Arithmetic.addResidue x y ≡ Arithmetic.addResidue y x
commutativeDepthOne (neg ∷ []) (neg ∷ []) = refl
commutativeDepthOne (neg ∷ []) (zer ∷ []) = refl
commutativeDepthOne (neg ∷ []) (pos ∷ []) = refl
commutativeDepthOne (zer ∷ []) (neg ∷ []) = refl
commutativeDepthOne (zer ∷ []) (zer ∷ []) = refl
commutativeDepthOne (zer ∷ []) (pos ∷ []) = refl
commutativeDepthOne (pos ∷ []) (neg ∷ []) = refl
commutativeDepthOne (pos ∷ []) (zer ∷ []) = refl
commutativeDepthOne (pos ∷ []) (pos ∷ []) = refl

associativeDepthOne :
  (x y z : Q.Residue3Pow Q.one) →
  Arithmetic.addResidue (Arithmetic.addResidue x y) z
  ≡ Arithmetic.addResidue x (Arithmetic.addResidue y z)
associativeDepthOne (neg ∷ []) (neg ∷ []) (neg ∷ []) = refl
associativeDepthOne (neg ∷ []) (neg ∷ []) (zer ∷ []) = refl
associativeDepthOne (neg ∷ []) (neg ∷ []) (pos ∷ []) = refl
associativeDepthOne (neg ∷ []) (zer ∷ []) (neg ∷ []) = refl
associativeDepthOne (neg ∷ []) (zer ∷ []) (zer ∷ []) = refl
associativeDepthOne (neg ∷ []) (zer ∷ []) (pos ∷ []) = refl
associativeDepthOne (neg ∷ []) (pos ∷ []) (neg ∷ []) = refl
associativeDepthOne (neg ∷ []) (pos ∷ []) (zer ∷ []) = refl
associativeDepthOne (neg ∷ []) (pos ∷ []) (pos ∷ []) = refl
associativeDepthOne (zer ∷ []) (neg ∷ []) (neg ∷ []) = refl
associativeDepthOne (zer ∷ []) (neg ∷ []) (zer ∷ []) = refl
associativeDepthOne (zer ∷ []) (neg ∷ []) (pos ∷ []) = refl
associativeDepthOne (zer ∷ []) (zer ∷ []) (neg ∷ []) = refl
associativeDepthOne (zer ∷ []) (zer ∷ []) (zer ∷ []) = refl
associativeDepthOne (zer ∷ []) (zer ∷ []) (pos ∷ []) = refl
associativeDepthOne (zer ∷ []) (pos ∷ []) (neg ∷ []) = refl
associativeDepthOne (zer ∷ []) (pos ∷ []) (zer ∷ []) = refl
associativeDepthOne (zer ∷ []) (pos ∷ []) (pos ∷ []) = refl
associativeDepthOne (pos ∷ []) (neg ∷ []) (neg ∷ []) = refl
associativeDepthOne (pos ∷ []) (neg ∷ []) (zer ∷ []) = refl
associativeDepthOne (pos ∷ []) (neg ∷ []) (pos ∷ []) = refl
associativeDepthOne (pos ∷ []) (zer ∷ []) (neg ∷ []) = refl
associativeDepthOne (pos ∷ []) (zer ∷ []) (zer ∷ []) = refl
associativeDepthOne (pos ∷ []) (zer ∷ []) (pos ∷ []) = refl
associativeDepthOne (pos ∷ []) (pos ∷ []) (neg ∷ []) = refl
associativeDepthOne (pos ∷ []) (pos ∷ []) (zer ∷ []) = refl
associativeDepthOne (pos ∷ []) (pos ∷ []) (pos ∷ []) = refl

depthOneArithmeticLaws : Arithmetic.TriadicArithmeticLawReceipt Q.one
depthOneArithmeticLaws =
  record
    { associativity = associativeDepthOne
    ; commutative = commutativeDepthOne
    }

depthOneAdditiveGroup : Irrep.FiniteAdditiveGroup Q.one
depthOneAdditiveGroup =
  Arithmetic.finiteAdditiveGroup Q.one depthOneArithmeticLaws

------------------------------------------------------------------------
-- Symbolic third roots of unity.

data C3Phase : Set where
  phase0 : C3Phase
  phase1 : C3Phase
  phase2 : C3Phase

multiplyPhase : C3Phase → C3Phase → C3Phase
multiplyPhase phase0 b = b
multiplyPhase phase1 phase0 = phase1
multiplyPhase phase1 phase1 = phase2
multiplyPhase phase1 phase2 = phase0
multiplyPhase phase2 phase0 = phase2
multiplyPhase phase2 phase1 = phase0
multiplyPhase phase2 phase2 = phase1

conjugatePhase : C3Phase → C3Phase
conjugatePhase phase0 = phase0
conjugatePhase phase1 = phase2
conjugatePhase phase2 = phase1

c3PhaseAssociative :
  (a b c : C3Phase) →
  multiplyPhase (multiplyPhase a b) c
  ≡ multiplyPhase a (multiplyPhase b c)
c3PhaseAssociative phase0 b c = refl
c3PhaseAssociative phase1 phase0 c = refl
c3PhaseAssociative phase1 phase1 phase0 = refl
c3PhaseAssociative phase1 phase1 phase1 = refl
c3PhaseAssociative phase1 phase1 phase2 = refl
c3PhaseAssociative phase1 phase2 phase0 = refl
c3PhaseAssociative phase1 phase2 phase1 = refl
c3PhaseAssociative phase1 phase2 phase2 = refl
c3PhaseAssociative phase2 phase0 c = refl
c3PhaseAssociative phase2 phase1 phase0 = refl
c3PhaseAssociative phase2 phase1 phase1 = refl
c3PhaseAssociative phase2 phase1 phase2 = refl
c3PhaseAssociative phase2 phase2 phase0 = refl
c3PhaseAssociative phase2 phase2 phase1 = refl
c3PhaseAssociative phase2 phase2 phase2 = refl

c3PhaseRing : Irrep.PhaseRing
c3PhaseRing =
  record
    { Phase = C3Phase
    ; oneᵖ = phase0
    ; _∙ᵖ_ = multiplyPhase
    ; conjugateᵖ = conjugatePhase
    ; oneMultiplyOne = refl
    ; phaseAssociative = c3PhaseAssociative
    }

------------------------------------------------------------------------
-- The exact three-by-three character table.

characterValue :
  Q.Residue3Pow Q.one →
  Q.Residue3Pow Q.one →
  C3Phase
characterValue (zer ∷ []) x = phase0
characterValue (pos ∷ []) (neg ∷ []) = phase2
characterValue (pos ∷ []) (zer ∷ []) = phase0
characterValue (pos ∷ []) (pos ∷ []) = phase1
characterValue (neg ∷ []) (neg ∷ []) = phase1
characterValue (neg ∷ []) (zer ∷ []) = phase0
characterValue (neg ∷ []) (pos ∷ []) = phase2

characterAtZero :
  (m : Q.Residue3Pow Q.one) →
  characterValue m rZero ≡ phase0
characterAtZero (neg ∷ []) = refl
characterAtZero (zer ∷ []) = refl
characterAtZero (pos ∷ []) = refl

characterAdditive :
  (m x y : Q.Residue3Pow Q.one) →
  characterValue m (Arithmetic.addResidue x y)
  ≡ multiplyPhase (characterValue m x) (characterValue m y)
characterAdditive (neg ∷ []) (neg ∷ []) (neg ∷ []) = refl
characterAdditive (neg ∷ []) (neg ∷ []) (zer ∷ []) = refl
characterAdditive (neg ∷ []) (neg ∷ []) (pos ∷ []) = refl
characterAdditive (neg ∷ []) (zer ∷ []) (neg ∷ []) = refl
characterAdditive (neg ∷ []) (zer ∷ []) (zer ∷ []) = refl
characterAdditive (neg ∷ []) (zer ∷ []) (pos ∷ []) = refl
characterAdditive (neg ∷ []) (pos ∷ []) (neg ∷ []) = refl
characterAdditive (neg ∷ []) (pos ∷ []) (zer ∷ []) = refl
characterAdditive (neg ∷ []) (pos ∷ []) (pos ∷ []) = refl
characterAdditive (zer ∷ []) x y = refl
characterAdditive (pos ∷ []) (neg ∷ []) (neg ∷ []) = refl
characterAdditive (pos ∷ []) (neg ∷ []) (zer ∷ []) = refl
characterAdditive (pos ∷ []) (neg ∷ []) (pos ∷ []) = refl
characterAdditive (pos ∷ []) (zer ∷ []) (neg ∷ []) = refl
characterAdditive (pos ∷ []) (zer ∷ []) (zer ∷ []) = refl
characterAdditive (pos ∷ []) (zer ∷ []) (pos ∷ []) = refl
characterAdditive (pos ∷ []) (pos ∷ []) (neg ∷ []) = refl
characterAdditive (pos ∷ []) (pos ∷ []) (zer ∷ []) = refl
characterAdditive (pos ∷ []) (pos ∷ []) (pos ∷ []) = refl

depthOneCharacter :
  (m : Q.Residue3Pow Q.one) →
  Irrep.AdditiveCharacter depthOneAdditiveGroup c3PhaseRing
depthOneCharacter m =
  record
    { frequency = m
    ; evaluate = characterValue m
    ; evaluateZero = characterAtZero m
    ; additiveLaw = characterAdditive m
    }

characterFrequencyExact :
  (m : Q.Residue3Pow Q.one) →
  frequency (depthOneCharacter m) ≡ m
characterFrequencyExact m = refl

------------------------------------------------------------------------
-- Explicit table rows in residue order (-1, 0, +1).

record CharacterRow : Set where
  constructor character-row
  field
    atNeg : C3Phase
    atZero : C3Phase
    atPos : C3Phase

open CharacterRow public

characterRow : Q.Residue3Pow Q.one → CharacterRow
characterRow m =
  character-row
    (characterValue m rNeg)
    (characterValue m rZero)
    (characterValue m rPos)

trivialRowExact :
  characterRow rZero ≡ character-row phase0 phase0 phase0
trivialRowExact = refl

positiveRowExact :
  characterRow rPos ≡ character-row phase2 phase0 phase1
positiveRowExact = refl

negativeRowExact :
  characterRow rNeg ≡ character-row phase1 phase0 phase2
negativeRowExact = refl

------------------------------------------------------------------------
-- Claim boundary.

depthOneCharacterStatement : String
depthOneCharacterStatement =
  "The complete three-character table of the additive group Z/3Z is implemented over a symbolic third-root phase ring, with the character homomorphism law checked by finite exhaustion."

depthOneCharacterBoundary : String
depthOneCharacterBoundary =
  "This establishes the exact depth-one character family, not the higher-depth cyclotomic DFT, orthogonality sum, inverse transform, Parseval theorem, or uniform-in-depth spectral limit."
