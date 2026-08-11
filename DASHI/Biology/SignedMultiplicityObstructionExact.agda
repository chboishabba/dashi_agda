module DASHI.Biology.SignedMultiplicityObstructionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Peter Buergisser, Christian Ikenmeyer, Greta Panova,
-- "No occurrence obstructions in geometric complexity theory",
-- Journal of the American Mathematical Society 32 (2019), 163-193.
-- DOI: 10.1090/jams/908.
--
-- Julian Doerfler, Christian Ikenmeyer, Greta Panova,
-- "On Geometric Complexity Theory: Multiplicity Obstructions Are Stronger
-- Than Occurrence Obstructions",
-- SIAM Journal on Applied Algebra and Geometry 4(2) (2020), 354-376.
-- DOI: 10.1137/19M1287638.
--
-- DASHI CONTRIBUTION
--
-- Replace the lossy Boolean occurrence shadow by an integer-valued relational
-- multiplicity defect.  Its sign is an exact three-way coarse quotient.  An
-- involution on representation labels gives the yin/yang-style twisted defect
-- and an exact anti-symmetry law.  This is a generic finite-index formalism;
-- it does NOT assert a new GCT lower bound or a Monster complexity theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer.Base using (ℤ; +_; -[1+_]; -_; _⊖_)
import Data.Integer.Properties as ℤP

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP

Multiplicity : Set → Set
Multiplicity I = I → Nat

delta : ∀ {I} → Multiplicity I → Multiplicity I → I → ℤ
delta A B i = A i ⊖ B i

data DefectOrientation : Set where
  negativeDefect balancedDefect positiveDefect : DefectOrientation

orientationOfInteger : ℤ → DefectOrientation
orientationOfInteger (+ zero) = balancedDefect
orientationOfInteger (+ suc n) = positiveDefect
orientationOfInteger -[1+ n ] = negativeDefect

reverseOrientation : DefectOrientation → DefectOrientation
reverseOrientation negativeDefect = positiveDefect
reverseOrientation balancedDefect = balancedDefect
reverseOrientation positiveDefect = negativeDefect

reverseOrientationInvolutive :
  (orientation : DefectOrientation) →
  reverseOrientation (reverseOrientation orientation) ≡ orientation
reverseOrientationInvolutive negativeDefect = refl
reverseOrientationInvolutive balancedDefect = refl
reverseOrientationInvolutive positiveDefect = refl

orientationNegates :
  (z : ℤ) →
  orientationOfInteger (- z) ≡ reverseOrientation (orientationOfInteger z)
orientationNegates (+ zero) = refl
orientationNegates (+ suc n) = refl
orientationNegates -[1+ n ] = refl

deltaSwap :
  ∀ {I} (A B : Multiplicity I) (i : I) →
  delta B A i ≡ - delta A B i
deltaSwap A B i = ℤP.⊖-swap (B i) (A i)

orientationSwap :
  ∀ {I} (A B : Multiplicity I) (i : I) →
  orientationOfInteger (delta B A i)
  ≡ reverseOrientation (orientationOfInteger (delta A B i))
orientationSwap A B i
  rewrite deltaSwap A B i = orientationNegates (delta A B i)

------------------------------------------------------------------------
-- Occurrence is a strict information-losing quotient of multiplicity.
------------------------------------------------------------------------

data Presence : Set where
  absent present : Presence

presence : Nat → Presence
presence zero = absent
presence (suc n) = present

oneAndTwoHaveSamePresence : presence 1 ≡ presence 2
oneAndTwoHaveSamePresence = refl

oneAndTwoHaveNonzeroSignedDefect : 1 ⊖ 2 ≡ -[1+ 0 ]
oneAndTwoHaveNonzeroSignedDefect = refl

-- Bridge the new defect orientation to the orientation language already used
-- by the full signed SSP/FRACTRAN weave.
toSSPFibreOrientation : DefectOrientation → SSP.FibreOrientation
toSSPFibreOrientation negativeDefect = SSP.inverseOrientation
toSSPFibreOrientation balancedDefect = SSP.mediatedOrientation
toSSPFibreOrientation positiveDefect = SSP.forwardOrientation

------------------------------------------------------------------------
-- Twisted yin/yang defect under an involution of representation labels.
------------------------------------------------------------------------

record LabelInvolution (I : Set) : Set where
  constructor labelInvolution
  field
    twist : I → I
    involutive : (i : I) → twist (twist i) ≡ i

open LabelInvolution public

twistedDelta :
  ∀ {I} → LabelInvolution I →
  Multiplicity I → Multiplicity I → I → ℤ
twistedDelta involution A B i = A i ⊖ B (twist involution i)

twistedAntiSymmetry :
  ∀ {I} (involution : LabelInvolution I)
    (A B : Multiplicity I) (i : I) →
  twistedDelta involution B A (twist involution i)
  ≡ - twistedDelta involution A B i
twistedAntiSymmetry involution A B i
  rewrite involutive involution i =
  ℤP.⊖-swap (B (twist involution i)) (A i)

record MultiplicityObstructionClaimScope : Set where
  constructor multiplicityObstructionClaimScope
  field
    signedDefectAndTwistedAntiSymmetryConstructed : Bool
    signedDefectAndTwistedAntiSymmetryConstructedIsTrue :
      signedDefectAndTwistedAntiSymmetryConstructed ≡ true

    occurrenceShownToForgetMultiplicity : Bool
    occurrenceShownToForgetMultiplicityIsTrue :
      occurrenceShownToForgetMultiplicity ≡ true

    permanentDeterminantSeparatedHere : Bool
    permanentDeterminantSeparatedHereIsFalse :
      permanentDeterminantSeparatedHere ≡ false

    monsterComplexityLowerBoundConstructed : Bool
    monsterComplexityLowerBoundConstructedIsFalse :
      monsterComplexityLowerBoundConstructed ≡ false

canonicalMultiplicityObstructionClaimScope : MultiplicityObstructionClaimScope
canonicalMultiplicityObstructionClaimScope =
  multiplicityObstructionClaimScope true refl true refl false refl false refl
