module DASHI.Foundations.CyclicNineCharacterPullbackExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The supplied PaletteCharacterTable development exhibits a ternary
-- character substructure inside the cyclic nine palette transform.  This
-- module records the exact quotient/pullback statement on existing DASHI
-- carriers rather than identifying C9 with C3 x C3.
--
-- DASHI CONTRIBUTION
--
--   C9 --mod 3--> C3 --chi_k--> {1,zeta,zeta^2}
--
-- gives three characters of C9 that factor through the ternary quotient.
-- They are constant on the three-element fibres {0,3,6}, {1,4,7}, {2,5,8},
-- reproduce the existing C3 character rows on the canonical section
-- {0,1,2}, and diagonalize one-step C9 rotation with the same cubic
-- eigenvalues.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.Phase3RootCharacterWeldExact as Root3
import DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact as Nine

------------------------------------------------------------------------
-- C9 -> C3 quotient.
------------------------------------------------------------------------

c9ToC3 : Base.NonaryTruth → Phase.Phase3
c9ToC3 n = Root3.triToPhase (Nine.nonaryMod3 n)

c9ToC3Rotation :
  (n : Base.NonaryTruth) →
  c9ToC3 (Base.rotateNonary n)
  ≡ Root3.zetaRotate (c9ToC3 n)
c9ToC3Rotation Base.non-0 = refl
c9ToC3Rotation Base.non-1 = refl
c9ToC3Rotation Base.non-2 = refl
c9ToC3Rotation Base.non-3 = refl
c9ToC3Rotation Base.non-4 = refl
c9ToC3Rotation Base.non-5 = refl
c9ToC3Rotation Base.non-6 = refl
c9ToC3Rotation Base.non-7 = refl
c9ToC3Rotation Base.non-8 = refl

------------------------------------------------------------------------
-- Pull back the three C3 characters.
------------------------------------------------------------------------

c9TernaryCharacter :
  Phase.Phase3 → Base.NonaryTruth → Phase.Phase3
c9TernaryCharacter k n = Root3.character k (c9ToC3 n)

c9CharacterZeroFibre :
  (k : Phase.Phase3) →
  c9TernaryCharacter k Base.non-0
    ≡ c9TernaryCharacter k Base.non-3
  × c9TernaryCharacter k Base.non-3
    ≡ c9TernaryCharacter k Base.non-6
c9CharacterZeroFibre Phase.phase0 = refl , refl
c9CharacterZeroFibre Phase.phase1 = refl , refl
c9CharacterZeroFibre Phase.phase2 = refl , refl

c9CharacterOneFibre :
  (k : Phase.Phase3) →
  c9TernaryCharacter k Base.non-1
    ≡ c9TernaryCharacter k Base.non-4
  × c9TernaryCharacter k Base.non-4
    ≡ c9TernaryCharacter k Base.non-7
c9CharacterOneFibre Phase.phase0 = refl , refl
c9CharacterOneFibre Phase.phase1 = refl , refl
c9CharacterOneFibre Phase.phase2 = refl , refl

c9CharacterTwoFibre :
  (k : Phase.Phase3) →
  c9TernaryCharacter k Base.non-2
    ≡ c9TernaryCharacter k Base.non-5
  × c9TernaryCharacter k Base.non-5
    ≡ c9TernaryCharacter k Base.non-8
c9CharacterTwoFibre Phase.phase0 = refl , refl
c9CharacterTwoFibre Phase.phase1 = refl , refl
c9CharacterTwoFibre Phase.phase2 = refl , refl

c9CharacterSectionRow :
  Phase.Phase3 → Phase.Phase3 × (Phase.Phase3 × Phase.Phase3)
c9CharacterSectionRow k =
  c9TernaryCharacter k Base.non-0 ,
  (c9TernaryCharacter k Base.non-1 ,
   c9TernaryCharacter k Base.non-2)

c9SectionReproducesC3CharacterTable :
  (k : Phase.Phase3) →
  c9CharacterSectionRow k ≡ Root3.characterRow k
c9SectionReproducesC3CharacterTable Phase.phase0 = refl
c9SectionReproducesC3CharacterTable Phase.phase1 = refl
c9SectionReproducesC3CharacterTable Phase.phase2 = refl

-- Pullback characters diagonalize the C9 generator because the quotient sends
-- one C9 step to one C3 step.
c9TernaryCharacterDiagonalizesRotation :
  (k : Phase.Phase3) →
  (n : Base.NonaryTruth) →
  c9TernaryCharacter k (Base.rotateNonary n)
  ≡ Root3.phaseMul k (c9TernaryCharacter k n)
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-0 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-1 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-2 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-3 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-4 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-5 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-6 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-7 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase0 Base.non-8 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-0 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-1 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-2 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-3 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-4 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-5 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-6 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-7 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase1 Base.non-8 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-0 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-1 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-2 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-3 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-4 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-5 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-6 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-7 = refl
c9TernaryCharacterDiagonalizesRotation Phase.phase2 Base.non-8 = refl

record CyclicNineCharacterPullbackBoundary : Set where
  field
    c9ToC3QuotientConstructed : Bool
    threeCharactersPulledBack : Bool
    threeElementFibresExplicit : Bool
    c3CharacterRowsRecovered : Bool
    c9IdentifiedWithC3TimesC3 : Bool

canonicalCyclicNineCharacterPullbackBoundary :
  CyclicNineCharacterPullbackBoundary
canonicalCyclicNineCharacterPullbackBoundary =
  record
    { c9ToC3QuotientConstructed = true
    ; threeCharactersPulledBack = true
    ; threeElementFibresExplicit = true
    ; c3CharacterRowsRecovered = true
    ; c9IdentifiedWithC3TimesC3 = false
    }
