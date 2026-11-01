module DASHI.Philosophy.LocalChartNormalisation where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import CRTJFixedPointBridge as CRTJ

------------------------------------------------------------------------
-- Generic local-unit structure.
--
-- The inverse and multiplication are typed operations supplied by the chart.
-- No claim is made that an arbitrary philosophical carrier is a field.

record LocalUnitStructure (X : Set) : Set₁ where
  field
    star :
      X

    unit :
      X

    inverse :
      X →
      X

    multiply :
      X →
      X →
      X

    leftIdentity :
      (x : X) →
      multiply unit x ≡ x

    rightIdentity :
      (x : X) →
      multiply x unit ≡ x

    starInverse :
      multiply (inverse star) star ≡ unit

open LocalUnitStructure public

normalise :
  ∀ {X : Set} →
  LocalUnitStructure X →
  X →
  X
normalise local x =
  multiply local (inverse local (star local)) x

normaliseStar :
  ∀ {X : Set} →
  (local : LocalUnitStructure X) →
  normalise local (star local) ≡ unit local
normaliseStar local =
  starInverse local

------------------------------------------------------------------------
-- Symbolic 10/11 chart.

globalStarIndex : Nat
globalStarIndex =
  10

relationalExtensionIndex : Nat
relationalExtensionIndex =
  11

jPlusOneIsEleven :
  globalStarIndex + 1 ≡ relationalExtensionIndex
jPlusOneIsEleven =
  refl

------------------------------------------------------------------------
-- Existing CRT/J arithmetic is retained as the mathematical owner.
-- The observer reading is an explicit symbolic bridge and does not promote a
-- social or political theorem.

record SymbolicJObserverBridge : Set₁ where
  field
    arithmeticBridge :
      CRTJ.CRTJFixedPointBridge

    globalStarReadAsTen :
      Bool

    localStarReadAsUnit :
      Bool

    observerReadingIsStructuralInterpretation :
      Bool

    observerReadingIsMathematicalOrPoliticalTheorem :
      Bool

    observerAloneChangesTopology :
      Bool

open SymbolicJObserverBridge public

canonicalSymbolicJObserverBridge :
  SymbolicJObserverBridge
canonicalSymbolicJObserverBridge =
  record
    { arithmeticBridge =
        CRTJ.crtJFixedPointBridgeSurface
    ; globalStarReadAsTen =
        true
    ; localStarReadAsUnit =
        true
    ; observerReadingIsStructuralInterpretation =
        true
    ; observerReadingIsMathematicalOrPoliticalTheorem =
        false
    ; observerAloneChangesTopology =
        false
    }

canonicalObserverAloneDoesNotChangeTopology :
  observerAloneChangesTopology canonicalSymbolicJObserverBridge
  ≡
  false
canonicalObserverAloneDoesNotChangeTopology =
  refl
