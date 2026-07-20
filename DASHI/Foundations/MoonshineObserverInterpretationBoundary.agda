module DASHI.Foundations.MoonshineObserverInterpretationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.Moonshine196883Boundary as Moonshine
import DASHI.Foundations.ObserverExtensionBoundary as Observer

------------------------------------------------------------------------
-- The exact arithmetic split may carry an explicit DASHI observer reading,
-- but that reading is not a theorem of moonshine, Monster representation
-- theory, or the modular j-invariant.

observerPlusOneArithmetic : Moonshine.moonshineLargeFactor + 1 ≡ 196884
observerPlusOneArithmetic = Moonshine.moonshinePlusIdentity-value

record ObserverPlusOneInterpretation : Set where
  constructor observerPlusOneInterpretation
  field
    arithmeticSplit : Moonshine.PlusOneSplit
    observerExtension : Observer.ObserverExtensionBoundary
    nontrivialStructureLabel : String
    identitySummandLabel : String
    assembledLabel : String
    observerReadingExplicitlyInterpretive : Bool
    periodClaimPromoted : Bool
    periodClaimPromotedIsFalse : periodClaimPromoted ≡ false
    jFixedPointClaimPromoted : Bool
    jFixedPointClaimPromotedIsFalse : jFixedPointClaimPromoted ≡ false
    monsterAuthorityPromoted : Bool
    monsterAuthorityPromotedIsFalse : monsterAuthorityPromoted ≡ false
    modularJAuthorityPromoted : Bool
    modularJAuthorityPromotedIsFalse : modularJAuthorityPromoted ≡ false

canonicalObserverPlusOneInterpretation : ObserverPlusOneInterpretation
canonicalObserverPlusOneInterpretation =
  observerPlusOneInterpretation
    Moonshine.canonical196884Split
    Observer.canonicalObserverExtensionBoundary
    "196883 as the supplied nontrivial structural summand"
    "1 as a trivial, identity, or observer summand"
    "196884 as the exact direct arithmetic assembly"
    true
    false refl
    false refl
    false refl
    false refl

record MoonshineObserverBoundary : Set where
  constructor moonshineObserverBoundary
  field
    exactArithmeticRetained : Bool
    observerReadingAllowedAsNamedChart : Bool
    arithmeticProvesObserverOntology : Bool
    arithmeticProvesObserverOntologyIsFalse :
      arithmeticProvesObserverOntology ≡ false
    plusOneAutomaticallyChangesTopology : Bool
    plusOneAutomaticallyChangesTopologyIsFalse :
      plusOneAutomaticallyChangesTopology ≡ false
    interpretation : String

canonicalMoonshineObserverBoundary : MoonshineObserverBoundary
canonicalMoonshineObserverBoundary =
  moonshineObserverBoundary
    true
    true
    false refl
    false refl
    "196884=196883+1 supports an explicit trivial-plus-nontrivial or observer-summand chart, while period, topology, Monster, and modular-j consequences remain separately gated"
