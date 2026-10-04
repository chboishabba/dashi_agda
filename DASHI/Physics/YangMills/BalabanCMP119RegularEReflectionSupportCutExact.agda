{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularEReflectionSupportCutExact where

------------------------------------------------------------------------
-- CMP119 REGULAR-E / OS SUPPORT CUT
--
-- The selected Sect.-2 regular-E form already owns
--
--   E_k(A) = sum_component E_k(component,A)
--
-- on one finite component list.  Unlike the B and R source carriers, however,
-- that record currently exposes `Component` rather than a source `Polymer`.
-- There is no component->polymer support map elsewhere in the live repository.
--
-- This file names exactly that representation seam.  Given a map from the SAME
-- localized component to a literal periodic block polymer, the already-owned
-- OS-time classifier applies without changing the E activity or inventing new
-- localization mathematics.
--
-- Supplying this map with its physical/source meaning remains conditional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as E
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Geometry

------------------------------------------------------------------------
-- Minimal same-component support dictionary.
------------------------------------------------------------------------

record RegularEComponentPeriodicSupportDictionary
    {Density Background Volume Component : Set}
    {scale : Nat} {density : Density}
    (form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density)
    (n : Nat) : Set₁ where
  field
    -- This is a support dictionary for the SAME `Component` that indexes the
    -- existing localizedRegularActivity.  It is not a replacement component.
    componentPolymer : Component → Periodic.PeriodicPolymer n

open RegularEComponentPeriodicSupportDictionary public

------------------------------------------------------------------------
-- Executable classifier, separated from the source witness.
------------------------------------------------------------------------

classifyRegularEComponentAtCut :
  ∀ {n Component} →
  (Component → Periodic.PeriodicPolymer n) →
  Nat → Component → Geometry.PolymerReflectionClass
classifyRegularEComponentAtCut support cut component =
  Geometry.classifyPeriodicPolymerAtCut cut (support component)

RegularEComponentPositiveOnly :
  ∀ {Density Background Volume Component scale density n}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density} →
  RegularEComponentPeriodicSupportDictionary form n →
  Nat → Component → Set
RegularEComponentPositiveOnly dictionary cut component =
  classifyRegularEComponentAtCut
    (componentPolymer dictionary) cut component ≡ Geometry.positiveOnly

RegularEComponentNegativeOnly :
  ∀ {Density Background Volume Component scale density n}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density} →
  RegularEComponentPeriodicSupportDictionary form n →
  Nat → Component → Set
RegularEComponentNegativeOnly dictionary cut component =
  classifyRegularEComponentAtCut
    (componentPolymer dictionary) cut component ≡ Geometry.negativeOnly

RegularEComponentCrossing :
  ∀ {Density Background Volume Component scale density n}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density} →
  RegularEComponentPeriodicSupportDictionary form n →
  Nat → Component → Set
RegularEComponentCrossing dictionary cut component =
  classifyRegularEComponentAtCut
    (componentPolymer dictionary) cut component ≡ Geometry.crossingSupport

RegularEComponentEmptySupport :
  ∀ {Density Background Volume Component scale density n}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density} →
  RegularEComponentPeriodicSupportDictionary form n →
  Nat → Component → Set
RegularEComponentEmptySupport dictionary cut component =
  classifyRegularEComponentAtCut
    (componentPolymer dictionary) cut component ≡ Geometry.emptySupport

------------------------------------------------------------------------
-- Every localized E component gets exactly one classifier value.
------------------------------------------------------------------------

regularEComponentSupportClassCases :
  ∀ {Density Background Volume Component scale density n}
    {form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density}
    (dictionary : RegularEComponentPeriodicSupportDictionary form n)
    cut component →
  RegularEComponentPositiveOnly dictionary cut component
  ⊎ RegularEComponentNegativeOnly dictionary cut component
  ⊎ RegularEComponentCrossing dictionary cut component
  ⊎ RegularEComponentEmptySupport dictionary cut component
regularEComponentSupportClassCases dictionary cut component
  with classifyRegularEComponentAtCut
    (componentPolymer dictionary) cut component
... | Geometry.positiveOnly = inj₁ refl
... | Geometry.negativeOnly = inj₂ (inj₁ refl)
... | Geometry.crossingSupport = inj₂ (inj₂ (inj₁ refl))
... | Geometry.emptySupport = inj₂ (inj₂ (inj₂ refl))

------------------------------------------------------------------------
-- Status firewall.
------------------------------------------------------------------------

regularEReflectionSupportClassifierLevel : ProofLevel
regularEReflectionSupportClassifierLevel = machineChecked

-- Source/representation payment: identify each selected CMP119 localized E
-- component with its actual periodic support polymer on the same cutoff.
regularEComponentPeriodicSupportDictionaryLevel : ProofLevel
regularEComponentPeriodicSupportDictionaryLevel = conditional

-- One-sided localized E activities still have to be proved to transform into
-- each other under the selected OS reflection.
cmp119RegularEOneSidedActivityReflectionLevel : ProofLevel
cmp119RegularEOneSidedActivityReflectionLevel = conditional

-- Only geometrically crossing E components need an independent cross-plane
-- kernel theorem or counterexample.
cmp119RegularECrossingKernelRPLevel : ProofLevel
cmp119RegularECrossingKernelRPLevel = conditional
