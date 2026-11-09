module DASHI.Chemistry.HydrogenFuelCycleAtomicMassConservationExact where

-- Source ownership:
-- Stoichiometric molecular step/path conservation is in existing PR #1481
-- DASHI.Chemistry.HydrogenMolecularInventoryExact (user-directed ChatGPT draft).
-- Atomic masses and their primary-source conventions are inherited from
-- DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact
-- (Prohaska et al., 2021 standard weights; DOI 10.1515/pac-2019-0603).
-- Reweighting atom counts is a routine algebraic consequence; no claim of
-- new chemical law, exact isotope masses, or verified device performance.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Chemistry.HydrogenMolecularInventoryExact as Chem
import DASHI.Chemistry.HydrogenFuelCycleAtomicIdentityExact as Atom

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
    {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

cong₃ :
  ∀ {A B C D : Set} (f : A → B → C → D)
    {x x' : A} {y y' : B} {z z' : C} →
  x ≡ x' → y ≡ y' → z ≡ z' →
  f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

-- A standard-weight linear functional on the *element counts*.
-- Values are milli-u convention indices, not measured macroscopic mass.
weightedElementConvention : Chem.Inventory → Nat
weightedElementConvention x =
  (Atom.hMassMilliU * Chem.hydrogenAtoms x)
  + ((Atom.cMassMilliU * Chem.carbonAtoms x)
  + (Atom.oMassMilliU * Chem.oxygenAtoms x))

oneStepConventionMassConserved :
  ∀ {x y} → Chem.MolecularStep x y →
  weightedElementConvention x ≡ weightedElementConvention y
oneStepConventionMassConserved step =
  cong₃
    (λ h c o →
      (Atom.hMassMilliU * h)
        + ((Atom.cMassMilliU * c) + (Atom.oMassMilliU * o)))
    (Chem.stepConservesHydrogen step)
    (Chem.stepConservesCarbon step)
    (Chem.stepConservesOxygen step)

pathConventionMassConserved :
  ∀ {x y} → Chem.MolecularPath x y →
  weightedElementConvention x ≡ weightedElementConvention y
pathConventionMassConserved path =
  cong₃
    (λ h c o →
      (Atom.hMassMilliU * h)
        + ((Atom.cMassMilliU * c) + (Atom.oMassMilliU * o)))
    (Chem.pathConservesHydrogen path)
    (Chem.pathConservesCarbon path)
    (Chem.pathConservesOxygen path)
