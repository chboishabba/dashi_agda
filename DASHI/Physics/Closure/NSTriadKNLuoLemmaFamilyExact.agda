module DASHI.Physics.Closure.NSTriadKNLuoLemmaFamilyExact where

------------------------------------------------------------------------
-- PURPOSE
-- Generic fail-closed representation of a named theorem family.
--
-- A LemmaSpecification assigns an actual proposition to every machine-readable
-- lemma name. LemmaInhabitants then requires a proof of every assigned
-- proposition. Inventories can therefore be constructed without claiming the
-- frontier analytic statements are already inhabited.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record LemmaSpecification (Name : Set) : Set₁ where
  field
    statement : Name → Set

open LemmaSpecification public

record LemmaInhabitants
    {Name : Set}
    (specification : LemmaSpecification Name) : Set₁ where
  field
    prove : (name : Name) → statement specification name

open LemmaInhabitants public

record CompleteLemmaFamily (Name : Set) : Set₁ where
  field
    specification : LemmaSpecification Name
    inhabitants : LemmaInhabitants specification

open CompleteLemmaFamily public

lemmaFamilyRepresentationConstructed : Bool
lemmaFamilyRepresentationConstructed = true

lemmaFamilyRepresentationConstructedIsTrue :
  lemmaFamilyRepresentationConstructed ≡ true
lemmaFamilyRepresentationConstructedIsTrue = refl
