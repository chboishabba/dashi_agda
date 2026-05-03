module DASHI.Physics.Closure.ChemistryRightLimitsQuotientObservable where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest genuinely new quotient-visible pre-spectral chemistry-facing
-- observable beyond the current defect/promoted pair.
--
-- This surface works entirely on ChemistryFeature, so it is quotient-visible
-- by construction. It stays pre-spectral and non-scale-setting by exposing
-- only a coarse strong/weak-channel count on the U-coordinate.

countStrong : ∀ {n} → Vec CDQ.Strength n → Nat
countStrong [] = zero
countStrong (CDQ.weak ∷ xs) = countStrong xs
countStrong (CDQ.strong ∷ xs) = suc (countStrong xs)

strongCountObservable : CDQ.ChemistryFeature → Nat
strongCountObservable f =
  countStrong (CDQ.ChemistryFeature.u f)

record ChemistryRightLimitsQuotientObservable : Setω where
  field
    observableName : String

    quotientObservable :
      CDQ.ChemistryFeature → Nat

    quotientVisible :
      (f : CDQ.ChemistryFeature) →
      quotientObservable f ≡ strongCountObservable f

    preSpectralBoundary : Set
    preScaleSettingBoundary : Set

    nonClaimBoundary : List String

canonicalChemistryRightLimitsQuotientObservable :
  ChemistryRightLimitsQuotientObservable
canonicalChemistryRightLimitsQuotientObservable =
  record
    { observableName =
        "quotient-visible strong-count pre-spectral observable"
    ; quotientObservable = strongCountObservable
    ; quotientVisible = λ _ → refl
    ; preSpectralBoundary =
        (f : CDQ.ChemistryFeature) →
        strongCountObservable f ≡ strongCountObservable f
    ; preScaleSettingBoundary =
        (f : CDQ.ChemistryFeature) →
        strongCountObservable f ≡ strongCountObservable f
    ; nonClaimBoundary =
        "ChemistryRightLimitsQuotientObservable only names a quotient-visible strong-count observable on ChemistryFeature.u"
        ∷ "It is pre-spectral and non-scale-setting, and it does not prove spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "It is a new chemistry-facing observable beyond the current defect/promoted empirical pair, but not yet coupled to them"
        ∷ []
    }
