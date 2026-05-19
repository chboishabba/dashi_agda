module DASHI.Physics.Closure.ShellDictionaryRecoveryGateTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.ShellFillingDictionaryCompatibilityTheorem as SFDCT
open import Ontology.DNA.ChemistryQuotient as CDQ

------------------------------------------------------------------------
-- Smallest honest strengthening beyond shell/dictionary interface descent.
--
-- This theorem does not claim shell-filling uniqueness, periodic-table
-- structure, spectra, ionization energies, bonding, or finished chemistry.
-- It only promotes the current quotient-visible gate to a theorem-facing
-- shell/dictionary recovery class across the currently landed concrete and
-- UV-concrete chemistry interfaces.

record ShellDictionaryRecoveryGateTheorem : Setω where
  field
    shellDictionaryCompatibility :
      SFDCT.ShellFillingDictionaryCompatibilityTheorem

    recoveryGate :
      CDQ.ChemistryFeature → CDQ.ChemistryFeature
    recoveryGateStable :
      ∀ f →
      recoveryGate f ≡ f

    recoveredDictionaryClass :
      CDQ.ChemistryFeature → Set

    closedShellClassRecovered : Set

    concreteRepresentativeRecovered :
      ∀ f →
      CDQ.ChemistryQuotient._≈chem_
        (CDQ.ChemistryQuotientInterface.quotient
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
            shellDictionaryCompatibility))
        (CDQ.ChemistryQuotientInterface.representative
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
            shellDictionaryCompatibility)
          (recoveryGate f))
        (CDQ.ChemistryQuotientInterface.representative
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
            shellDictionaryCompatibility)
          f)

    uvRepresentativeRecovered :
      ∀ f →
      CDQ.ChemistryQuotient._≈chem_
        (CDQ.ChemistryQuotientInterface.quotient
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
            shellDictionaryCompatibility))
        (CDQ.ChemistryQuotientInterface.representative
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
            shellDictionaryCompatibility)
          (recoveryGate f))
        (CDQ.ChemistryQuotientInterface.representative
          (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
            shellDictionaryCompatibility)
          f)

    carrierIndependenceGate : Set

    nonClaimBoundary : List String

canonicalShellDictionaryRecoveryGateTheorem :
  ShellDictionaryRecoveryGateTheorem
canonicalShellDictionaryRecoveryGateTheorem =
  let
    compatibility =
      SFDCT.canonicalShellFillingDictionaryCompatibilityTheorem
    gate =
      SFDCT.ShellFillingDictionaryCompatibilityTheorem.chemistryDictionaryGate
        compatibility
    gate-stable =
      SFDCT.ShellFillingDictionaryCompatibilityTheorem.chemistryDictionaryGateStable
        compatibility
    concrete-compatible =
      SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteQuotientCompatible
        compatibility
    uv-compatible =
      SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvQuotientCompatible
        compatibility
  in
  record
    { shellDictionaryCompatibility = compatibility
    ; recoveryGate = gate
    ; recoveryGateStable = gate-stable
    ; recoveredDictionaryClass =
        λ _ → CDQ.ChemistryFeature
    ; closedShellClassRecovered =
        (f : CDQ.ChemistryFeature) → gate f ≡ f
    ; concreteRepresentativeRecovered =
        concrete-compatible
    ; uvRepresentativeRecovered =
        uv-compatible
    ; carrierIndependenceGate =
        (f : CDQ.ChemistryFeature) →
        CDQ.ChemistryQuotient._≈chem_
          (CDQ.ChemistryQuotientInterface.quotient
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
              compatibility))
          (CDQ.ChemistryQuotientInterface.representative
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
              compatibility)
            (gate f))
          (CDQ.ChemistryQuotientInterface.representative
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.concreteInterface
              compatibility)
            f)
        ×
        CDQ.ChemistryQuotient._≈chem_
          (CDQ.ChemistryQuotientInterface.quotient
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
              compatibility))
          (CDQ.ChemistryQuotientInterface.representative
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
              compatibility)
            (gate f))
          (CDQ.ChemistryQuotientInterface.representative
            (SFDCT.ShellFillingDictionaryCompatibilityTheorem.uvConcreteInterface
              compatibility)
            f)
    ; nonClaimBoundary =
        "ShellDictionaryRecoveryGateTheorem upgrades the current shell/dictionary lane only to a quotient-visible recovery class"
        ∷ "It does not prove shell-filling uniqueness, periodic-table structure, spectra, ionization energies, bonding, or finished chemistry"
        ∷ "The recoveryGate remains the current chemistry dictionary gate carried by the closed-shell package"
        ∷ []
    }

