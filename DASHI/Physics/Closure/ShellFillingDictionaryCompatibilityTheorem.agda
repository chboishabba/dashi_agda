module DASHI.Physics.Closure.ShellFillingDictionaryCompatibilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.Closure.ClosedShellStabilityGateTheorem as CSGT
open import Ontology.DNA.ChemistryQuotient as CDQ
open import Ontology.DNA.ChemistryConcrete as CDC
open import Ontology.DNA.ChemistryUVConcrete as CDUV

------------------------------------------------------------------------
-- Smallest honest shell-filling / chemistry-dictionary strengthening lane.
--
-- This theorem does not claim shell-filling uniqueness, spectra recovery,
-- ionization-energy recovery, bonding, or finished chemistry. It only says:
--
-- * the currently landed closed-shell gate can be read on the current
--   chemistry dictionary carrier;
-- * that carrier already has concrete quotient interfaces; and
-- * the gate descends coherently through those quotient interfaces.

record ShellFillingDictionaryCompatibilityTheorem : Setω where
  field
    closedShellGate : CSGT.ClosedShellStabilityGateTheorem

    chemistryFeatureCarrier : Set
    chemistryFeatureCarrier≡ :
      chemistryFeatureCarrier ≡ CDQ.ChemistryFeature

    chemistryDictionaryGate :
      CDQ.ChemistryFeature → CDQ.ChemistryFeature
    chemistryDictionaryGateStable :
      ∀ f →
      chemistryDictionaryGate f ≡ f

    concreteInterface : CDQ.ChemistryQuotientInterface
    uvConcreteInterface : CDQ.ChemistryQuotientInterface

    concreteSectionStable :
      ∀ f →
      CDQ.ChemistryQuotient.featureMap
        (CDQ.ChemistryQuotientInterface.quotient concreteInterface)
        (CDQ.ChemistryQuotientInterface.representative
          concreteInterface
          (chemistryDictionaryGate f))
        ≡
      f

    uvSectionStable :
      ∀ f →
      CDQ.ChemistryQuotient.featureMap
        (CDQ.ChemistryQuotientInterface.quotient uvConcreteInterface)
        (CDQ.ChemistryQuotientInterface.representative
          uvConcreteInterface
          (chemistryDictionaryGate f))
        ≡
      f

    concreteQuotientCompatible :
      ∀ f →
      CDQ.ChemistryQuotient._≈chem_
        (CDQ.ChemistryQuotientInterface.quotient concreteInterface)
        (CDQ.ChemistryQuotientInterface.representative
          concreteInterface
          (chemistryDictionaryGate f))
        (CDQ.ChemistryQuotientInterface.representative
          concreteInterface
          f)

    uvQuotientCompatible :
      ∀ f →
      CDQ.ChemistryQuotient._≈chem_
        (CDQ.ChemistryQuotientInterface.quotient uvConcreteInterface)
        (CDQ.ChemistryQuotientInterface.representative
          uvConcreteInterface
          (chemistryDictionaryGate f))
        (CDQ.ChemistryQuotientInterface.representative
          uvConcreteInterface
          f)

    closedShellDictionaryClassStable :
      ∀ f →
      CDQ.ChemistryQuotient._≈chem_
        (CDQ.ChemistryQuotientInterface.quotient concreteInterface)
        (CDQ.ChemistryQuotientInterface.representative
          concreteInterface
          (chemistryDictionaryGate f))
        (CDQ.ChemistryQuotientInterface.representative
          concreteInterface
          f)

    nonClaimBoundary : List String

canonicalShellFillingDictionaryCompatibilityTheorem :
  ShellFillingDictionaryCompatibilityTheorem
canonicalShellFillingDictionaryCompatibilityTheorem =
  let
    closedShellGate = CSGT.canonicalClosedShellStabilityGateTheorem
    gate =
      CSGT.ClosedShellStabilityGateTheorem.chemistryDictionaryGate
        closedShellGate
    gate-stable =
      CSGT.ClosedShellStabilityGateTheorem.chemistryDictionaryGateStable
        closedShellGate
  in
  record
    { closedShellGate = closedShellGate
    ; chemistryFeatureCarrier =
        CSGT.ClosedShellStabilityGateTheorem.chemistryFeatureCarrier
          closedShellGate
    ; chemistryFeatureCarrier≡ = refl
    ; chemistryDictionaryGate = gate
    ; chemistryDictionaryGateStable = gate-stable
    ; concreteInterface = CDC.chemistryQuotientInterfaceConcrete
    ; uvConcreteInterface = CDUV.chemistryQuotientInterfaceUVConcrete
    ; concreteSectionStable =
        λ f →
          trans
            (CDQ.ChemistryQuotientInterface.section
              CDC.chemistryQuotientInterfaceConcrete
              (gate f))
            (gate-stable f)
    ; uvSectionStable =
        λ f →
          trans
            (CDQ.ChemistryQuotientInterface.section
              CDUV.chemistryQuotientInterfaceUVConcrete
              (gate f))
            (gate-stable f)
    ; concreteQuotientCompatible =
        λ f →
          trans
            (CDQ.ChemistryQuotientInterface.section
              CDC.chemistryQuotientInterfaceConcrete
              (gate f))
            (trans
              (gate-stable f)
              (sym
                (CDQ.ChemistryQuotientInterface.section
                  CDC.chemistryQuotientInterfaceConcrete
                  f)))
    ; uvQuotientCompatible =
        λ f →
          trans
            (CDQ.ChemistryQuotientInterface.section
              CDUV.chemistryQuotientInterfaceUVConcrete
              (gate f))
            (trans
              (gate-stable f)
              (sym
                (CDQ.ChemistryQuotientInterface.section
                  CDUV.chemistryQuotientInterfaceUVConcrete
                  f)))
    ; closedShellDictionaryClassStable =
        λ f →
          trans
            (CDQ.ChemistryQuotientInterface.section
              CDC.chemistryQuotientInterfaceConcrete
              (gate f))
            (trans
              (gate-stable f)
              (sym
                (CDQ.ChemistryQuotientInterface.section
                  CDC.chemistryQuotientInterfaceConcrete
                  f)))
    ; nonClaimBoundary =
        "ShellFillingDictionaryCompatibilityTheorem only says the current closed-shell gate descends coherently through the current chemistry quotient interfaces"
        ∷ "It does not prove shell-filling uniqueness, periodic-table structure, spectra, ionization energies, bonding, or finished chemistry"
        ∷ "The chemistryDictionaryGate remains the current quotient-visible gate, not a full atomic solver"
        ∷ []
    }
