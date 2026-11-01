module DASHI.Promotion.ChemistryFiniteRuleTargets where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant
import DASHI.Promotion.ChemistrySpectroscopyAuthorityIntake as Intake

------------------------------------------------------------------------
-- Finite chemistry rule targets.
--
-- This module records a finite, canonical shell-filling target surface for
-- the first ten atomic numbers.  It also records symbolic Rydberg and Gibbs
-- formula slots.  The finite rows are computable targets only: measured
-- constants, spectra, thermochemistry, and wet-lab authority remain gated by
-- the upstream quantitative adapter and spectroscopy authority intake.

data FiniteElementTarget : Set where
  hydrogen : FiniteElementTarget
  helium : FiniteElementTarget
  lithium : FiniteElementTarget
  beryllium : FiniteElementTarget
  boron : FiniteElementTarget
  carbon : FiniteElementTarget
  nitrogen : FiniteElementTarget
  oxygen : FiniteElementTarget
  fluorine : FiniteElementTarget
  neon : FiniteElementTarget

atomicNumber : FiniteElementTarget → Nat
atomicNumber hydrogen = 1
atomicNumber helium = 2
atomicNumber lithium = 3
atomicNumber beryllium = 4
atomicNumber boron = 5
atomicNumber carbon = 6
atomicNumber nitrogen = 7
atomicNumber oxygen = 8
atomicNumber fluorine = 9
atomicNumber neon = 10

record ShellOccupation : Set where
  constructor shell
  field
    oneS : Nat
    twoS : Nat
    twoPX : Nat
    twoPY : Nat
    twoPZ : Nat

open ShellOccupation public

occupationElectronCount : ShellOccupation → Nat
occupationElectronCount occ =
  oneS occ + twoS occ + twoPX occ + twoPY occ + twoPZ occ

finiteAufbauOccupation : FiniteElementTarget → ShellOccupation
finiteAufbauOccupation hydrogen = shell 1 0 0 0 0
finiteAufbauOccupation helium = shell 2 0 0 0 0
finiteAufbauOccupation lithium = shell 2 1 0 0 0
finiteAufbauOccupation beryllium = shell 2 2 0 0 0
finiteAufbauOccupation boron = shell 2 2 1 0 0
finiteAufbauOccupation carbon = shell 2 2 1 1 0
finiteAufbauOccupation nitrogen = shell 2 2 1 1 1
finiteAufbauOccupation oxygen = shell 2 2 2 1 1
finiteAufbauOccupation fluorine = shell 2 2 2 2 1
finiteAufbauOccupation neon = shell 2 2 2 2 2

data FiniteRuleKind : Set where
  aufbauRule : FiniteRuleKind
  pauliRule : FiniteRuleKind
  hundRule : FiniteRuleKind

record FiniteRuleTarget : Set₁ where
  field
    ruleLabel : String
    ruleKind : FiniteRuleKind
    finiteCarrier : String
    exactTargetCount : Nat
    targetElements : List FiniteElementTarget
    authorityBoundary : String
    finiteRuleAccepted : Bool
    finiteRuleAcceptedIsTrue : finiteRuleAccepted ≡ true
    promotesPhysicalChemistry : Bool
    promotesPhysicalChemistryIsFalse :
      promotesPhysicalChemistry ≡ false
    promotesSpectroscopy : Bool
    promotesSpectroscopyIsFalse :
      promotesSpectroscopy ≡ false
    promotesWetLabValidation : Bool
    promotesWetLabValidationIsFalse :
      promotesWetLabValidation ≡ false

open FiniteRuleTarget public

canonicalFiniteElementTargets : List FiniteElementTarget
canonicalFiniteElementTargets =
  hydrogen
  ∷ helium
  ∷ lithium
  ∷ beryllium
  ∷ boron
  ∷ carbon
  ∷ nitrogen
  ∷ oxygen
  ∷ fluorine
  ∷ neon
  ∷ []

targetCount : List FiniteElementTarget → Nat
targetCount [] = zero
targetCount (_ ∷ xs) = suc (targetCount xs)

ruleCount : List FiniteRuleTarget → Nat
ruleCount [] = zero
ruleCount (_ ∷ xs) = suc (ruleCount xs)

mkFiniteRuleTarget :
  String →
  FiniteRuleKind →
  String →
  String →
  FiniteRuleTarget
mkFiniteRuleTarget label kind carrier boundary =
  record
    { ruleLabel = label
    ; ruleKind = kind
    ; finiteCarrier = carrier
    ; exactTargetCount = targetCount canonicalFiniteElementTargets
    ; targetElements = canonicalFiniteElementTargets
    ; authorityBoundary = boundary
    ; finiteRuleAccepted = true
    ; finiteRuleAcceptedIsTrue = refl
    ; promotesPhysicalChemistry = false
    ; promotesPhysicalChemistryIsFalse = refl
    ; promotesSpectroscopy = false
    ; promotesSpectroscopyIsFalse = refl
    ; promotesWetLabValidation = false
    ; promotesWetLabValidationIsFalse = refl
    }

canonicalFiniteRuleTargets : List FiniteRuleTarget
canonicalFiniteRuleTargets =
  mkFiniteRuleTarget
    "finite Aufbau shell-filling target"
    aufbauRule
    "1s then 2s then 2p capacity order for Z = 1..10"
    "finite ordering target only; orbital energies and anomalies need physical authority"
  ∷ mkFiniteRuleTarget
    "finite Pauli shell-capacity target"
    pauliRule
    "1s <= 2, 2s <= 2, each 2p orbital <= 2"
    "finite capacity check only; spin/orbital semantics need quantum and spectroscopy authority"
  ∷ mkFiniteRuleTarget
    "finite Hund 2p occupancy target"
    hundRule
    "2p single-occupancy before pairing for boron through neon"
    "finite multiplicity target only; measured term symbols and spectra need authority"
  ∷ []

data FormulaSlotKind : Set where
  rydbergFormulaSlot : FormulaSlotKind
  gibbsDeltaGFormulaSlot : FormulaSlotKind

record ChemistryFormulaSlot : Set₁ where
  field
    formulaLabel : String
    formulaKind : FormulaSlotKind
    registrySlotLabel : String
    symbolicFormula : String
    exactInputs : List String
    measuredAuthorityInputs : List String
    adapterBoundary : String
    measuredAuthorityAccepted : Bool
    measuredAuthorityAcceptedIsFalse :
      measuredAuthorityAccepted ≡ false
    spectroscopyAuthorityAccepted : Bool
    spectroscopyAuthorityAcceptedIsFalse :
      spectroscopyAuthorityAccepted ≡ false
    thermochemistryAuthorityAccepted : Bool
    thermochemistryAuthorityAcceptedIsFalse :
      thermochemistryAuthorityAccepted ≡ false
    wetLabAuthorityAccepted : Bool
    wetLabAuthorityAcceptedIsFalse :
      wetLabAuthorityAccepted ≡ false
    promotesFormulaClaim : Bool
    promotesFormulaClaimIsFalse :
      promotesFormulaClaim ≡ false

open ChemistryFormulaSlot public

mkFormulaSlot :
  String →
  FormulaSlotKind →
  String →
  String →
  List String →
  List String →
  String →
  ChemistryFormulaSlot
mkFormulaSlot label kind registrySlot formula exact measured boundary =
  record
    { formulaLabel = label
    ; formulaKind = kind
    ; registrySlotLabel = registrySlot
    ; symbolicFormula = formula
    ; exactInputs = exact
    ; measuredAuthorityInputs = measured
    ; adapterBoundary = boundary
    ; measuredAuthorityAccepted = false
    ; measuredAuthorityAcceptedIsFalse = refl
    ; spectroscopyAuthorityAccepted = false
    ; spectroscopyAuthorityAcceptedIsFalse = refl
    ; thermochemistryAuthorityAccepted = false
    ; thermochemistryAuthorityAcceptedIsFalse = refl
    ; wetLabAuthorityAccepted = false
    ; wetLabAuthorityAcceptedIsFalse = refl
    ; promotesFormulaClaim = false
    ; promotesFormulaClaimIsFalse = refl
    }

formulaSlotCount : List ChemistryFormulaSlot → Nat
formulaSlotCount [] = zero
formulaSlotCount (_ ∷ xs) = suc (formulaSlotCount xs)

canonicalFormulaSlots : List ChemistryFormulaSlot
canonicalFormulaSlots =
  mkFormulaSlot
    "Rydberg wavelength/frequency formula slot"
    rydbergFormulaSlot
    "Registry constant slot: Rydberg constant / R_infinity"
    "1 / lambda = R_infinity (1 / n1^2 - 1 / n2^2)"
    ( "integer levels n1 and n2"
    ∷ "exact optical conversion through c when frequency is requested"
    ∷ []
    )
    ( "R_infinity : CODATA measured constant"
    ∷ "isotope and reduced-mass adapter"
    ∷ "spectral-line authority and uncertainty"
    ∷ []
    )
    "symbolic spectroscopy slot only; measured spectra are gated by authority intake"
  ∷ mkFormulaSlot
    "Gibbs delta-G formula slot"
    gibbsDeltaGFormulaSlot
    "Registry law slot: Gibbs free energy relation"
    "Delta G = Delta H - T Delta S; Delta G = Delta G0 + R T ln Q"
    ( "R : exact derived expression N_A k_B"
    ∷ "temperature carrier T"
    ∷ []
    )
    ( "enthalpy and entropy authority"
    ∷ "activity model and standard-state convention"
    ∷ "thermochemistry authority and uncertainty"
    ∷ []
    )
    "symbolic thermochemistry slot only; measured values remain authority-gated"
  ∷ []

record ChemistryFiniteRuleTargets : Set₁ where
  field
    registryReceipt :
      Registry.ChemistryKnownInputsReferenceReceipt
    quantitativeAdapter :
      Quant.ChemistryQuantitativeAdapter
    spectroscopyAuthorityIntake :
      Intake.ChemistrySpectroscopyAuthorityIntake
    elements :
      List FiniteElementTarget
    elementCount :
      Nat
    elementCountMatches :
      elementCount ≡ targetCount elements
    finiteRules :
      List FiniteRuleTarget
    finiteRuleCount :
      Nat
    finiteRuleCountMatches :
      finiteRuleCount ≡ ruleCount finiteRules
    formulaSlots :
      List ChemistryFormulaSlot
    formulaSlotCountField :
      Nat
    formulaSlotCountMatches :
      formulaSlotCountField ≡ formulaSlotCount formulaSlots
    shellProfileFunction :
      FiniteElementTarget → ShellOccupation
    hydrogenElectronCount :
      occupationElectronCount (shellProfileFunction hydrogen) ≡
      atomicNumber hydrogen
    neonElectronCount :
      occupationElectronCount (shellProfileFunction neon) ≡
      atomicNumber neon
    finiteComputationOnly :
      Bool
    finiteComputationOnlyIsTrue :
      finiteComputationOnly ≡ true
    measuredConstantsAuthorityAccepted :
      Bool
    measuredConstantsAuthorityAcceptedIsFalse :
      measuredConstantsAuthorityAccepted ≡ false
    spectroscopyAuthorityAccepted :
      Bool
    spectroscopyAuthorityAcceptedIsFalse :
      spectroscopyAuthorityAccepted ≡ false
    thermochemistryAuthorityAccepted :
      Bool
    thermochemistryAuthorityAcceptedIsFalse :
      thermochemistryAuthorityAccepted ≡ false
    wetLabAuthorityAccepted :
      Bool
    wetLabAuthorityAcceptedIsFalse :
      wetLabAuthorityAccepted ≡ false
    promotesPhysicalChemistry :
      Bool
    promotesPhysicalChemistryIsFalse :
      promotesPhysicalChemistry ≡ false
    promotesSpectroscopy :
      Bool
    promotesSpectroscopyIsFalse :
      promotesSpectroscopy ≡ false
    promotesWetLabValidation :
      Bool
    promotesWetLabValidationIsFalse :
      promotesWetLabValidation ≡ false
    validationCommand :
      String

open ChemistryFiniteRuleTargets public

canonicalChemistryFiniteRuleTargets : ChemistryFiniteRuleTargets
canonicalChemistryFiniteRuleTargets =
  record
    { registryReceipt =
        Registry.canonicalChemistryKnownInputsReferenceReceipt
    ; quantitativeAdapter =
        Quant.canonicalChemistryQuantitativeAdapter
    ; spectroscopyAuthorityIntake =
        Intake.canonicalChemistrySpectroscopyAuthorityIntake
    ; elements =
        canonicalFiniteElementTargets
    ; elementCount =
        10
    ; elementCountMatches =
        refl
    ; finiteRules =
        canonicalFiniteRuleTargets
    ; finiteRuleCount =
        3
    ; finiteRuleCountMatches =
        refl
    ; formulaSlots =
        canonicalFormulaSlots
    ; formulaSlotCountField =
        2
    ; formulaSlotCountMatches =
        refl
    ; shellProfileFunction =
        finiteAufbauOccupation
    ; hydrogenElectronCount =
        refl
    ; neonElectronCount =
        refl
    ; finiteComputationOnly =
        true
    ; finiteComputationOnlyIsTrue =
        refl
    ; measuredConstantsAuthorityAccepted =
        false
    ; measuredConstantsAuthorityAcceptedIsFalse =
        refl
    ; spectroscopyAuthorityAccepted =
        false
    ; spectroscopyAuthorityAcceptedIsFalse =
        refl
    ; thermochemistryAuthorityAccepted =
        false
    ; thermochemistryAuthorityAcceptedIsFalse =
        refl
    ; wetLabAuthorityAccepted =
        false
    ; wetLabAuthorityAcceptedIsFalse =
        refl
    ; promotesPhysicalChemistry =
        false
    ; promotesPhysicalChemistryIsFalse =
        refl
    ; promotesSpectroscopy =
        false
    ; promotesSpectroscopyIsFalse =
        refl
    ; promotesWetLabValidation =
        false
    ; promotesWetLabValidationIsFalse =
        refl
    ; validationCommand =
        "agda -i . DASHI/Promotion/ChemistryFiniteRuleTargets.agda"
    }

canonicalFiniteElementCountIs10 :
  elementCount canonicalChemistryFiniteRuleTargets ≡ 10
canonicalFiniteElementCountIs10 = refl

canonicalFiniteRuleCountIs3 :
  finiteRuleCount canonicalChemistryFiniteRuleTargets ≡ 3
canonicalFiniteRuleCountIs3 = refl

canonicalFormulaSlotCountIs2 :
  formulaSlotCountField canonicalChemistryFiniteRuleTargets ≡ 2
canonicalFormulaSlotCountIs2 = refl

canonicalHydrogenElectronCountIs1 :
  occupationElectronCount (finiteAufbauOccupation hydrogen) ≡ 1
canonicalHydrogenElectronCountIs1 = refl

canonicalNeonElectronCountIs10 :
  occupationElectronCount (finiteAufbauOccupation neon) ≡ 10
canonicalNeonElectronCountIs10 = refl

canonicalMeasuredConstantsAuthorityAcceptedIsFalse :
  measuredConstantsAuthorityAccepted
    canonicalChemistryFiniteRuleTargets ≡ false
canonicalMeasuredConstantsAuthorityAcceptedIsFalse = refl

canonicalSpectroscopyAuthorityAcceptedIsFalse :
  spectroscopyAuthorityAccepted canonicalChemistryFiniteRuleTargets ≡ false
canonicalSpectroscopyAuthorityAcceptedIsFalse = refl

canonicalThermochemistryAuthorityAcceptedIsFalse :
  thermochemistryAuthorityAccepted
    canonicalChemistryFiniteRuleTargets ≡ false
canonicalThermochemistryAuthorityAcceptedIsFalse = refl

canonicalWetLabAuthorityAcceptedIsFalse :
  wetLabAuthorityAccepted canonicalChemistryFiniteRuleTargets ≡ false
canonicalWetLabAuthorityAcceptedIsFalse = refl

canonicalPhysicalChemistryPromotionIsFalse :
  promotesPhysicalChemistry canonicalChemistryFiniteRuleTargets ≡ false
canonicalPhysicalChemistryPromotionIsFalse = refl

canonicalSpectroscopyPromotionIsFalse :
  promotesSpectroscopy canonicalChemistryFiniteRuleTargets ≡ false
canonicalSpectroscopyPromotionIsFalse = refl

canonicalWetLabPromotionIsFalse :
  promotesWetLabValidation canonicalChemistryFiniteRuleTargets ≡ false
canonicalWetLabPromotionIsFalse = refl
