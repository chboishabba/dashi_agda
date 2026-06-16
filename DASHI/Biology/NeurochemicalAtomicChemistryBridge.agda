module DASHI.Biology.NeurochemicalAtomicChemistryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BioactiveMolecularRecognitionBridge as Bioactive
import DASHI.Biology.NeurochemicalVocabularyReceipt as Vocabulary
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant

------------------------------------------------------------------------
-- Empty type for blocked routes.

data Never : Set where

------------------------------------------------------------------------
-- Slot vocabulary.

data NeurochemicalAtomicChemistrySlot : Set where
  formulaSlot : NeurochemicalAtomicChemistrySlot
  molecularGraphSlot : NeurochemicalAtomicChemistrySlot
  chargeSlot : NeurochemicalAtomicChemistrySlot
  protonationSlot : NeurochemicalAtomicChemistrySlot
  stereochemistrySlot : NeurochemicalAtomicChemistrySlot
  conformerSlot : NeurochemicalAtomicChemistrySlot
  functionalGroupSlot : NeurochemicalAtomicChemistrySlot
  spectralIdentitySlot : NeurochemicalAtomicChemistrySlot
  concentrationSlot : NeurochemicalAtomicChemistrySlot
  unitSlot : NeurochemicalAtomicChemistrySlot
  bindingSlot : NeurochemicalAtomicChemistrySlot
  kineticsSlot : NeurochemicalAtomicChemistrySlot

canonicalNeurochemicalAtomicChemistrySlots :
  List NeurochemicalAtomicChemistrySlot
canonicalNeurochemicalAtomicChemistrySlots =
  formulaSlot
  ∷ molecularGraphSlot
  ∷ chargeSlot
  ∷ protonationSlot
  ∷ stereochemistrySlot
  ∷ conformerSlot
  ∷ functionalGroupSlot
  ∷ spectralIdentitySlot
  ∷ concentrationSlot
  ∷ unitSlot
  ∷ bindingSlot
  ∷ kineticsSlot
  ∷ []

data NeurochemicalAtomicChemistryLane : Set where
  vocabularyReceiptLane : NeurochemicalAtomicChemistryLane
  bioactiveRecognitionLane : NeurochemicalAtomicChemistryLane
  quantitativeAdapterLane : NeurochemicalAtomicChemistryLane
  chemistryObligationLane : NeurochemicalAtomicChemistryLane
  formulaLane : NeurochemicalAtomicChemistryLane
  molecularGraphLane : NeurochemicalAtomicChemistryLane
  chargeLane : NeurochemicalAtomicChemistryLane
  protonationLane : NeurochemicalAtomicChemistryLane
  stereochemistryLane : NeurochemicalAtomicChemistryLane
  conformerLane : NeurochemicalAtomicChemistryLane
  functionalGroupLane : NeurochemicalAtomicChemistryLane
  spectralIdentityLane : NeurochemicalAtomicChemistryLane
  concentrationLane : NeurochemicalAtomicChemistryLane
  unitLane : NeurochemicalAtomicChemistryLane
  bindingLane : NeurochemicalAtomicChemistryLane
  kineticsLane : NeurochemicalAtomicChemistryLane

canonicalNeurochemicalAtomicChemistryLanes :
  List NeurochemicalAtomicChemistryLane
canonicalNeurochemicalAtomicChemistryLanes =
  vocabularyReceiptLane
  ∷ bioactiveRecognitionLane
  ∷ quantitativeAdapterLane
  ∷ chemistryObligationLane
  ∷ formulaLane
  ∷ molecularGraphLane
  ∷ chargeLane
  ∷ protonationLane
  ∷ stereochemistryLane
  ∷ conformerLane
  ∷ functionalGroupLane
  ∷ spectralIdentityLane
  ∷ concentrationLane
  ∷ unitLane
  ∷ bindingLane
  ∷ kineticsLane
  ∷ []

data NeurochemicalAtomicChemistryGuard : Set where
  NoMolecularIdentityAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoBindingAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoConcentrationAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoDoseResponseAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoPharmacologicalAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoClinicalAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoTherapeuticAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoDiagnosticAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoBiomarkerAuthorityClaim : NeurochemicalAtomicChemistryGuard
  NoReceiptlessPromotionClaim : NeurochemicalAtomicChemistryGuard

canonicalNeurochemicalAtomicChemistryGuards :
  List NeurochemicalAtomicChemistryGuard
canonicalNeurochemicalAtomicChemistryGuards =
  NoMolecularIdentityAuthorityClaim
  ∷ NoBindingAuthorityClaim
  ∷ NoConcentrationAuthorityClaim
  ∷ NoDoseResponseAuthorityClaim
  ∷ NoPharmacologicalAuthorityClaim
  ∷ NoClinicalAuthorityClaim
  ∷ NoTherapeuticAuthorityClaim
  ∷ NoDiagnosticAuthorityClaim
  ∷ NoBiomarkerAuthorityClaim
  ∷ NoReceiptlessPromotionClaim
  ∷ []

data NeurochemicalAtomicChemistryRoute : Set where
  boundedAtomicChemistryReceiptRoute : NeurochemicalAtomicChemistryRoute
  molecularIdentityAuthorityRoute : NeurochemicalAtomicChemistryRoute
  bindingAuthorityRoute : NeurochemicalAtomicChemistryRoute
  concentrationAuthorityRoute : NeurochemicalAtomicChemistryRoute
  doseResponseAuthorityRoute : NeurochemicalAtomicChemistryRoute
  pharmacologicalAuthorityRoute : NeurochemicalAtomicChemistryRoute
  clinicalAuthorityRoute : NeurochemicalAtomicChemistryRoute
  therapeuticAuthorityRoute : NeurochemicalAtomicChemistryRoute
  diagnosticAuthorityRoute : NeurochemicalAtomicChemistryRoute
  biomarkerAuthorityRoute : NeurochemicalAtomicChemistryRoute

AdmissibleNeurochemicalAtomicChemistryRoute :
  NeurochemicalAtomicChemistryRoute → Set
AdmissibleNeurochemicalAtomicChemistryRoute
  boundedAtomicChemistryReceiptRoute = ⊤
AdmissibleNeurochemicalAtomicChemistryRoute molecularIdentityAuthorityRoute =
  Never
AdmissibleNeurochemicalAtomicChemistryRoute bindingAuthorityRoute = Never
AdmissibleNeurochemicalAtomicChemistryRoute concentrationAuthorityRoute =
  Never
AdmissibleNeurochemicalAtomicChemistryRoute doseResponseAuthorityRoute =
  Never
AdmissibleNeurochemicalAtomicChemistryRoute pharmacologicalAuthorityRoute =
  Never
AdmissibleNeurochemicalAtomicChemistryRoute clinicalAuthorityRoute = Never
AdmissibleNeurochemicalAtomicChemistryRoute therapeuticAuthorityRoute = Never
AdmissibleNeurochemicalAtomicChemistryRoute diagnosticAuthorityRoute = Never
AdmissibleNeurochemicalAtomicChemistryRoute biomarkerAuthorityRoute = Never

molecularIdentityAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute
    molecularIdentityAuthorityRoute →
  Never
molecularIdentityAuthorityRejected impossible = impossible

bindingAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute bindingAuthorityRoute →
  Never
bindingAuthorityRejected impossible = impossible

concentrationAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute concentrationAuthorityRoute →
  Never
concentrationAuthorityRejected impossible = impossible

doseResponseAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute doseResponseAuthorityRoute →
  Never
doseResponseAuthorityRejected impossible = impossible

pharmacologicalAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute
    pharmacologicalAuthorityRoute →
  Never
pharmacologicalAuthorityRejected impossible = impossible

clinicalAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible = impossible

therapeuticAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute therapeuticAuthorityRoute →
  Never
therapeuticAuthorityRejected impossible = impossible

diagnosticAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute diagnosticAuthorityRoute →
  Never
diagnosticAuthorityRejected impossible = impossible

biomarkerAuthorityRejected :
  AdmissibleNeurochemicalAtomicChemistryRoute biomarkerAuthorityRoute →
  Never
biomarkerAuthorityRejected impossible = impossible

------------------------------------------------------------------------
-- Candidate-only atomic chemistry surface.

record NeurochemicalAtomicChemistrySurface : Set₁ where
  field
    FormulaCandidate : Set
    MolecularGraphCandidate : Set
    ChargeCandidate : Set
    ProtonationCandidate : Set
    StereochemistryCandidate : Set
    ConformerCandidate : Set
    FunctionalGroupCandidate : Set
    SpectralIdentityCandidate : Set
    ConcentrationCandidate : Set
    UnitCandidate : Set
    BindingCandidate : Set
    KineticsCandidate : Set
    ObservationTrace : Set
    Receipt : Set
    BoundedAtomicChemistryMeaning : Set

    formulaCandidateFromTrace :
      ObservationTrace → FormulaCandidate

    molecularGraphCandidateFromTrace :
      ObservationTrace → MolecularGraphCandidate

    chargeCandidateFromTrace :
      ObservationTrace → ChargeCandidate

    protonationCandidateFromTrace :
      ObservationTrace → ProtonationCandidate

    stereochemistryCandidateFromTrace :
      ObservationTrace → StereochemistryCandidate

    conformerCandidateFromTrace :
      ObservationTrace → ConformerCandidate

    functionalGroupCandidateFromTrace :
      ObservationTrace → FunctionalGroupCandidate

    spectralIdentityCandidateFromTrace :
      ObservationTrace → SpectralIdentityCandidate

    concentrationCandidateFromTrace :
      ObservationTrace → ConcentrationCandidate

    unitCandidateFromTrace :
      ObservationTrace → UnitCandidate

    bindingCandidateFromTrace :
      ObservationTrace → BindingCandidate

    kineticsCandidateFromTrace :
      ObservationTrace → KineticsCandidate

    observedSlots :
      ObservationTrace → List NeurochemicalAtomicChemistrySlot

    admissibilityReceipt :
      ObservationTrace → Receipt

    receiptGate :
      ObservationTrace → Receipt → Set

    promoteBoundedAtomicChemistryMeaning :
      ObservationTrace → Receipt → BoundedAtomicChemistryMeaning

    nonPromotionGuards :
      List NeurochemicalAtomicChemistryGuard

    surfaceReading :
      String

open NeurochemicalAtomicChemistrySurface public

------------------------------------------------------------------------
-- Whole bridge.

record NeurochemicalAtomicChemistryBridge : Set₁ where
  field
    vocabularyRows :
      List CandidateOnly.CandidateOnlyRow

    vocabularyRowsAreCanonical :
      vocabularyRows ≡ Vocabulary.canonicalNeurochemicalVocabularyRows

    vocabularyRowsCandidateOnly :
      CandidateOnly.AllRowsCandidateOnly vocabularyRows

    vocabularyRowsPromotedFalse :
      CandidateOnly.AllRowsPromotedFalse vocabularyRows

    bioactiveRecognitionBridge :
      Bioactive.BioactiveMolecularRecognitionBridge

    bioactiveRecognitionBridgeIsCanonical :
      bioactiveRecognitionBridge
      ≡
      Bioactive.canonicalBioactiveMolecularRecognitionBridge

    bioactiveClinicalAuthorityFalse :
      Bioactive.BioactiveMolecularRecognitionBridge.clinicalAuthorityClaimFlag
        bioactiveRecognitionBridge
      ≡
      false

    bioactiveDoseResponseAuthorityFalse :
      Bioactive.BioactiveMolecularRecognitionBridge.doseResponseAuthorityClaimFlag
        bioactiveRecognitionBridge
      ≡
      false

    bioactiveBiomarkerAuthorityFalse :
      Bioactive.BioactiveMolecularRecognitionBridge.biomarkerAuthorityClaimFlag
        bioactiveRecognitionBridge
      ≡
      false

    chemistryQuantitativeAdapter :
      Quant.ChemistryQuantitativeAdapter

    chemistryQuantitativeAdapterIsCanonical :
      chemistryQuantitativeAdapter
      ≡
      Quant.canonicalChemistryQuantitativeAdapter

    chemistryQuantitativeAdapterPhysicalChemistryFalse :
      Quant.ChemistryQuantitativeAdapter.physicalChemistryPromoted
        chemistryQuantitativeAdapter
      ≡
      false

    chemistryQuantitativeAdapterSpectroscopyFalse :
      Quant.ChemistryQuantitativeAdapter.spectroscopyPromoted
        chemistryQuantitativeAdapter
      ≡
      false

    chemistryQuantitativeAdapterBondingFalse :
      Quant.ChemistryQuantitativeAdapter.bondingInterpretationPromoted
        chemistryQuantitativeAdapter
      ≡
      false

    chemistryQuantitativeAdapterWetLabFalse :
      Quant.ChemistryQuantitativeAdapter.wetLabValidationAccepted
        chemistryQuantitativeAdapter
      ≡
      false

    chemistryBiologyObligationIndex :
      ChemBio.ChemistryBiologyPromotionObligationIndex

    chemistryBiologyObligationIndexIsCanonical :
      chemistryBiologyObligationIndex
      ≡
      ChemBio.canonicalChemistryBiologyPromotionObligationIndex

    atomicChemistrySurface :
      NeurochemicalAtomicChemistrySurface

    lanes :
      List NeurochemicalAtomicChemistryLane

    lanesAreCanonical :
      lanes ≡ canonicalNeurochemicalAtomicChemistryLanes

    guards :
      List NeurochemicalAtomicChemistryGuard

    guardsAreCanonical :
      guards ≡ canonicalNeurochemicalAtomicChemistryGuards

    route :
      NeurochemicalAtomicChemistryRoute

    routeIsBounded :
      route ≡ boundedAtomicChemistryReceiptRoute

    routeAdmissible :
      AdmissibleNeurochemicalAtomicChemistryRoute route

    molecularIdentityAuthority :
      Bool

    molecularIdentityAuthorityIsFalse :
      molecularIdentityAuthority ≡ false

    bindingAuthority :
      Bool

    bindingAuthorityIsFalse :
      bindingAuthority ≡ false

    concentrationAuthority :
      Bool

    concentrationAuthorityIsFalse :
      concentrationAuthority ≡ false

    doseResponseAuthority :
      Bool

    doseResponseAuthorityIsFalse :
      doseResponseAuthority ≡ false

    pharmacologicalAuthority :
      Bool

    pharmacologicalAuthorityIsFalse :
      pharmacologicalAuthority ≡ false

    clinicalAuthority :
      Bool

    clinicalAuthorityIsFalse :
      clinicalAuthority ≡ false

    therapeuticAuthority :
      Bool

    therapeuticAuthorityIsFalse :
      therapeuticAuthority ≡ false

    diagnosticAuthority :
      Bool

    diagnosticAuthorityIsFalse :
      diagnosticAuthority ≡ false

    biomarkerAuthority :
      Bool

    biomarkerAuthorityIsFalse :
      biomarkerAuthority ≡ false

    bridgeReading :
      String

open NeurochemicalAtomicChemistryBridge public

------------------------------------------------------------------------
-- Canonical inhabitant.

canonicalNeurochemicalAtomicChemistrySurface :
  NeurochemicalAtomicChemistrySurface
canonicalNeurochemicalAtomicChemistrySurface = record
  { FormulaCandidate = ⊤
  ; MolecularGraphCandidate = ⊤
  ; ChargeCandidate = ⊤
  ; ProtonationCandidate = ⊤
  ; StereochemistryCandidate = ⊤
  ; ConformerCandidate = ⊤
  ; FunctionalGroupCandidate = ⊤
  ; SpectralIdentityCandidate = ⊤
  ; ConcentrationCandidate = ⊤
  ; UnitCandidate = ⊤
  ; BindingCandidate = ⊤
  ; KineticsCandidate = ⊤
  ; ObservationTrace = ⊤
  ; Receipt = ⊤
  ; BoundedAtomicChemistryMeaning = ⊤
  ; formulaCandidateFromTrace = λ _ -> tt
  ; molecularGraphCandidateFromTrace = λ _ -> tt
  ; chargeCandidateFromTrace = λ _ -> tt
  ; protonationCandidateFromTrace = λ _ -> tt
  ; stereochemistryCandidateFromTrace = λ _ -> tt
  ; conformerCandidateFromTrace = λ _ -> tt
  ; functionalGroupCandidateFromTrace = λ _ -> tt
  ; spectralIdentityCandidateFromTrace = λ _ -> tt
  ; concentrationCandidateFromTrace = λ _ -> tt
  ; unitCandidateFromTrace = λ _ -> tt
  ; bindingCandidateFromTrace = λ _ -> tt
  ; kineticsCandidateFromTrace = λ _ -> tt
  ; observedSlots = λ _ -> canonicalNeurochemicalAtomicChemistrySlots
  ; admissibilityReceipt = λ _ -> tt
  ; receiptGate = λ _ _ -> ⊤
  ; promoteBoundedAtomicChemistryMeaning = λ _ _ -> tt
  ; nonPromotionGuards = canonicalNeurochemicalAtomicChemistryGuards
  ; surfaceReading =
      "Neurochemical atomic chemistry is recorded as a candidate-only receipt surface over formula, graph, charge, protonation, stereochemistry, conformer, functional-group, spectral-identity, concentration, unit, binding, and kinetics slots; molecular identity, binding, concentration, dose-response, pharmacological, clinical, therapeutic, diagnostic, and biomarker authority remain blocked."
  }

canonicalNeurochemicalAtomicChemistryBridge :
  NeurochemicalAtomicChemistryBridge
canonicalNeurochemicalAtomicChemistryBridge = record
  { vocabularyRows =
      Vocabulary.canonicalNeurochemicalVocabularyRows
  ; vocabularyRowsAreCanonical =
      refl
  ; vocabularyRowsCandidateOnly =
      Vocabulary.canonicalNeurochemicalVocabularyRowsCandidateOnly
  ; vocabularyRowsPromotedFalse =
      Vocabulary.canonicalNeurochemicalVocabularyRowsPromotedFalse
  ; bioactiveRecognitionBridge =
      Bioactive.canonicalBioactiveMolecularRecognitionBridge
  ; bioactiveRecognitionBridgeIsCanonical =
      refl
  ; bioactiveClinicalAuthorityFalse =
      refl
  ; bioactiveDoseResponseAuthorityFalse =
      refl
  ; bioactiveBiomarkerAuthorityFalse =
      refl
  ; chemistryQuantitativeAdapter =
      Quant.canonicalChemistryQuantitativeAdapter
  ; chemistryQuantitativeAdapterIsCanonical =
      refl
  ; chemistryQuantitativeAdapterPhysicalChemistryFalse =
      refl
  ; chemistryQuantitativeAdapterSpectroscopyFalse =
      refl
  ; chemistryQuantitativeAdapterBondingFalse =
      refl
  ; chemistryQuantitativeAdapterWetLabFalse =
      refl
  ; chemistryBiologyObligationIndex =
      ChemBio.canonicalChemistryBiologyPromotionObligationIndex
  ; chemistryBiologyObligationIndexIsCanonical =
      refl
  ; atomicChemistrySurface =
      canonicalNeurochemicalAtomicChemistrySurface
  ; lanes =
      canonicalNeurochemicalAtomicChemistryLanes
  ; lanesAreCanonical =
      refl
  ; guards =
      canonicalNeurochemicalAtomicChemistryGuards
  ; guardsAreCanonical =
      refl
  ; route =
      boundedAtomicChemistryReceiptRoute
  ; routeIsBounded =
      refl
  ; routeAdmissible =
      tt
  ; molecularIdentityAuthority =
      false
  ; molecularIdentityAuthorityIsFalse =
      refl
  ; bindingAuthority =
      false
  ; bindingAuthorityIsFalse =
      refl
  ; concentrationAuthority =
      false
  ; concentrationAuthorityIsFalse =
      refl
  ; doseResponseAuthority =
      false
  ; doseResponseAuthorityIsFalse =
      refl
  ; pharmacologicalAuthority =
      false
  ; pharmacologicalAuthorityIsFalse =
      refl
  ; clinicalAuthority =
      false
  ; clinicalAuthorityIsFalse =
      refl
  ; therapeuticAuthority =
      false
  ; therapeuticAuthorityIsFalse =
      refl
  ; diagnosticAuthority =
      false
  ; diagnosticAuthorityIsFalse =
      refl
  ; biomarkerAuthority =
      false
  ; biomarkerAuthorityIsFalse =
      refl
  ; bridgeReading =
      "Candidate-only neurochemical atomic chemistry bridge: vocabulary and bioactive recognition are carried into atomic quantitative slotting, while molecular identity, binding, concentration, dose-response, pharmacological, clinical, therapeutic, diagnostic, and biomarker authority stay blocked."
  }
