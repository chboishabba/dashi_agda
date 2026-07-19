module DASHI.Chemistry.ExistingContentBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.NeurochemicalAtomicChemistryBridge as Neurochemical
import DASHI.Promotion.ChemistryBiologyObligations as ChemBio
import DASHI.Promotion.ChemistryQuantitativeAdapter as Quant
import DASHI.Chemistry.TransitionKernel as Kernel

------------------------------------------------------------------------
-- Explicit reuse map from pre-existing DASHI chemistry content.
--
-- The transition kernel adds spatial, temporal, hybrid-event, interface,
-- reachability, uncertainty, and reduction structure.  It does not replace
-- the existing quantitative-law, wet-lab, or authority boundaries.

data ExistingChemistryContent : Set where
  stoichiometryMoleculeCount
  lawOfMassAction
  beerLambertOptics
  nernstElectrochemistry
  spectroscopyObservable
  bondingPreservation
  wetLabReplication
  chemistryBiologyObligationIndex
  neurochemicalAtomicCandidateSurface : ExistingChemistryContent

record ExistingContentReference : Set where
  field
    content : ExistingChemistryContent
    existingModule : String
    existingCarrier : String
    consumedByNewKernel : String
    reuseMeaning : String

open ExistingContentReference public

canonicalExistingContentReferences : List ExistingContentReference
canonicalExistingContentReferences =
  record
    { content = stoichiometryMoleculeCount
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "StoichiometryMoleculeCountAdapter"
    ; consumedByNewKernel = "ConservationCertificate"
    ; reuseMeaning = "integer stoichiometry and atom/charge conservation remain the quantitative source surface"
    }
  ∷ record
    { content = lawOfMassAction
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "canonicalSymbolicLawCarriers: law of mass action"
    ; consumedByNewKernel = "RateLaw.massAction and Transition"
    ; reuseMeaning = "the kernel types the transition graph while the existing adapter governs quantitative authority"
    }
  ∷ record
    { content = beerLambertOptics
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "canonicalSymbolicLawCarriers: Beer-Lambert"
    ; consumedByNewKernel = "ObservableMap and instant-film optical observables"
    ; reuseMeaning = "absorbance observables reuse the established symbolic optical law carrier"
    }
  ∷ record
    { content = nernstElectrochemistry
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "canonicalSymbolicLawCarriers: Nernst equation"
    ; consumedByNewKernel = "environment-dependent transition applications"
    ; reuseMeaning = "electrochemical applications remain compatible without being baked into generic chemistry"
    }
  ∷ record
    { content = spectroscopyObservable
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "SpectroscopyObservableAdapter"
    ; consumedByNewKernel = "Species.opticalRoleLabel and ObservableMap"
    ; reuseMeaning = "spectral identity and instrument response remain externally receipted"
    }
  ∷ record
    { content = bondingPreservation
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "BondingInterpretationPreservationToken"
    ; consumedByNewKernel = "Species identity and ModelReduction invariant preservation"
    ; reuseMeaning = "model reduction cannot silently promote a bonding interpretation"
    }
  ∷ record
    { content = wetLabReplication
    ; existingModule = "DASHI.Promotion.ChemistryQuantitativeAdapter"
    ; existingCarrier = "WetLabProtocolReplicationReceipt"
    ; consumedByNewKernel = "ExperimentCandidate.protocolReceiptRequired"
    ; reuseMeaning = "every proposed discriminating experiment remains provenance and replication gated"
    }
  ∷ record
    { content = chemistryBiologyObligationIndex
    ; existingModule = "DASHI.Promotion.ChemistryBiologyObligations"
    ; existingCarrier = "ChemistryBiologyPromotionObligationIndex"
    ; consumedByNewKernel = "ChemistryTransitionKernel authority boundary"
    ; reuseMeaning = "biology-facing promotions remain blocked until the pre-existing obligations discharge"
    }
  ∷ record
    { content = neurochemicalAtomicCandidateSurface
    ; existingModule = "DASHI.Biology.NeurochemicalAtomicChemistryBridge"
    ; existingCarrier = "NeurochemicalAtomicChemistrySurface"
    ; consumedByNewKernel = "candidate species and kinetics evidence statuses"
    ; reuseMeaning = "candidate-only molecular identity, concentration, binding, and kinetics are preserved"
    }
  ∷ []

record ExistingChemistryBridge : Set₁ where
  field
    quantitativeAdapter : Quant.ChemistryQuantitativeAdapter
    quantitativeAdapterIsCanonical :
      quantitativeAdapter ≡ Quant.canonicalChemistryQuantitativeAdapter

    chemistryBiologyObligations :
      ChemBio.ChemistryBiologyPromotionObligationIndex
    chemistryBiologyObligationsAreCanonical :
      chemistryBiologyObligations
      ≡ ChemBio.canonicalChemistryBiologyPromotionObligationIndex

    neurochemicalBridge : Neurochemical.NeurochemicalAtomicChemistryBridge
    neurochemicalBridgeIsCanonical :
      neurochemicalBridge
      ≡ Neurochemical.canonicalNeurochemicalAtomicChemistryBridge

    references : List ExistingContentReference
    referencesAreCanonical :
      references ≡ canonicalExistingContentReferences

    physicalChemistryPromoted : Bool
    physicalChemistryPromotedIsFalse : physicalChemistryPromoted ≡ false

    wetLabValidationAccepted : Bool
    wetLabValidationAcceptedIsFalse : wetLabValidationAccepted ≡ false

open ExistingChemistryBridge public

canonicalExistingChemistryBridge : ExistingChemistryBridge
canonicalExistingChemistryBridge = record
  { quantitativeAdapter = Quant.canonicalChemistryQuantitativeAdapter
  ; quantitativeAdapterIsCanonical = refl
  ; chemistryBiologyObligations =
      ChemBio.canonicalChemistryBiologyPromotionObligationIndex
  ; chemistryBiologyObligationsAreCanonical = refl
  ; neurochemicalBridge =
      Neurochemical.canonicalNeurochemicalAtomicChemistryBridge
  ; neurochemicalBridgeIsCanonical = refl
  ; references = canonicalExistingContentReferences
  ; referencesAreCanonical = refl
  ; physicalChemistryPromoted = false
  ; physicalChemistryPromotedIsFalse = refl
  ; wetLabValidationAccepted = false
  ; wetLabValidationAcceptedIsFalse = refl
  }
