module DASHI.Chemistry.ChlorAlkaliHalfReactionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Geology.SaltConservationSpineExact as SaltConservation
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- CHLOR-ALKALI HALF-REACTION / ELECTRON ACCOUNTING
--
-- Canonical membrane/diaphragm-cell bookkeeping at the reaction level:
--
--   anode:   2 Cl- -> Cl2 + 2 e-
--   cathode: 2 H2O + 2 e- -> H2 + 2 OH-
--
-- with Na+ carried across the separator/electrolyte bookkeeping to yield
-- product NaOH.  This owner proves coefficient/electron compatibility and
-- deliberately does not claim one universal cell technology.
------------------------------------------------------------------------

electronSpecies : Chemistry.Species
electronSpecies = record
  { Chemistry.speciesId = "electron"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "-1 elementary charge"
  ; Chemistry.compositionLabel = "e-"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "electrode electron bookkeeping carrier"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

hydroxideIonSpecies : Chemistry.Species
hydroxideIonSpecies = record
  { Chemistry.speciesId = "hydroxide ion"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "-1"
  ; Chemistry.compositionLabel = "OH-"
  ; Chemistry.mobilityClass = Chemistry.mobile
  ; Chemistry.activityModelLabel = "aqueous electrolyte activity model supplied by application"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

record ElectrodeHalfReactionReceipt : Set₁ where
  constructor electrodeHalfReactionReceipt
  field
    transition : Chemistry.Transition
    electronMultiplicity : Nat
    electronBalanceReference : String
    electrodePotentialReference : String
    kineticsReference : String
    electrodeMaterialReference : String
    validationReference : String

open ElectrodeHalfReactionReceipt public

record ChlorAlkaliElectronWeld
    (lineage : Salt.SaltMaterialLineage)
    (production : Industry.ChlorAlkaliProductionReceipt lineage) : Set₁ where
  constructor chlorAlkaliElectronWeld
  field
    saltConservation : SaltConservation.SaltCrossDomainConservationSpine lineage
    anode : ElectrodeHalfReactionReceipt
    cathode : ElectrodeHalfReactionReceipt

    anodeElectronMultiplicityIsTwo : electronMultiplicity anode ≡ 2
    cathodeElectronMultiplicityIsTwo : electronMultiplicity cathode ≡ 2

    chlorideFeedIsLineageChloride :
      Industry.chlorideFeedSpecies (Industry.feedWeld production)
      ≡ Salt.chlorideSpecies (Salt.brine lineage)

    sodiumFeedIsLineageSodium :
      Industry.sodiumFeedSpecies (Industry.feedWeld production)
      ≡ Salt.sodiumSpecies (Salt.brine lineage)

    chlorineProductIsCanonical :
      Industry.chlorineProduct production ≡ Industry.chlorineGasSpecies
    hydrogenProductIsCanonical :
      Industry.hydrogenProduct production ≡ Industry.hydrogenGasSpecies
    causticProductIsCanonical :
      Industry.causticProduct production ≡ Industry.sodiumHydroxideSpecies

    separatorIonTransportReference : String
    sodiumHydroxideAssemblyReference : String
    halfReactionSumEqualsOverallReference : String
    chargeConservationReference : String
    atomConservationReference : String

open ChlorAlkaliElectronWeld public

------------------------------------------------------------------------
-- Explicit anti-collapse boundary.
------------------------------------------------------------------------

record ChlorAlkaliHalfReactionBoundary : Set where
  constructor chlorAlkaliHalfReactionBoundary
  field
    overallReactionAloneProvesElectronPath : Bool
    overallReactionAloneProvesElectronPathIsFalse :
      overallReactionAloneProvesElectronPath ≡ false

    equalElectronMultiplicityProvesEqualElectrodeKinetics : Bool
    equalElectronMultiplicityProvesEqualElectrodeKineticsIsFalse :
      equalElectronMultiplicityProvesEqualElectrodeKinetics ≡ false

    sodiumIsOxidisedAtAnode : Bool
    sodiumIsOxidisedAtAnodeIsFalse : sodiumIsOxidisedAtAnode ≡ false

    chlorideMaterialContinuityMustBeSharedWithSaltSpine : Bool
    chlorideMaterialContinuityMustBeSharedWithSaltSpineIsTrue :
      chlorideMaterialContinuityMustBeSharedWithSaltSpine ≡ true

canonicalChlorAlkaliHalfReactionBoundary : ChlorAlkaliHalfReactionBoundary
canonicalChlorAlkaliHalfReactionBoundary =
  chlorAlkaliHalfReactionBoundary false refl false refl false refl true refl
