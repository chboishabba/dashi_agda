module DASHI.Physics.MaiwaldActionSpectroscopyScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- MAIWALD / CRYOGENIC ION ACTION SPECTROSCOPY SCIENCE
------------------------------------------------------------------------

data ActionSpectroscopyStage : Set where
  electrosprayIonisation
  ionGuiding
  cryogenicTrapping
  bufferGasCooling
  messengerTagging
  massSelection
  tunableIRExcitation
  photodissociation
  fragmentMassDetection
  spectrumReconstruction
  structureAssignment
  : ActionSpectroscopyStage

record ActionSpectroscopyChain : Set where
  constructor action-spectroscopy-chain
  field
    stages : List ActionSpectroscopyStage
    sourceReference : String
    boundedReading : String

open ActionSpectroscopyChain public

canonicalActionSpectroscopyChain : ActionSpectroscopyChain
canonicalActionSpectroscopyChain = action-spectroscopy-chain
  ( electrosprayIonisation
  ∷ ionGuiding
  ∷ cryogenicTrapping
  ∷ bufferGasCooling
  ∷ messengerTagging
  ∷ massSelection
  ∷ tunableIRExcitation
  ∷ photodissociation
  ∷ fragmentMassDetection
  ∷ spectrumReconstruction
  ∷ structureAssignment
  ∷ [] )
  "JPL FY23 SURP poster SP23012p, Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "The public JPL poster explicitly describes the experimental chain from ESI through cryogenic messenger tagging, IR photodissociation and fragment-ion detection."

photodissociationMechanism : S.ScientificMechanismReceipt
photodissociationMechanism = S.scientific-mechanism-receipt
  "messenger photodissociation action spectroscopy"
  "a mass-selected tagged ion absorbs resonant IR light; absorption can eject the weakly bound messenger, and the fragment yield as a function of photon energy traces a vibrational action spectrum"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "JPL SP23012p"
  "The measured action spectrum is weighted by the dissociation quantum yield; it is not automatically identical to a linear absorption cross-section spectrum."

isomerDiscriminationReceipt : S.ScientificMechanismReceipt
isomerDiscriminationReceipt = S.scientific-mechanism-receipt
  "valine versus aminovaleric-acid biosignature discrimination"
  "mass-selected ions with the same nominal mass/composition can exhibit distinct vibrational fingerprints, allowing structural-isomer discrimination beyond mass spectrometry alone"
  S.experimentalObservation
  S.sourceBacked
  "JPL SP23012p, comparison of deprotonated valine and aminovaleric acid"
  "This supports the value of coupling vibrational structure information to mass selection; it does not establish universal biosignature specificity in arbitrary planetary mixtures."

dftAssignmentReceipt : S.ScientificMechanismReceipt
dftAssignmentReceipt = S.scientific-mechanism-receipt
  "ValH+ structure assignment"
  "density-functional calculations using B3LYP/cc-pVTZ were compared with experimental spectra to support assignment of the lower-energy trans structural family"
  S.sourceInterpretation
  S.sourceBacked
  "JPL SP23012p"
  "Agreement between calculated and experimental spectra supports a structural assignment but remains method- and conformer-model dependent."

messengerTagTradeoff : S.ScientificMechanismReceipt
messengerTagTradeoff = S.scientific-mechanism-receipt
  "cryogenic messenger tagging"
  "the tag must bind strongly enough to form a stable complex at the operating temperature but weakly enough that resonant absorption yields detectable tag loss"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "JPL SP23012p discussion of N2, H2O and CH4 binding/temperature behaviour"
  "Messenger choice couples thermodynamic stability, accessible planetary-temperature regimes and photodissociation quantum yield."

actionSpectroscopyNeedsMixtureValidation : S.ScientificReverseObligation
actionSpectroscopyNeedsMixtureValidation = S.scientific-reverse-obligation
  "planetary biosignature identification by action spectroscopy"
  S.benchmarkReceipt
  "test selectivity, sensitivity, dynamic range and false-positive behaviour in complex mixtures, relevant salts/matrices, radiation histories and mission-relevant temperatures"
  "instrument-level biosignature discrimination performance in realistic planetary samples"
  "unambiguous life detection merely from clean laboratory isomer discrimination"

record CurrentMaiwaldScienceAssessment : Set where
  constructor current-maiwald-science-assessment
  field
    experimentalChainOwned : Bool
    experimentalChainOwnedIsTrue : experimentalChainOwned ≡ true
    isomerDiscriminationOwned : Bool
    isomerDiscriminationOwnedIsTrue : isomerDiscriminationOwned ≡ true
    missionMixtureValidationClosed : Bool
    missionMixtureValidationClosedIsFalse : missionMixtureValidationClosed ≡ false

canonicalCurrentMaiwaldScienceAssessment : CurrentMaiwaldScienceAssessment
canonicalCurrentMaiwaldScienceAssessment = current-maiwald-science-assessment
  true refl
  true refl
  false refl
