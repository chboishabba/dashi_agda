module DASHI.Physics.MaiwaldActionSpectroscopyScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

data ActionSpectroscopyStage : Set where electrosprayIonisation ionGuiding cryogenicTrapping bufferGasCooling messengerTagging massSelection tunableIRExcitation photodissociation fragmentMassDetection spectrumReconstruction structureAssignment : ActionSpectroscopyStage
record ActionSpectroscopyChain : Set where constructor action-spectroscopy-chain; field stages : List ActionSpectroscopyStage; sourceReference : String; boundedReading : String
open ActionSpectroscopyChain public
canonicalActionSpectroscopyChain = action-spectroscopy-chain (electrosprayIonisation ∷ ionGuiding ∷ cryogenicTrapping ∷ bufferGasCooling ∷ messengerTagging ∷ massSelection ∷ tunableIRExcitation ∷ photodissociation ∷ fragmentMassDetection ∷ spectrumReconstruction ∷ structureAssignment ∷ []) "JPL FY23 SURP poster SP23012p" "Public JPL chain from ESI through cryogenic tagging, IR photodissociation and fragment-ion detection."
photodissociationMechanism : S.ScientificMechanismReceipt
photodissociationMechanism = S.scientific-mechanism-receipt "messenger photodissociation action spectroscopy" "a mass-selected tagged ion absorbs resonant IR light; absorption can eject the weakly bound messenger, and fragment yield versus photon energy traces a vibrational action spectrum" S.constitutiveOrEngineeringMechanism S.sourceBacked "JPL SP23012p" "The action spectrum is weighted by dissociation quantum yield and is not automatically identical to a linear absorption cross-section spectrum."
isomerDiscriminationReceipt : S.ScientificMechanismReceipt
isomerDiscriminationReceipt = S.scientific-mechanism-receipt "valine versus aminovaleric-acid discrimination" "same-mass/composition ions can exhibit distinct vibrational fingerprints, adding structural-isomer discrimination beyond mass spectrometry alone" S.experimentalObservation S.sourceBacked "JPL SP23012p" "Supports mass+structure discrimination, not universal biosignature specificity in arbitrary planetary mixtures."
dftAssignmentReceipt : S.ScientificMechanismReceipt
dftAssignmentReceipt = S.scientific-mechanism-receipt "ValH+ structure assignment" "B3LYP/cc-pVTZ calculations were compared with experiment to support the lower-energy trans-family assignment" S.sourceInterpretation S.sourceBacked "JPL SP23012p" "Agreement supports assignment but remains method- and conformer-model dependent."
messengerTagTradeoff : S.ScientificMechanismReceipt
messengerTagTradeoff = S.scientific-mechanism-receipt "cryogenic messenger tagging" "the tag must bind strongly enough for stable complex formation yet weakly enough for resonant absorption to yield detectable tag loss" S.constitutiveOrEngineeringMechanism S.sourceBacked "JPL SP23012p" "Messenger choice couples temperature regime, stability and dissociation yield."
actionSpectroscopyNeedsMixtureValidation : S.ScientificReverseObligation
actionSpectroscopyNeedsMixtureValidation = S.scientific-reverse-obligation "planetary biosignature identification by action spectroscopy" S.benchmarkReceipt "test selectivity, sensitivity, dynamic range and false positives in complex mixtures, relevant matrices, radiation histories and mission temperatures" "instrument-level discrimination performance in realistic planetary samples" "unambiguous life detection from clean laboratory isomer discrimination"
record CurrentMaiwaldScienceAssessment : Set where constructor current-maiwald-science-assessment; field experimentalChainOwned : Bool; experimentalChainOwnedIsTrue : experimentalChainOwned ≡ true; isomerDiscriminationOwned : Bool; isomerDiscriminationOwnedIsTrue : isomerDiscriminationOwned ≡ true; missionMixtureValidationClosed : Bool; missionMixtureValidationClosedIsFalse : missionMixtureValidationClosed ≡ false
canonicalCurrentMaiwaldScienceAssessment = current-maiwald-science-assessment true refl true refl false refl
