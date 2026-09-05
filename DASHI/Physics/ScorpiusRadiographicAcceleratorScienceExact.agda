module DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

data RadiographyStage : Set where pulsedPower electronInjection inductionAcceleration beamTransport targetConversion xRayPulse objectTransmission detectorImage hydrodynamicInference : RadiographyStage
record RadiographyChain : Set where constructor radiography-chain; field stages : List RadiographyStage; sourceReference : String; boundedReading : String
open RadiographyChain public
scorpiusRadiographyChain = radiography-chain (pulsedPower ∷ electronInjection ∷ inductionAcceleration ∷ beamTransport ∷ targetConversion ∷ xRayPulse ∷ objectTransmission ∷ detectorImage ∷ hydrodynamicInference ∷ []) "LANL/NNSA public DARHT and Scorpius engineering descriptions" "Public accelerator-to-radiograph chain: high-current electrons are accelerated, converted to x rays, and used for time-resolved imaging of dynamic experiments."
inductionAccelerationReceipt : S.ScientificMechanismReceipt
inductionAccelerationReceipt = S.scientific-mechanism-receipt "DARHT/Scorpius linear induction accelerator" "successive induction cells add accelerating voltage to a high-current electron beam while beam-transport elements control propagation" S.constitutiveOrEngineeringMechanism S.sourceBacked "LANL/NNSA public accelerator architecture" "Public engineering principle, not release of classified experiment-specific design data."
bremsstrahlungReceipt : S.ScientificMechanismReceipt
bremsstrahlungReceipt = S.scientific-mechanism-receipt "hydrodynamic radiography" "the accelerated electron beam strikes a conversion target to generate an intense bremsstrahlung x-ray pulse for imaging dense dynamic objects" S.establishedBackgroundLaw S.established "standard accelerator-radiography mechanism; LANL/NNSA descriptions" "Sensitive content can reside in experiment geometry, material state, timing, diagnostics and downstream inference."
multiPulseReceipt : S.ScientificMechanismReceipt
multiPulseReceipt = S.scientific-mechanism-receipt "DARHT/Scorpius radiography" "multiple temporally separated x-ray pulses provide time-resolved views of a rapidly evolving experiment" S.constitutiveOrEngineeringMechanism S.sourceBacked "LANL/NNSA public material" "Multiple images constrain evolution but do not identify constitutive behaviour without a forward/inverse model."
scorpiusNeedsInverseModelReceipt : S.ScientificReverseObligation
scorpiusNeedsInverseModelReceipt = S.scientific-reverse-obligation "radiograph -> hydrodynamic/material-state inference" S.mechanismToObservationWeld "recover detector response, source spectrum, geometry, attenuation model, reconstruction/inversion and uncertainty propagation" "what physical state is constrained by a particular radiograph" "complete weapons-design information from public accelerator architecture"
record CurrentScorpiusScienceAssessment : Set where constructor current-scorpius-science-assessment; field acceleratorChainOwned : Bool; acceleratorChainOwnedIsTrue : acceleratorChainOwned ≡ true; xRayConversionMechanismOwned : Bool; xRayConversionMechanismOwnedIsTrue : xRayConversionMechanismOwned ≡ true; experimentSpecificInverseProblemClosed : Bool; experimentSpecificInverseProblemClosedIsFalse : experimentSpecificInverseProblemClosed ≡ false
canonicalCurrentScorpiusScienceAssessment = current-scorpius-science-assessment true refl true refl false refl
