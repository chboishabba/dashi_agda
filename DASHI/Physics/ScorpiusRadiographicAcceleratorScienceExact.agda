module DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- DARHT / SCORPIUS RADIOGRAPHIC ACCELERATOR SCIENCE
------------------------------------------------------------------------

data RadiographyStage : Set where
  pulsedPower
  electronInjection
  inductionAcceleration
  beamTransport
  targetConversion
  xRayPulse
  objectTransmission
  detectorImage
  hydrodynamicInference
  : RadiographyStage

record RadiographyChain : Set where
  constructor radiography-chain
  field
    stages : List RadiographyStage
    sourceReference : String
    boundedReading : String

open RadiographyChain public

scorpiusRadiographyChain : RadiographyChain
scorpiusRadiographyChain = radiography-chain
  ( pulsedPower
  ∷ electronInjection
  ∷ inductionAcceleration
  ∷ beamTransport
  ∷ targetConversion
  ∷ xRayPulse
  ∷ objectTransmission
  ∷ detectorImage
  ∷ hydrodynamicInference
  ∷ [] )
  "LANL/NNSA public DARHT and Scorpius engineering descriptions"
  "The chain captures the public accelerator-to-radiograph mechanism: a high-current electron beam is accelerated, converted to an intense x-ray pulse at a target, and used for time-resolved radiography of dynamic experiments."

inductionAccelerationReceipt : S.ScientificMechanismReceipt
inductionAccelerationReceipt = S.scientific-mechanism-receipt
  "DARHT/Scorpius linear induction accelerator"
  "successive induction cells add accelerating voltage to a high-current electron beam while beam transport elements control the beam through the accelerator"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "LANL/NNSA public accelerator architecture material"
  "This is the public engineering principle of a linear induction accelerator, not a release of classified experiment-specific weapons-design data."

bremsstrahlungReceipt : S.ScientificMechanismReceipt
bremsstrahlungReceipt = S.scientific-mechanism-receipt
  "hydrodynamic radiography"
  "the accelerated electron beam strikes a conversion target to generate an intense bremsstrahlung x-ray pulse used to image dense dynamic objects"
  S.establishedBackgroundLaw
  S.established
  "standard accelerator-radiography mechanism; LANL/NNSA DARHT/Scorpius descriptions"
  "The x-ray generation and attenuation physics are conventional; classified or bounded content can reside in the experiment geometry, material state, timing, diagnostics and downstream inference."

multiPulseReceipt : S.ScientificMechanismReceipt
multiPulseReceipt = S.scientific-mechanism-receipt
  "DARHT/Scorpius radiography"
  "multiple temporally separated x-ray pulses provide time-resolved views of a rapidly evolving experiment"
  S.constitutiveOrEngineeringMechanism
  S.sourceBacked
  "LANL/NNSA DARHT and Scorpius public material"
  "Multiple images constrain dynamic evolution; they do not by themselves identify material constitutive behaviour without a forward/inverse model."

scorpiusNeedsInverseModelReceipt : S.ScientificReverseObligation
scorpiusNeedsInverseModelReceipt = S.scientific-reverse-obligation
  "radiograph -> hydrodynamic/material-state inference"
  S.mechanismToObservationWeld
  "recover detector response, source spectrum, geometry, attenuation model, reconstruction/inversion procedure and uncertainty propagation for a particular experiment"
  "what physical state is actually constrained by the radiographic data"
  "complete weapons-design information merely from public accelerator architecture"

record CurrentScorpiusScienceAssessment : Set where
  constructor current-scorpius-science-assessment
  field
    acceleratorChainOwned : Bool
    acceleratorChainOwnedIsTrue : acceleratorChainOwned ≡ true
    xRayConversionMechanismOwned : Bool
    xRayConversionMechanismOwnedIsTrue : xRayConversionMechanismOwned ≡ true
    experimentSpecificInverseProblemClosed : Bool
    experimentSpecificInverseProblemClosedIsFalse :
      experimentSpecificInverseProblemClosed ≡ false

canonicalCurrentScorpiusScienceAssessment : CurrentScorpiusScienceAssessment
canonicalCurrentScorpiusScienceAssessment = current-scorpius-science-assessment
  true refl
  true refl
  false refl
