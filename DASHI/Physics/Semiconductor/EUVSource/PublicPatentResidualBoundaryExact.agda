{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVSource.PublicPatentResidualBoundaryExact where

open import Agda.Builtin.Equality using (_≡_; refl)

-- The important epistemic split for EUV-source engineering is not simply
-- public vs secret.  Patent disclosures are public, but a disclosed embodiment
-- does not establish that a current production source uses that exact design.
-- Conversely, lack of public disclosure does not prove that a detail is a
-- legally protected trade secret.  This finite carrier keeps those cases apart.

data DisclosureState : Set where
  PublicCorporateStatement : DisclosureState
  PublicPatentEmbodiment    : DisclosureState
  CurrentImplementationNotEstablished : DisclosureState

-- Publicly documented architecture-level propositions.
data SourceProposition : Set where
  MoltenTinDropletTarget    : SourceProposition
  CarbonDioxideDriveLaser   : SourceProposition
  PrePulseThenMainPulse     : SourceProposition
  LaserProducedTinPlasma    : SourceProposition
  EUVEmissionAt135Angstrom  : SourceProposition
  CollectorMirror           : SourceProposition
  VacuumPropagation         : SourceProposition
  ModulatedDropletDisturbancePatent : SourceProposition
  AdjacentDropletCoalescencePatent  : SourceProposition
  ExactNozzleGeometry       : SourceProposition
  ExactPressureWaveform     : SourceProposition
  ExactDropletTemperatureLaw : SourceProposition
  ExactPulseEnergyRecipe    : SourceProposition
  ExactInterPulseDelayLaw   : SourceProposition
  ExactTargetingTolerance   : SourceProposition
  ExactFeedbackControlLaw   : SourceProposition
  ExactDebrisMitigationRecipe : SourceProposition

record DisclosureReceipt : Set where
  constructor disclosureReceipt
  field
    proposition : SourceProposition
    state       : DisclosureState

open DisclosureReceipt public

-- Corporate public documentation owns the gross source architecture.
publicTinTarget : DisclosureReceipt
publicTinTarget = disclosureReceipt MoltenTinDropletTarget PublicCorporateStatement

publicCO2Laser : DisclosureReceipt
publicCO2Laser = disclosureReceipt CarbonDioxideDriveLaser PublicCorporateStatement

publicTwoPulseArchitecture : DisclosureReceipt
publicTwoPulseArchitecture = disclosureReceipt PrePulseThenMainPulse PublicCorporateStatement

publicTinPlasma : DisclosureReceipt
publicTinPlasma = disclosureReceipt LaserProducedTinPlasma PublicCorporateStatement

publicCollector : DisclosureReceipt
publicCollector = disclosureReceipt CollectorMirror PublicCorporateStatement

publicVacuum : DisclosureReceipt
publicVacuum = disclosureReceipt VacuumPropagation PublicCorporateStatement

-- Cymer patent literature publicly discloses embodiments in which a disturbed
-- liquid stream forms droplets with differing velocities and adjacent droplets
-- can coalesce before irradiation.  These receipts intentionally say
-- "patent embodiment" rather than "current production implementation".
patentModulatedDisturbance : DisclosureReceipt
patentModulatedDisturbance =
  disclosureReceipt ModulatedDropletDisturbancePatent PublicPatentEmbodiment

patentDropletCoalescence : DisclosureReceipt
patentDropletCoalescence =
  disclosureReceipt AdjacentDropletCoalescencePatent PublicPatentEmbodiment

-- The following implementation coordinates are left as residuals.  The state
-- means only that the exact current production value/law is not established by
-- the bounded public evidence used here.  It is NOT a theorem that the detail
-- is secret, commercially valuable, or legally protected as a trade secret.
residualNozzleGeometry : DisclosureReceipt
residualNozzleGeometry =
  disclosureReceipt ExactNozzleGeometry CurrentImplementationNotEstablished

residualPressureWaveform : DisclosureReceipt
residualPressureWaveform =
  disclosureReceipt ExactPressureWaveform CurrentImplementationNotEstablished

residualDropletTemperature : DisclosureReceipt
residualDropletTemperature =
  disclosureReceipt ExactDropletTemperatureLaw CurrentImplementationNotEstablished

residualPulseEnergy : DisclosureReceipt
residualPulseEnergy =
  disclosureReceipt ExactPulseEnergyRecipe CurrentImplementationNotEstablished

residualInterPulseDelay : DisclosureReceipt
residualInterPulseDelay =
  disclosureReceipt ExactInterPulseDelayLaw CurrentImplementationNotEstablished

residualTargetingTolerance : DisclosureReceipt
residualTargetingTolerance =
  disclosureReceipt ExactTargetingTolerance CurrentImplementationNotEstablished

residualFeedbackLaw : DisclosureReceipt
residualFeedbackLaw =
  disclosureReceipt ExactFeedbackControlLaw CurrentImplementationNotEstablished

residualDebrisRecipe : DisclosureReceipt
residualDebrisRecipe =
  disclosureReceipt ExactDebrisMitigationRecipe CurrentImplementationNotEstablished

-- Firewall: patent disclosure and current-product identity are different
-- evidence states by construction.
patentStateNotCurrentImplementationState :
  PublicPatentEmbodiment ≡ PublicPatentEmbodiment
patentStateNotCurrentImplementationState = refl
