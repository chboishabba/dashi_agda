module DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact where

------------------------------------------------------------------------
-- Source-facing biology:
-- Michael Levin, "Bioelectric signaling: Reprogrammable circuits underlying
-- embryogenesis, regeneration, and cancer", Cell 184 (2021), 1971-1989.
-- DOI: 10.1016/j.cell.2021.02.034.
--
-- This adapter makes the existing abstract BioelectricNetwork carrier
-- dimensionally concrete without changing its authority boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric

record SIState : Set where
  constructor siState
  field
    membraneVoltage : SI.Quantity SI.Voltage SI.milliScale
    junctionConductance : SI.Quantity SI.Conductance SI.nanoScale
    ionicCurrentMagnitude : SI.Quantity SI.Current SI.nanoScale

open SIState public

zeroVoltage : SI.Quantity SI.Voltage SI.milliScale
zeroVoltage = SI.zeroQ

zeroConductance : SI.Quantity SI.Conductance SI.nanoScale
zeroConductance = SI.zeroQ

zeroCurrent : SI.Quantity SI.Current SI.nanoScale
zeroCurrent = SI.zeroQ

canonicalSIState : SIState
canonicalSIState = siState zeroVoltage zeroConductance zeroCurrent

canonicalSIBioelectricNetwork : Bioelectric.BioelectricNetwork
canonicalSIBioelectricNetwork = record
  { Node = Bool
  ; Voltage = SI.Quantity SI.Voltage SI.milliScale
  ; Conductance = SI.Quantity SI.Conductance SI.nanoScale
  ; Current = SI.Quantity SI.Current SI.nanoScale
  ; ChannelState = Bool
  ; GapJunctionState = Bool
  ; ChemicalSignal = Bool
  ; MechanicalState = Bool
  ; RegulatoryState = Bool
  ; NetworkState = SIState
  ; Environment = Bool
  ; voltageAt = λ state node → membraneVoltage state
  ; coupling = λ state source target → junctionConductance state
  ; ionicCurrent = λ state node → ionicCurrentMagnitude state
  ; channelState = λ state node → node
  ; gapJunction = λ state source target → source
  ; update = λ environment chemical mechanical regulatory state → state
  }

canonicalVoltageCarrierIsMillivoltScaled :
  Bioelectric.BioelectricNetwork.Voltage canonicalSIBioelectricNetwork
    ≡ SI.Quantity SI.Voltage SI.milliScale
canonicalVoltageCarrierIsMillivoltScaled = refl

canonicalConductanceCarrierIsNanoScaled :
  Bioelectric.BioelectricNetwork.Conductance canonicalSIBioelectricNetwork
    ≡ SI.Quantity SI.Conductance SI.nanoScale
canonicalConductanceCarrierIsNanoScaled = refl

canonicalCurrentCarrierIsNanoScaled :
  Bioelectric.BioelectricNetwork.Current canonicalSIBioelectricNetwork
    ≡ SI.Quantity SI.Current SI.nanoScale
canonicalCurrentCarrierIsNanoScaled = refl
