module DASHI.Physics.Foundations.ResonantFlightAcoustomechanicalCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPhaseControlExact as Phase
import DASHI.Physics.Foundations.ResonantFlightEnergyNetworkExact as Energy
import DASHI.Physics.Foundations.ResonantFlightMechanicalImpedanceExact as Imp
import DASHI.Physics.Foundations.GoniometerPhasedArrayRFSensingCrossPollinationExact as RF

------------------------------------------------------------------------
-- Speaker/bass design and RF provide reusable *structural* analogies:
-- relative phase, impedance matching, reflected loading, and coupled
-- resonators.  This module does not identify acoustic, RF, and
-- aerodynamic physics; it records the common observation/control roles.
------------------------------------------------------------------------

data CouplingDomain : Set where
  radio acoustic mechanical aerodynamic : CouplingDomain

record CrossDomainRole : Set₁ where
  constructor cross-domain-role
  field
    Domain : Set
    Source Load State : Set
    source : Source
    load : Load
    state : State

open CrossDomainRole public

record SpeakerWingAnalogy : Set₁ where
  constructor speaker-wing-analogy
  field
    DriverMass WingInertia : Set
    SuspensionCompliance WingCompliance : Set
    RadiationLoad AerodynamicLoad : Set
    speakerDriver : DriverMass
    wingDriver : WingInertia

open SpeakerWingAnalogy public

record PhaseSelectiveMechanicalNetwork : Set₁ where
  constructor phase-selective-mechanical-network
  field
    Phase Input : Set
    Output : Set
    transfer : Phase → Input → Output

open PhaseSelectiveMechanicalNetwork public

record MechanicalCyclicBus : Set₁ where
  constructor mechanical-cyclic-bus
  field
    PilotInput Phase JointCommand : Set
    phaseControl : PilotInput → Phase → JointCommand

open MechanicalCyclicBus public

------------------------------------------------------------------------
-- Explicit semantic firewall: shared phase/impedance form does not make
-- RF array sensing, loudspeaker radiation, and flapping aerodynamics the
-- same physical theory.
------------------------------------------------------------------------

record CrossDomainIdentityFirewall : Set where
  constructor cross-domain-identity-firewall
  field
    rfEqualsAerodynamics : Bool
    rfEqualsAerodynamicsIsFalse : rfEqualsAerodynamics ≡ false
    acousticsEqualsAerodynamics : Bool
    acousticsEqualsAerodynamicsIsFalse : acousticsEqualsAerodynamics ≡ false
    analogyCreatesEmpiricalAuthority : Bool
    analogyCreatesEmpiricalAuthorityIsFalse :
      analogyCreatesEmpiricalAuthority ≡ false

open CrossDomainIdentityFirewall public

canonicalCrossDomainIdentityFirewall : CrossDomainIdentityFirewall
canonicalCrossDomainIdentityFirewall =
  cross-domain-identity-firewall false refl false refl false refl

------------------------------------------------------------------------
-- Existing phased-array/goniometer authority firewall remains intact.
------------------------------------------------------------------------

rfCrossPollinationRetainsAuthorityFirewall :
  RF.CrossDomainAuthorityFirewall
rfCrossPollinationRetainsAuthorityFirewall =
  RF.canonicalCrossDomainAuthorityFirewall
