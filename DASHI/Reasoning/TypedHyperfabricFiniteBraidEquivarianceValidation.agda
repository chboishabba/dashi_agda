module DASHI.Reasoning.TypedHyperfabricFiniteBraidEquivarianceValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TypedHyperfabricFiniteBraidEquivarianceExact as Bridge

finiteBraidOwnsDeformationAuthority :
  Bridge.finiteBraidRhizomeOwnsBraidAction
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ true
finiteBraidOwnsDeformationAuthority = refl

restrictionEquivarianceIsRequired :
  Bridge.restrictionEquivarianceRequired
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ true
restrictionEquivarianceIsRequired = refl

sectionTransportNeedsWitness :
  Bridge.sectionTransportWitnessRequired
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ true
sectionTransportNeedsWitness = refl

actionTraceAloneDoesNotPayBraidTransport :
  Bridge.actionTraceAlonePaysHyperfabricBraidTransport
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ false
actionTraceAloneDoesNotPayBraidTransport = refl

arbitraryFabricDoesNotAutomaticallyAdmitBraid :
  Bridge.arbitraryTypedHyperfabricAutomaticallyBraidEquivariant
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ false
arbitraryFabricDoesNotAutomaticallyAdmitBraid = refl

finiteTwoStrandSpecimenHasSectionTransport :
  Bridge.finiteTwoStrandSectionTransportConstructed
    Bridge.canonicalTypedHyperfabricFiniteBraidBoundary ≡ true
finiteTwoStrandSpecimenHasSectionTransport = refl
