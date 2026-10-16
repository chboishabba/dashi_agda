module DASHI.Biology.KitzerowBH4TransportAcquisitionStatusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4TransportCarrierProbeExact as Probe

record TransportAcquisitionStatus : Set where
  constructor transportAcquisitionStatus
  field
    paidCarrierCoordinate : String
    paidQuantitativeCoordinate : String
    paidIntercellularChainCoordinate : String
    unpaidTargetCoordinate : String
    transportExistencePaid : Bool
    transportExistencePaidIsTrue : transportExistencePaid ≡ true
    contextSpecificCarrierMechanismsPaid : Bool
    contextSpecificCarrierMechanismsPaidIsTrue : contextSpecificCarrierMechanismsPaid ≡ true
    nonNeuralTranscellularRatePaid : Bool
    nonNeuralTranscellularRatePaidIsTrue : nonNeuralTranscellularRatePaid ≡ true
    neuralDonorRecipientRatePaid : Bool
    neuralDonorRecipientRatePaidIsFalse : neuralDonorRecipientRatePaid ≡ false
    wholeAllocatorClosed : Bool
    wholeAllocatorClosedIsFalse : wholeAllocatorClosed ≡ false

open TransportAcquisitionStatus public

canonicalTransportAcquisitionStatus : TransportAcquisitionStatus
canonicalTransportAcquisitionStatus =
  transportAcquisitionStatus
    "passive-like uptake in rat neural/PC12 preparations coexists with ENT1/ENT2 pterin transport, OAT1/OAT3 biopterin transport and transporter-sensitive epithelial BH4 translocation"
    "Ohashi et al. 2009 Caco-2: about 150 pmol BH4/h/well apical-to-basolateral at 100 micromol/L apical BH4"
    "catecholaminergic BH4 release + recipient-cell dose-dependent uptake/NO response + catecholaminergic/nNOS coculture functional effect are separately paid"
    "same-object isotope-resolved donor-derived BH4/BH2 molecular transfer rate into target neural recipient cells with simultaneous branch/redox readouts"
    true refl
    true refl
    true refl
    false refl
    false refl

probeBoundaryConsumed : Probe.TransportCarrierBoundary
probeBoundaryConsumed = Probe.canonicalTransportCarrierBoundary
