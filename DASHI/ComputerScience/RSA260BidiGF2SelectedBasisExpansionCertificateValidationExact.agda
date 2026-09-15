module DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionCertificateValidationExact where

import DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionCertificateExact as Cert

verifiedPacketRoundTrip :
  ∀ {Coordinates : Set}
    (decoder : Cert.SelectedBasisDecoder Coordinates)
    (packet : Cert.VerifiedMatrixFactorPacket decoder) →
  Cert.decodeVerifiedPacket decoder packet ≡ Cert.expectedMatrix packet
verifiedPacketRoundTrip = Cert.verifiedMatrixFactorRoundTrip

boundary : Cert.GF2SelectedBasisExpansionCertificateBoundary
boundary = Cert.canonicalGF2SelectedBasisExpansionCertificateBoundary

firstResidual : Cert.GF2SelectedBasisExpansionCertificateResidual
firstResidual = Cert.firstGF2SelectedBasisExpansionCertificateResidual
