module DASHI.Analysis.RiemannG2QuarticFarShellInverseSquareDonorValidationExact where

import DASHI.Analysis.RiemannG2QuarticFarShellInverseSquareDonorExact as O

sourceTheoremWritten :
  O.QuarticFarShellInverseSquareBoundary.fullInverseSquareLeanSourceWritten
    O.canonicalQuarticFarShellInverseSquareBoundary ≡ true
sourceTheoremWritten = refl

sameObjectTransportStillOpen :
  O.QuarticFarShellInverseSquareBoundary.sameObjectFarShellTransportPaid
    O.canonicalQuarticFarShellInverseSquareBoundary ≡ false
sameObjectTransportStillOpen = refl

r2StillOpen :
  O.QuarticFarShellInverseSquareBoundary.directR2EnvelopePaid
    O.canonicalQuarticFarShellInverseSquareBoundary ≡ false
r2StillOpen = refl
