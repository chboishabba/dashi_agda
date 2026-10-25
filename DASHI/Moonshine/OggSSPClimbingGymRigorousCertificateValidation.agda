module DASHI.Moonshine.OggSSPClimbingGymRigorousCertificateValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.DyadicPhaseCellCertificateExact as Dyadic
import DASHI.Moonshine.OggSSPClimbingGymRigorousCertificateExact as Rigorous
import DASHI.Moonshine.OggSSPClimbingGymRigorousSourceAttributionExact as Source

------------------------------------------------------------------------
-- RED-first contract for the rigorous analytic-certificate continuation.
--
-- This validation owner intentionally names the production modules before
-- they are created.  The contract is narrow: exact external enclosure data may
-- determine a native finite radix cell after integer arithmetic is checked,
-- but producer provenance / interval arithmetic never becomes an Agda proof of
-- the Riemann hypothesis, Monster specificity, or a same-object zeta theorem.
------------------------------------------------------------------------

nativeRadixCellCheckerClosed :
  Dyadic.certifiedDyadicCellToRadialAddressClosed
    Dyadic.canonicalDyadicPhaseCellBoundary
  ≡ true
nativeRadixCellCheckerClosed = refl

externalProducerRemainsOutsideKernel :
  Rigorous.externalRigorousProducerIsAgdaKernelProof
    Rigorous.canonicalRigorousClimbingGymCertificateBoundary
  ≡ false
externalProducerRemainsOutsideKernel = refl

certifiedCellDoesNotProveZetaZero :
  Rigorous.certifiedPhaseCellProvesInputIsZetaZero
    Rigorous.canonicalRigorousClimbingGymCertificateBoundary
  ≡ false
certifiedCellDoesNotProveZetaZero = refl

flintCitationDoesNotImportProof :
  Source.flintCitationImportsProof
    Source.canonicalRigorousZeroSourceBoundary
  ≡ false
flintCitationDoesNotImportProof = refl

lmfdbRemainsIndependentReference :
  Source.lmfdbIsCertificateProducer
    Source.canonicalRigorousZeroSourceBoundary
  ≡ false
lmfdbRemainsIndependentReference = refl
