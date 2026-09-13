module DASHI.Papers.NavierStokes.TheoremInterfaceValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Papers.NavierStokes.TheoremInterface as Paper

------------------------------------------------------------------------
-- Focused cumulative validation root for the canonical Paper-1 interface.
--
-- This file certifies only that the paper-facing status surface agrees with
-- the authoritative owners it imports.  In particular, checking this file does
-- NOT prove R568 or P3: both are required to remain false here while their
-- analytic producers are open.
------------------------------------------------------------------------

directCompanionConstructedIsTrue :
  Paper.directCompanionConstructed ≡ true
directCompanionConstructedIsTrue =
  Paper.directCompanionConstructedIsTrue Paper.canonicalNSPaperTheoremStatus

directLeafACompilerConstructedIsTrue :
  Paper.directLeafACompilerConstructed ≡ true
directLeafACompilerConstructedIsTrue =
  Paper.directLeafACompilerConstructedIsTrue Paper.canonicalNSPaperTheoremStatus

directOffDiagonalConsumerConstructedIsTrue :
  Paper.directOffDiagonalConsumerConstructed ≡ true
directOffDiagonalConsumerConstructedIsTrue =
  Paper.directOffDiagonalConsumerConstructedIsTrue Paper.canonicalNSPaperTheoremStatus

commutatorOnlySpacetimeProducerClosedIsFalse :
  Paper.commutatorOnlySpacetimeProducerClosed ≡ false
commutatorOnlySpacetimeProducerClosedIsFalse =
  Paper.commutatorOnlySpacetimeProducerClosedIsFalse Paper.canonicalNSPaperTheoremStatus

sameOutputDebtPaymentClosedIsFalse :
  Paper.sameOutputDebtPaymentClosed ≡ false
sameOutputDebtPaymentClosedIsFalse =
  Paper.sameOutputDebtPaymentClosedIsFalse Paper.canonicalNSPaperTheoremStatus

p3SeparationProducerClosedIsFalse :
  Paper.p3SeparationProducerClosed ≡ false
p3SeparationProducerClosedIsFalse =
  Paper.p3SeparationProducerClosedIsFalse Paper.canonicalNSPaperTheoremStatus

historicalA1A9RetainedIsTrue :
  Paper.historicalA1A9Retained ≡ true
historicalA1A9RetainedIsTrue =
  Paper.historicalA1A9RetainedIsTrue Paper.canonicalNSPaperTheoremStatus

clayTerminalPromotionIsFalse :
  Paper.clayTerminalPromotion ≡ false
clayTerminalPromotionIsFalse =
  Paper.clayTerminalPromotionIsFalse Paper.canonicalNSPaperTheoremStatus
