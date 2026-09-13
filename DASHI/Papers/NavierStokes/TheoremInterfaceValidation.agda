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

status : Paper.NSPaperTheoremStatus
status = Paper.canonicalNSPaperTheoremStatus

directCompanionConstructedIsTrue :
  Paper.NSPaperTheoremStatus.directCompanionConstructed status ≡ true
directCompanionConstructedIsTrue =
  Paper.NSPaperTheoremStatus.directCompanionConstructedIsTrue status

directLeafACompilerConstructedIsTrue :
  Paper.NSPaperTheoremStatus.directLeafACompilerConstructed status ≡ true
directLeafACompilerConstructedIsTrue =
  Paper.NSPaperTheoremStatus.directLeafACompilerConstructedIsTrue status

directOffDiagonalConsumerConstructedIsTrue :
  Paper.NSPaperTheoremStatus.directOffDiagonalConsumerConstructed status ≡ true
directOffDiagonalConsumerConstructedIsTrue =
  Paper.NSPaperTheoremStatus.directOffDiagonalConsumerConstructedIsTrue status

commutatorOnlySpacetimeProducerClosedIsFalse :
  Paper.NSPaperTheoremStatus.commutatorOnlySpacetimeProducerClosed status ≡ false
commutatorOnlySpacetimeProducerClosedIsFalse =
  Paper.NSPaperTheoremStatus.commutatorOnlySpacetimeProducerClosedIsFalse status

sameOutputDebtPaymentClosedIsFalse :
  Paper.NSPaperTheoremStatus.sameOutputDebtPaymentClosed status ≡ false
sameOutputDebtPaymentClosedIsFalse =
  Paper.NSPaperTheoremStatus.sameOutputDebtPaymentClosedIsFalse status

p3SeparationProducerClosedIsFalse :
  Paper.NSPaperTheoremStatus.p3SeparationProducerClosed status ≡ false
p3SeparationProducerClosedIsFalse =
  Paper.NSPaperTheoremStatus.p3SeparationProducerClosedIsFalse status

historicalA1A9RetainedIsTrue :
  Paper.NSPaperTheoremStatus.historicalA1A9Retained status ≡ true
historicalA1A9RetainedIsTrue =
  Paper.NSPaperTheoremStatus.historicalA1A9RetainedIsTrue status

clayTerminalPromotionIsFalse :
  Paper.NSPaperTheoremStatus.clayTerminalPromotion status ≡ false
clayTerminalPromotionIsFalse =
  Paper.NSPaperTheoremStatus.clayTerminalPromotionIsFalse status
