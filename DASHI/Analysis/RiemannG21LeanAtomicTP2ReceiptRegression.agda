module DASHI.Analysis.RiemannG21LeanAtomicTP2ReceiptRegression where

import DASHI.Analysis.RiemannG21LeanAtomicTP2ReceiptBoundary as Receipt

open import DASHI.Core.Prelude

regressionSinhTP2SourceWritten :
  Receipt.LeanAtomicTP2ReceiptBoundary.sinhTP2SourceWritten
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary ≡ true
regressionSinhTP2SourceWritten =
  Receipt.LeanAtomicTP2ReceiptBoundary.sinhTP2SourceWrittenIsTrue
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary

regressionCoshTP2SourceWritten :
  Receipt.LeanAtomicTP2ReceiptBoundary.coshTP2SourceWritten
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary ≡ true
regressionCoshTP2SourceWritten =
  Receipt.LeanAtomicTP2ReceiptBoundary.coshTP2SourceWrittenIsTrue
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary

regressionNoAgdaPromotion :
  Receipt.LeanAtomicTP2ReceiptBoundary.atomicTP2ImportedIntoAgda
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary ≡ false
regressionNoAgdaPromotion =
  Receipt.LeanAtomicTP2ReceiptBoundary.atomicTP2ImportedIntoAgdaIsFalse
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary

regressionContinuumStillOpen :
  Receipt.LeanAtomicTP2ReceiptBoundary.actualTaperDoubleIntegralSignPaid
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary ≡ false
regressionContinuumStillOpen =
  Receipt.LeanAtomicTP2ReceiptBoundary.actualTaperDoubleIntegralSignPaidIsFalse
    Receipt.canonicalLeanAtomicTP2ReceiptBoundary
