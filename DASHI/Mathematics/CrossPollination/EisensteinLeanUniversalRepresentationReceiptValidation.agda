module DASHI.Mathematics.CrossPollination.EisensteinLeanUniversalRepresentationReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.CrossPollination.EisensteinObserverRecoverableQuotientExact as Observer
import DASHI.Mathematics.CrossPollination.EisensteinLeanUniversalRepresentationReceiptExact as Receipt

leanOwnerIsFormalReconstruction :
  Receipt.leanEisensteinClaimOrigin ≡ Attribution.leanFormalReconstruction
leanOwnerIsFormalReconstruction = refl

coefficientSourceObserved :
  Receipt.leanUniversalCoefficientSourceObserved
  ≡ true
coefficientSourceObserved = refl

analyticSourceObserved :
  Receipt.leanDirichletSeriesSourceObserved
  ≡ true
analyticSourceObserved = refl

noLeanProofObjectImportedIntoAgda :
  Receipt.leanProofObjectImportedIntoAgda
  ≡ false
noLeanProofObjectImportedIntoAgda = refl

receiptDoesNotInhabitAgdaCoefficientTheorem :
  Receipt.agdaUniversalCoefficientTheoremInhabitedFromReceipt
  ≡ false
receiptDoesNotInhabitAgdaCoefficientTheorem = refl

receiptDoesNotInhabitAgdaAnalyticTheorem :
  Receipt.agdaDirichletSeriesTheoremInhabitedFromReceipt
  ≡ false
receiptDoesNotInhabitAgdaAnalyticTheorem = refl

noExternalSourceAcquiredByCrossProverReceipt :
  Receipt.externalScientificSourceAcquiredByThisReceipt
  ≡ false
noExternalSourceAcquiredByCrossProverReceipt = refl

observerDonorCarriesLocalChiSufficiency :
  Descent.ConsumerSufficient Observer.phaseOfNat Observer.chiMinus3WeightOfNat
observerDonorCarriesLocalChiSufficiency =
  Receipt.phaseSufficiency Receipt.canonicalObserverLeanDonorBundle

donorBundleStillDoesNotImportCoefficientTheorem :
  Receipt.coefficientTheoremImported
    Receipt.canonicalObserverLeanDonorBundle
  ≡ false
donorBundleStillDoesNotImportCoefficientTheorem = refl
