module DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutRegression where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact as Cut

nearUpperInternal :
  Cut.terminalRole Cut.chosenFiniteNearUpper ≡ Cut.producerInternal
nearUpperInternal = refl

nearSlackInternal :
  Cut.terminalRole Cut.chosenNearLeavesFarAllowance ≡ Cut.producerInternal
nearSlackInternal = refl

gammaEnvelopeInternal :
  Cut.terminalRole Cut.freshSameTaperGammaEnvelope ≡ Cut.producerInternal
gammaEnvelopeInternal = refl

gammaFitInternal :
  Cut.terminalRole Cut.gammaEnvelopeFitsAssignedAllowance ≡ Cut.producerInternal
gammaFitInternal = refl

offPaymentTerminal :
  Cut.terminalRole Cut.offAllowancePayment ≡ Cut.terminalAnalytic
offPaymentTerminal = refl

gammaPaymentTerminal :
  Cut.terminalRole Cut.gammaAllowancePayment ≡ Cut.terminalAnalytic
gammaPaymentTerminal = refl

attachmentDownstream :
  Cut.terminalRole Cut.finalOrderSameObjectClusterAttachment ≡ Cut.downstream
attachmentDownstream = refl

contradictionCompilerOutput :
  Cut.terminalRole Cut.finalHighOrdinateContradiction ≡ Cut.compilerOutput
contradictionCompilerOutput = refl

rhStillOpen :
  Cut.FinalPoleQuotientTwoPaymentBoundary.rhDerived
    Cut.canonicalFinalPoleQuotientTwoPaymentBoundary ≡ false
rhStillOpen = refl
