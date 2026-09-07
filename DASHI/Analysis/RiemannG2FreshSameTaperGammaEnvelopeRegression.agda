module DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as Fresh
import DASHI.Analysis.RiemannG2FinalGammaRouteSchedulerRegression as Scheduler

historical8889IdentityNotRequired :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.historical8889IdentityRequiredForFreshEnvelope
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
historical8889IdentityNotRequired = refl

historicalLossLocalizationNotRequired :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.historicalPrecisionLossLocalizationRequiredForFreshEnvelope
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
historicalLossLocalizationNotRequired = refl

sameFinalTaperRequired :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.sameLiteralFinalTaperStillRequired
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ true
sameFinalTaperRequired = refl

responseUpperCompilesTarget :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.freshResponseUpperCompilesGammaTarget
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ true
responseUpperCompilesTarget = refl

allowanceFitCompilesPayment :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.freshEnvelopeAllowanceFitCompilesFinalPayment
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ true
allowanceFitCompilesPayment = refl

noEnvelopeFabricated :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.freshGammaEnvelopeInhabitedHere
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
noEnvelopeFabricated = refl

finalGammaStillOpen :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.finalGammaPaymentClosedHere
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
finalGammaStillOpen = refl

rhStillOpen :
  Fresh.FreshSameTaperGammaEnvelopeBoundary.rhDerived
    Fresh.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
rhStillOpen = refl
