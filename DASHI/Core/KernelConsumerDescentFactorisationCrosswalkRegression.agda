module DASHI.Core.KernelConsumerDescentFactorisationCrosswalkRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel
import DASHI.Core.KernelConsumerDescentFactorisationCrosswalkExact as Crosswalk

kernelDescentToCanonicalFactorisation :
  ∀ {Fine Coarse Output : Set}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  Kernel.ConsumerDescent project consume →
  Factorized.FactorizedRefinement consume project
kernelDescentToCanonicalFactorisation = Crosswalk.kernelDescentToFactorized

canonicalFactorisationToKernelDescent :
  ∀ {Fine Coarse Output : Set}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  Factorized.FactorizedRefinement consume project →
  Kernel.ConsumerDescent project consume
canonicalFactorisationToKernelDescent = Crosswalk.factorizedToKernelDescent
