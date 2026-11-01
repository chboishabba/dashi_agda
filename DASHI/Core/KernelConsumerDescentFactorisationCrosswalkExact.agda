module DASHI.Core.KernelConsumerDescentFactorisationCrosswalkExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

------------------------------------------------------------------------
-- KERNEL CONSUMER DESCENT <-> CANONICAL FACTORIZED REFINEMENT
--
-- Both records carry exactly an interpreter from the projected surface to the
-- consumer output plus the same commuting equation.  Keep both public APIs for
-- compatibility, but make their definitional theorem content explicitly
-- translatable.
------------------------------------------------------------------------

kernelDescentToFactorized :
  ∀ {Fine Coarse Output : Set}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  Kernel.ConsumerDescent project consume →
  Factorized.FactorizedRefinement consume project
kernelDescentToFactorized descent =
  Factorized.factorizedRefinement
    (Kernel.quotientConsumer descent)
    (Kernel.factorises descent)

factorizedToKernelDescent :
  ∀ {Fine Coarse Output : Set}
    {project : Fine → Coarse}
    {consume : Fine → Output} →
  Factorized.FactorizedRefinement consume project →
  Kernel.ConsumerDescent project consume
factorizedToKernelDescent factorization =
  Kernel.consumerDescent
    (Factorized.factor factorization)
    (Factorized.factorizes factorization)
