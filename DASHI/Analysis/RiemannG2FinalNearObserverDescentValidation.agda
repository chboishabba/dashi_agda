module DASHI.Analysis.RiemannG2FinalNearObserverDescentValidation where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Unit using (tt)

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Foundations.HyperformChartGluingExact as Glue

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Concrete
import DASHI.Analysis.RiemannG2FinalNearObserverDescentExact as R1

embeddedFoldChartHasOverlap :
  ∀ {S transport offInput carrier certificate}
    (bridge : Concrete.ConcreteCertificateFinalScalarBridge
      {S = S} {transport = transport}
      offInput carrier certificate) →
  Glue.chartA (R1.finalNearEmbeddedFoldGluing bridge) tt
  ≡
  Glue.chartB (R1.finalNearEmbeddedFoldGluing bridge) tt
embeddedFoldChartHasOverlap bridge =
  Glue.glueOnOverlap (R1.finalNearEmbeddedFoldGluing bridge) tt

offBudgetFactorsThroughFold :
  ∀ {S transport offInput carrier certificate}
    (bridge : Concrete.ConcreteCertificateFinalScalarBridge
      {S = S} {transport = transport}
      offInput carrier certificate) →
  Descent.FactorsThrough
    (Glue.observe (R1.finalNearFoldObserver S))
    (R1.finalNearPlusFarConsumer S
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff offInput)))
offBudgetFactorsThroughFold {S = S} {transport = transport} {offInput = offInput} bridge =
  R1.finalNearPlusFarFactorsThroughObservedFold S
    (Transport.farBudgetAt transport
      (Direct.chosenCutoff offInput))
