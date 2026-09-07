module DASHI.Analysis.RiemannG2DirectInputsToAnalyticCoresExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact as CertifiedOff

------------------------------------------------------------------------
-- HISTORICAL DIRECT INPUTS -> MINIMAL ANALYTIC CORES
--
-- The direct allowance inputs predate the analytic-core split and bundle
-- theorem-bearing budget fits with representation receipts.  The current search
-- target is smaller: OffAnalyticCore + GammaAnalyticCore, with cutoff/taper
-- identity carried separately.  These compilers prove the historical route is
-- an implementation of that minimal route, not a third terminal API.
------------------------------------------------------------------------

directOffAnalyticCore :
  ∀ {S} →
  Off.DirectPoleQuotientOffAllowanceInput S →
  Core.OffAnalyticCore
directOffAnalyticCore input =
  Core.off-analytic-core
    (Off.compilePoleQuotientOffTarget input)
    (Off.assignedOffAllowance input)
    (Off.compiledOffBudgetFitsAssignedAllowance input)
    (Off.producerReference input)

directOffRepresentationAttachment :
  ∀ {S} →
  (input : Off.DirectPoleQuotientOffAllowanceInput S) →
  Core.OffRepresentationAttachment (directOffAnalyticCore input)
directOffRepresentationAttachment input =
  Core.off-representation-attachment
    (Off.CrossingCutoff input (Off.chosenCutoff input))
    (Off.chosenCutoffCrosses input)
    (Off.sameLiteralPoleQuotientTaperAsFinalConsumer input)
    (Off.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input)
    (Off.producerReference input)

directGammaAnalyticCore :
  Gamma.DirectPoleQuotientGammaAllowanceInput →
  Core.GammaAnalyticCore
directGammaAnalyticCore input =
  Core.gamma-analytic-core
    (Gamma.target input)
    (Gamma.assignedGammaAllowance input)
    (Gamma.gammaBudgetBelowAssignedAllowance input)
    (Gamma.producerReference input)

directGammaRepresentationAttachment :
  (input : Gamma.DirectPoleQuotientGammaAllowanceInput) →
  Core.GammaRepresentationAttachment (directGammaAnalyticCore input)
directGammaRepresentationAttachment input =
  Core.gamma-representation-attachment
    (Gamma.sameLiteralPoleQuotientTaperAsFinalConsumer input)
    (Gamma.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input)
    (Gamma.producerReference input)

------------------------------------------------------------------------
-- Definitional factorization of the historical payment compilers.
------------------------------------------------------------------------

directOffPaymentFactorsThroughAnalyticCore :
  ∀ {S} →
  (input : Off.DirectPoleQuotientOffAllowanceInput S) →
  Off.compilePoleQuotientOffAllowancePayment input
  ≡ Core.compileOffAllowancePayment
      (directOffAnalyticCore input)
      (directOffRepresentationAttachment input)
directOffPaymentFactorsThroughAnalyticCore input = refl

directGammaPaymentFactorsThroughAnalyticCore :
  (input : Gamma.DirectPoleQuotientGammaAllowanceInput) →
  Gamma.compilePoleQuotientGammaAllowancePayment input
  ≡ Core.compileGammaAllowancePayment
      (directGammaAnalyticCore input)
      (directGammaRepresentationAttachment input)
directGammaPaymentFactorsThroughAnalyticCore input = refl

------------------------------------------------------------------------
-- Certified finite-upper Off route -> current analytic core.
--
-- The newer proof-carrying finite route already compiles a final Off payment.
-- Project only its theorem-bearing fields into the authoritative core; the
-- payment's cutoff/taper receipts remain representation data.
------------------------------------------------------------------------

paymentToOffAnalyticCore :
  Payment.PoleQuotientOffAllowancePayment →
  Core.OffAnalyticCore
paymentToOffAnalyticCore payment =
  Core.off-analytic-core
    (Payment.PoleQuotientOffAllowancePayment.target payment)
    (Payment.PoleQuotientOffAllowancePayment.assignedOffAllowance payment)
    (Payment.PoleQuotientOffAllowancePayment.offBudgetBelowAssignedAllowance payment)
    (Payment.PoleQuotientOffAllowancePayment.producerReference payment)

certifiedFiniteUpperOffAnalyticCore :
  ∀ {space formula window S transport} →
  CertifiedOff.CertifiedFiniteNearUpperOffPacket
    space formula window S transport →
  Core.OffAnalyticCore
certifiedFiniteUpperOffAnalyticCore packet =
  paymentToOffAnalyticCore
    (CertifiedOff.compileCertifiedFiniteNearUpperOffPayment packet)

record DirectInputsToAnalyticCoresBoundary : Set where
  constructor direct-inputs-to-analytic-cores-boundary
  field
    historicalDirectRouteIsIndependentTerminalAPI : Bool
    historicalDirectRouteIsIndependentTerminalAPIIsFalse :
      historicalDirectRouteIsIndependentTerminalAPI ≡ false

    directOffPaymentDefinitionallyFactorsThroughCore : Bool
    directOffPaymentDefinitionallyFactorsThroughCoreIsTrue :
      directOffPaymentDefinitionallyFactorsThroughCore ≡ true

    directGammaPaymentDefinitionallyFactorsThroughCore : Bool
    directGammaPaymentDefinitionallyFactorsThroughCoreIsTrue :
      directGammaPaymentDefinitionallyFactorsThroughCore ≡ true

    certifiedFiniteUpperRouteCompilesOffAnalyticCore : Bool
    certifiedFiniteUpperRouteCompilesOffAnalyticCoreIsTrue :
      certifiedFiniteUpperRouteCompilesOffAnalyticCore ≡ true

    representationReceiptsCountAsFreshAnalysis : Bool
    representationReceiptsCountAsFreshAnalysisIsFalse :
      representationReceiptsCountAsFreshAnalysis ≡ false

    analyticCoreInhabitanceFabricatedHere : Bool
    analyticCoreInhabitanceFabricatedHereIsFalse :
      analyticCoreInhabitanceFabricatedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalDirectInputsToAnalyticCoresBoundary :
  DirectInputsToAnalyticCoresBoundary
canonicalDirectInputsToAnalyticCoresBoundary =
  direct-inputs-to-analytic-cores-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Historical direct Off/Gamma inputs factor definitionally through the newer analytic-core split, so they are implementations of the minimal route rather than independent terminal search surfaces. The proof-carrying finite-upper Off route also projects to OffAnalyticCore. Cutoff/taper identity remains representation data. No analytic core is fabricated and RH is not derived."
