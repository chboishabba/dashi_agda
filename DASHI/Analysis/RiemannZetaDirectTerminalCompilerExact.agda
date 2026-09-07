module DASHI.Analysis.RiemannZetaDirectTerminalCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set₂)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannZetaTerminalPaymentCompressionExact as Cut

------------------------------------------------------------------------
-- DIRECT TERMINAL COMPILER
--
-- Historical producer route.  Once the literal Off and Gamma producer inputs
-- exist, do not hand-build their payment records and do not reopen the final
-- contradiction algebra.  Compile the two payments, attach them once to the
-- final ordered scalar/taper carrier, and invoke the existing contradiction.
------------------------------------------------------------------------

record DirectTerminalRHPacket : Set₂ where
  field
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offInput : Off.DirectPoleQuotientOffAllowanceInput offSurface

    gammaInput : Gamma.DirectPoleQuotientGammaAllowanceInput

    finalSurface : Split.OrderedAdditiveComplementSurface
    cluster : Cluster.PoleQuotientClusterMarginTarget

    finalOrderTransport :
      Final.FinalPoleQuotientOrderTransport
        finalSurface
        (Off.compilePoleQuotientOffAllowancePayment offInput)
        (Gamma.compilePoleQuotientGammaAllowancePayment gammaInput)
        cluster

open DirectTerminalRHPacket public

compiledOffPayment :
  DirectTerminalRHPacket → Payment.PoleQuotientOffAllowancePayment
compiledOffPayment packet =
  Off.compilePoleQuotientOffAllowancePayment (offInput packet)

compiledGammaPayment :
  DirectTerminalRHPacket → Payment.PoleQuotientGammaAllowancePayment
compiledGammaPayment packet =
  Gamma.compilePoleQuotientGammaAllowancePayment (gammaInput packet)

terminalPacketContradiction : DirectTerminalRHPacket → ⊥
terminalPacketContradiction packet =
  Final.orderTransportContradiction (finalOrderTransport packet)

------------------------------------------------------------------------
-- MINIMAL ANALYTIC-CORE TERMINAL COMPILER
--
-- Preferred current route.  The final analytic work is represented by the two
-- budget-fit cores introduced after the historical direct-input API.  Once
-- these cores, their exact representation attachments, and the already-owned
-- final same-object/order/cluster package exist, contradiction is compiler
-- output.  No determinant-era producer package is required by this route.
------------------------------------------------------------------------

record AnalyticCoreTerminalRHPacket : Set₂ where
  field
    cores : Core.FinalPoleQuotientTwoAnalyticCores
    attachments : Core.FinalPoleQuotientAnalyticCoreAttachments cores
    completion : Core.FinalPoleQuotientAnalyticCompletion cores attachments

open AnalyticCoreTerminalRHPacket public

analyticCorePacketContradiction : AnalyticCoreTerminalRHPacket → ⊥
analyticCorePacketContradiction packet =
  Core.compileAnalyticCoresToHighOrdinateContradiction
    (cores packet)
    (attachments packet)
    (completion packet)

compiledAnalyticCoreOffPayment :
  (packet : AnalyticCoreTerminalRHPacket) →
  Payment.PoleQuotientOffAllowancePayment
compiledAnalyticCoreOffPayment packet =
  Core.compileOffAllowancePayment
    (Core.offCore (cores packet))
    (Core.offAttachment (attachments packet))

compiledAnalyticCoreGammaPayment :
  (packet : AnalyticCoreTerminalRHPacket) →
  Payment.PoleQuotientGammaAllowancePayment
compiledAnalyticCoreGammaPayment packet =
  Core.compileGammaAllowancePayment
    (Core.gammaCore (cores packet))
    (Core.gammaAttachment (attachments packet))

------------------------------------------------------------------------
-- PRIZE-FACING HIGH/LOW COMPILER
--
-- This is only a dependency compiler.  It does not manufacture low-ordinate
-- verification, classical-stability, or high-zero analytic cores.  It merely
-- states their exact same-substrate composition into RiemannHypothesisFor.
------------------------------------------------------------------------

record PrizeFacingRHPacket : Set₂ where
  field
    analytic : Analytic.AnalyticSubstrate
    Low High : Universal.AnalyticNontrivialZero analytic → Set

    coverLowHigh :
      (ρ : Universal.AnalyticNontrivialZero analytic) →
      Low ρ ⊎ High ρ

    lowCertifiedCritical :
      (ρ : Universal.AnalyticNontrivialZero analytic) →
      Low ρ →
      Universal.analyticCritical ρ

    criticalLineStable : Universal.CriticalLineStable analytic

    highOffLineAnalyticCores :
      Universal.HighOffLineAnalyticCoreProducer analytic High

open PrizeFacingRHPacket public

compilePrizeFacingRH :
  (packet : PrizeFacingRHPacket) →
  Analytic.RiemannHypothesisFor (PrizeFacingRHPacket.analytic packet)
compilePrizeFacingRH packet =
  Universal.analyticCoreHighLowCompletionImpliesRH
    (PrizeFacingRHPacket.analytic packet)
    (PrizeFacingRHPacket.Low packet)
    (PrizeFacingRHPacket.High packet)
    (PrizeFacingRHPacket.coverLowHigh packet)
    (PrizeFacingRHPacket.lowCertifiedCritical packet)
    (PrizeFacingRHPacket.criticalLineStable packet)
    (PrizeFacingRHPacket.highOffLineAnalyticCores packet)

------------------------------------------------------------------------
-- Exact dependency pins.
------------------------------------------------------------------------

offCompositionAlreadyCompilerOwned :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.nearFarCompilerAlreadyOwnsFullComposition
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offCompositionAlreadyCompilerOwned = refl

offFinalPaymentCompiles :
  Off.PoleQuotientOffAllowanceDirectCompilerBoundary.finalOffTargetAndAllowancePaymentCompile
    Off.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
offFinalPaymentCompiles = refl

gammaFinalPaymentCompiles :
  Gamma.PoleQuotientGammaAllowanceDirectCompilerBoundary.finalGammaAllowancePaymentCompiles
    Gamma.canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary ≡ true
gammaFinalPaymentCompiles = refl

analyticCoresCompileExistingPayments :
  Core.FinalPoleQuotientAnalyticCoreBoundary.analyticCoresPlusAttachmentsCompileExistingPayments
    Core.canonicalFinalPoleQuotientAnalyticCoreBoundary ≡ true
analyticCoresCompileExistingPayments = refl

finalOrderTransportCompilesContradiction :
  Final.FinalOrderTransportBoundary.orderTransportPackageCompilesContradiction
    Final.canonicalFinalOrderTransportBoundary ≡ true
finalOrderTransportCompilesContradiction = refl

record DirectTerminalCompilerBoundary : Set where
  constructor direct-terminal-compiler-boundary
  field
    handBuildOffPaymentAfterInput : Bool
    handBuildOffPaymentAfterInputIsFalse : handBuildOffPaymentAfterInput ≡ false
    handBuildGammaPaymentAfterInput : Bool
    handBuildGammaPaymentAfterInputIsFalse : handBuildGammaPaymentAfterInput ≡ false
    rebuildFinalContradictionAfterTransport : Bool
    rebuildFinalContradictionAfterTransportIsFalse : rebuildFinalContradictionAfterTransport ≡ false
    analyticCoreRoutePreferredOverDeterminantPackaging : Bool
    analyticCoreRoutePreferredOverDeterminantPackagingIsTrue :
      analyticCoreRoutePreferredOverDeterminantPackaging ≡ true
    prizeFacingCompilerManufacturesLowCoverage : Bool
    prizeFacingCompilerManufacturesLowCoverageIsFalse :
      prizeFacingCompilerManufacturesLowCoverage ≡ false
    packetInhabitanceClaimedHere : Bool
    packetInhabitanceClaimedHereIsFalse : packetInhabitanceClaimedHere ≡ false
    rhDerivedWithoutPacket : Bool
    rhDerivedWithoutPacketIsFalse : rhDerivedWithoutPacket ≡ false

canonicalDirectTerminalCompilerBoundary : DirectTerminalCompilerBoundary
canonicalDirectTerminalCompilerBoundary =
  direct-terminal-compiler-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl

compressionBoundaryReused : Cut.TerminalPaymentCompressionBoundary
compressionBoundaryReused = Cut.canonicalTerminalPaymentCompressionBoundary
