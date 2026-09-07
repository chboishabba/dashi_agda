module DASHI.Analysis.RiemannZetaDirectTerminalCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set₂)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as Off
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final
import DASHI.Analysis.RiemannZetaTerminalPaymentCompressionExact as Cut

------------------------------------------------------------------------
-- DIRECT TERMINAL COMPILER
--
-- Once the literal Off and Gamma producer inputs exist, do not hand-build their
-- payment records and do not reopen the final contradiction algebra. Compile the
-- two payments, attach them once to the final ordered scalar/taper carrier, and
-- invoke the already-owned final contradiction compiler.
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
    false refl
    false refl

compressionBoundaryReused : Cut.TerminalPaymentCompressionBoundary
compressionBoundaryReused = Cut.canonicalTerminalPaymentCompressionBoundary
