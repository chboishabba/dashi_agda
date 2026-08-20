module DASHI.Physics.Closure.NSTriadKNLuoGalerkinKernelRound15Validation where

------------------------------------------------------------------------
-- PURPOSE
-- Cumulative validation root for the round-fifteen periodic Galerkin,
-- centered-kernel, residual-tail and continuation tranche.
-- This root is the single pinned Agda entry point used by the round-15 CI.
-- Corrected stacked validation trigger revision 2.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoCommutatorContinuumRound14Validation

import DASHI.Physics.Closure.NSTriadKNDaLioRiviereThreeTermCommutatorSourceAuditExact
import DASHI.Physics.Closure.NSTriadKNFrankSukochevZaninCommutatorSourceAuditExact

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshCharacterOrthogonalityExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshParsevalExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinParsevalExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinSupportUniformExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinHighHighTerminalExact

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicCenteredKernelSecondMomentExact
import DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSixThreeKernelEstimateExact
import DASHI.Physics.Closure.NSTriadKNLuoLowHighSixThreeTerminalExact
import DASHI.Physics.Closure.NSTriadKNLuoHighLowDerivativePlacementTerminalExact

import DASHI.Physics.Closure.NSTriadKNYuFiniteFarFieldConvolutionC0Exact
import DASHI.Physics.Closure.NSTriadKNYuIncrementDefectCriticalKernelExact
import DASHI.Physics.Closure.NSTriadKNYuLocalizationCaccioppoliTailExact

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinFourClassContinuationExact
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinUniformLimitContinuationExact
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceDynamicRarityExact
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedDefectTransferExact
import DASHI.Physics.Closure.NSTriadKNLuoGoodCoherenceWeightedDefectExact
