module DASHI.Physics.Closure.NSTriadKNNineOwnerToBlockDecayBridgeRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The Round-28 nine-owner reserve program and the older source-faithful Luo
-- continuation program had remained partly parallel.  Their first genuinely
-- shared quantity is the integrated cutoff energy inequality.
--
-- This file identifies it exactly: the strict nine-owner estimate
--
--   E_out + (1-sum eta_i) D <= E_in + admissible remainder
--
-- *is* the integrated cutoff inequality consumed by the block-decay lane.
-- There is no new mega-receipt and no second energy estimate.
--
-- The bridge record below therefore asks downstream work only for the
-- correction-majorant/fixed-shift/base-block/decay implications which are not
-- consequences of owner absorption.  From those and one NineOwnerCriticalBalance
-- it constructs the existing PhysicalBlockDecayPrimitiveInputs and hence the
-- existing PhysicalBlockDecayReceipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_*_; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalBlockDecayReductionExact as Block

NineOwnerIntegratedCutoffEnergyInequality :
  Nine.NineOwnerCriticalBalance → Set
NineOwnerIntegratedCutoffEnergyInequality balance =
  Nine.energyOut balance
    + Nine.remainingViscosity balance
      * Owner.dissipation (Nine.environment balance)
  ≤
  Nine.energyIn balance + Nine.admissibleRemainder balance

physicalNineOwnerBalanceToIntegratedCutoffEnergyInequality :
  (balance : Nine.NineOwnerCriticalBalance) →
  NineOwnerIntegratedCutoffEnergyInequality balance
physicalNineOwnerBalanceToIntegratedCutoffEnergyInequality =
  Nine.nineOwnerStrictCriticalEstimate

record ReserveToBlockDecayBridge
    (balance : Nine.NineOwnerCriticalBalance) : Set₁ where
  field
    FluxCorrectionBelowExplicitMajorant : Set
    fluxCorrectionBelowExplicitMajorant :
      FluxCorrectionBelowExplicitMajorant

    ExplicitMajorantBelowDyadicDecayTarget : Set
    explicitMajorantBelowDyadicDecayTarget :
      ExplicitMajorantBelowDyadicDecayTarget

    FixedShiftRecursion : Set
    fixedShiftRecursionFromReserve :
      NineOwnerIntegratedCutoffEnergyInequality balance →
      FluxCorrectionBelowExplicitMajorant →
      ExplicitMajorantBelowDyadicDecayTarget →
      FixedShiftRecursion

    BaseBlockFinite : Set
    baseBlockFinite : BaseBlockFinite

    BaseBlockUniformBound : Set
    baseBlockUniformBound : BaseBlockFinite → BaseBlockUniformBound

    RecursionCoefficientStrictlyBelowOne : Set
    recursionCoefficientStrictlyBelowOne :
      RecursionCoefficientStrictlyBelowOne

    CorrectionDecayCompatibleWithTarget : Set
    correctionDecayCompatibleWithTarget :
      CorrectionDecayCompatibleWithTarget

    PhysicalBlockDecayCertificate : Set
    blockInductionCloses :
      FixedShiftRecursion →
      BaseBlockUniformBound →
      RecursionCoefficientStrictlyBelowOne →
      CorrectionDecayCompatibleWithTarget →
      PhysicalBlockDecayCertificate

    ShellUniformDyadicDecay : Set
    blockDecayGivesShellUniformDyadicDecay :
      PhysicalBlockDecayCertificate → ShellUniformDyadicDecay

    ShellL2Decay : Set
    energyDecayImpliesShellL2Decay :
      ShellUniformDyadicDecay → ShellL2Decay

    GradientShellDecay : Set
    dissipationDecayImpliesGradientShellDecay :
      ShellUniformDyadicDecay → GradientShellDecay

    AlphaAboveOneSummability : Set
    alphaAboveOneSummability : AlphaAboveOneSummability

    RequiredContinuationRegularity : Set
    shellDecayAndSummabilityGiveRequiredRegularity :
      ShellL2Decay →
      GradientShellDecay →
      AlphaAboveOneSummability →
      RequiredContinuationRegularity

open ReserveToBlockDecayBridge public

physicalReserveToBlockDecayPrimitiveInputs :
  ∀ {balance} →
  ReserveToBlockDecayBridge balance →
  Block.PhysicalBlockDecayPrimitiveInputs
physicalReserveToBlockDecayPrimitiveInputs {balance} bridge = record
  { IntegratedCutoffEnergyInequality =
      NineOwnerIntegratedCutoffEnergyInequality balance
  ; integratedCutoffEnergyInequality =
      physicalNineOwnerBalanceToIntegratedCutoffEnergyInequality balance
  ; FluxCorrectionBelowExplicitMajorant =
      FluxCorrectionBelowExplicitMajorant bridge
  ; fluxCorrectionBelowExplicitMajorant =
      fluxCorrectionBelowExplicitMajorant bridge
  ; ExplicitMajorantBelowDyadicDecayTarget =
      ExplicitMajorantBelowDyadicDecayTarget bridge
  ; explicitMajorantBelowDyadicDecayTarget =
      explicitMajorantBelowDyadicDecayTarget bridge
  ; FixedShiftRecursion = FixedShiftRecursion bridge
  ; fixedShiftRecursionFromPhysicalInequalities =
      fixedShiftRecursionFromReserve bridge
  ; BaseBlockFinite = BaseBlockFinite bridge
  ; baseBlockFinite = baseBlockFinite bridge
  ; BaseBlockUniformBound = BaseBlockUniformBound bridge
  ; baseBlockUniformBound = baseBlockUniformBound bridge
  ; RecursionCoefficientStrictlyBelowOne =
      RecursionCoefficientStrictlyBelowOne bridge
  ; recursionCoefficientStrictlyBelowOne =
      recursionCoefficientStrictlyBelowOne bridge
  ; CorrectionDecayCompatibleWithTarget =
      CorrectionDecayCompatibleWithTarget bridge
  ; correctionDecayCompatibleWithTarget =
      correctionDecayCompatibleWithTarget bridge
  ; PhysicalBlockDecayCertificate = PhysicalBlockDecayCertificate bridge
  ; blockInductionCloses = blockInductionCloses bridge
  ; ShellUniformDyadicDecay = ShellUniformDyadicDecay bridge
  ; blockDecayGivesShellUniformDyadicDecay =
      blockDecayGivesShellUniformDyadicDecay bridge
  ; ShellL2Decay = ShellL2Decay bridge
  ; energyDecayImpliesShellL2Decay = energyDecayImpliesShellL2Decay bridge
  ; GradientShellDecay = GradientShellDecay bridge
  ; dissipationDecayImpliesGradientShellDecay =
      dissipationDecayImpliesGradientShellDecay bridge
  ; AlphaAboveOneSummability = AlphaAboveOneSummability bridge
  ; alphaAboveOneSummability = alphaAboveOneSummability bridge
  ; RequiredContinuationRegularity = RequiredContinuationRegularity bridge
  ; shellDecayAndSummabilityGiveRequiredRegularity =
      shellDecayAndSummabilityGiveRequiredRegularity bridge
  }

physicalReserveToBlockDecayReceipt :
  ∀ {balance} →
  ReserveToBlockDecayBridge balance →
  Block.PhysicalBlockDecayReceipt
physicalReserveToBlockDecayReceipt bridge =
  Block.physicalBlockDecayReceipt
    (physicalReserveToBlockDecayPrimitiveInputs bridge)

nineOwnerReserveIntegratedCutoffBridgeClosed : Bool
nineOwnerReserveIntegratedCutoffBridgeClosed = true

ownerAndSourceFaithfulContinuationNoLongerParallelAtEnergyStep : Bool
ownerAndSourceFaithfulContinuationNoLongerParallelAtEnergyStep = true

nineOwnerReserveIntegratedCutoffBridgeClosedIsTrue :
  nineOwnerReserveIntegratedCutoffBridgeClosed ≡ true
nineOwnerReserveIntegratedCutoffBridgeClosedIsTrue = refl

ownerAndSourceFaithfulContinuationNoLongerParallelAtEnergyStepIsTrue :
  ownerAndSourceFaithfulContinuationNoLongerParallelAtEnergyStep ≡ true
ownerAndSourceFaithfulContinuationNoLongerParallelAtEnergyStepIsTrue = refl
