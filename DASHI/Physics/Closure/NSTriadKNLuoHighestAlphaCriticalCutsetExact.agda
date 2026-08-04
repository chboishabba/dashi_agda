module DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaCriticalCutsetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Compress the 661 stage-qualified completion inventory to the 28 declarations
-- whose inhabitation changes the mathematical status of the project.
--
-- This is a dependency cutset, not a proof of the open leaves.  Every
-- declaration is assigned a proposition by CriticalSpecification and must be
-- inhabited by CriticalInhabitants.  The predecessor relation records the
-- highest-alpha order and is independently checked by
-- scripts/check_ns_luo_highest_alpha_path.py.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLuoLemmaFamilyExact as Family

data CriticalLemma : Set where
  officialWeightedSpatialIntegralFourierIdentity
  rp1PairCoefficientIdentification
  rp2PairCoefficientIdentification
  tailPairCoefficientIdentification
  officialMultiplierReceiptsInhabited
  sourceAbsoluteFluxMatchesPhysicalBridge
  sourceLowGradientMatchesPhysicalBridge
  sourceEnergyDominatedByCommonSchurWeightedEnergy
  physicalFluxBelowLowGradientTimesWeightedEnergy
  officialEquation42
  physicalRHSMatchesTotalInteractionFold
  physicalJ11LowerBound
  physicalJ11UpperBound
  physicalJ12Bound
  physicalJ2Bound
  analyticFourShellRatioEqualsQuarter
  integralGronwall
  integratedCutoffEnergyInequality
  fluxCorrectionAbsorbedUniformly
  physicalBlockDecayCertificate
  shellDecayImpliesContinuationRegularity
  canonicalAnalyticPhysicalLeaves
  finiteMaximalTimeExcludedForEveryDatum
  officialInfiniteRealAnalyticInputs
  globalStrongSolutionForEveryAdmissibleDatum
  globalVelocitySmooth
  globalPressureSmooth
  submissionAuditReceiptComplete
    : CriticalLemma

CriticalSpecification : Set₁
CriticalSpecification = Family.LemmaSpecification CriticalLemma

CriticalInhabitants : CriticalSpecification → Set₁
CriticalInhabitants = Family.LemmaInhabitants

criticalPathOrder : List CriticalLemma
criticalPathOrder =
  officialWeightedSpatialIntegralFourierIdentity ∷
  rp1PairCoefficientIdentification ∷
  rp2PairCoefficientIdentification ∷
  tailPairCoefficientIdentification ∷
  officialMultiplierReceiptsInhabited ∷
  sourceAbsoluteFluxMatchesPhysicalBridge ∷
  sourceLowGradientMatchesPhysicalBridge ∷
  sourceEnergyDominatedByCommonSchurWeightedEnergy ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  officialEquation42 ∷
  physicalRHSMatchesTotalInteractionFold ∷
  physicalJ11LowerBound ∷
  physicalJ11UpperBound ∷
  physicalJ12Bound ∷
  physicalJ2Bound ∷
  analyticFourShellRatioEqualsQuarter ∷
  integralGronwall ∷
  integratedCutoffEnergyInequality ∷
  fluxCorrectionAbsorbedUniformly ∷
  physicalBlockDecayCertificate ∷
  shellDecayImpliesContinuationRegularity ∷
  canonicalAnalyticPhysicalLeaves ∷
  finiteMaximalTimeExcludedForEveryDatum ∷
  officialInfiniteRealAnalyticInputs ∷
  globalStrongSolutionForEveryAdmissibleDatum ∷
  globalVelocitySmooth ∷
  globalPressureSmooth ∷
  submissionAuditReceiptComplete ∷
  []

criticalPhase : CriticalLemma → Nat
criticalPhase officialWeightedSpatialIntegralFourierIdentity = 1
criticalPhase rp1PairCoefficientIdentification = 1
criticalPhase rp2PairCoefficientIdentification = 1
criticalPhase tailPairCoefficientIdentification = 1
criticalPhase officialMultiplierReceiptsInhabited = 2
criticalPhase sourceAbsoluteFluxMatchesPhysicalBridge = 2
criticalPhase sourceLowGradientMatchesPhysicalBridge = 2
criticalPhase sourceEnergyDominatedByCommonSchurWeightedEnergy = 2
criticalPhase physicalFluxBelowLowGradientTimesWeightedEnergy = 2
criticalPhase officialEquation42 = 3
criticalPhase physicalRHSMatchesTotalInteractionFold = 3
criticalPhase physicalJ11LowerBound = 4
criticalPhase physicalJ11UpperBound = 4
criticalPhase physicalJ12Bound = 4
criticalPhase physicalJ2Bound = 4
criticalPhase analyticFourShellRatioEqualsQuarter = 5
criticalPhase integralGronwall = 5
criticalPhase integratedCutoffEnergyInequality = 5
criticalPhase fluxCorrectionAbsorbedUniformly = 5
criticalPhase physicalBlockDecayCertificate = 5
criticalPhase shellDecayImpliesContinuationRegularity = 5
criticalPhase canonicalAnalyticPhysicalLeaves = 6
criticalPhase finiteMaximalTimeExcludedForEveryDatum = 7
criticalPhase officialInfiniteRealAnalyticInputs = 8
criticalPhase globalStrongSolutionForEveryAdmissibleDatum = 9
criticalPhase globalVelocitySmooth = 9
criticalPhase globalPressureSmooth = 9
criticalPhase submissionAuditReceiptComplete = 10

criticalPredecessors : CriticalLemma → List CriticalLemma
criticalPredecessors officialWeightedSpatialIntegralFourierIdentity = []
criticalPredecessors rp1PairCoefficientIdentification =
  officialWeightedSpatialIntegralFourierIdentity ∷ []
criticalPredecessors rp2PairCoefficientIdentification =
  officialWeightedSpatialIntegralFourierIdentity ∷ []
criticalPredecessors tailPairCoefficientIdentification =
  officialWeightedSpatialIntegralFourierIdentity ∷ []
criticalPredecessors officialMultiplierReceiptsInhabited = []
criticalPredecessors sourceAbsoluteFluxMatchesPhysicalBridge =
  officialWeightedSpatialIntegralFourierIdentity ∷
  rp1PairCoefficientIdentification ∷
  rp2PairCoefficientIdentification ∷
  tailPairCoefficientIdentification ∷
  []
criticalPredecessors sourceLowGradientMatchesPhysicalBridge =
  officialMultiplierReceiptsInhabited ∷ []
criticalPredecessors sourceEnergyDominatedByCommonSchurWeightedEnergy =
  sourceAbsoluteFluxMatchesPhysicalBridge ∷
  sourceLowGradientMatchesPhysicalBridge ∷
  []
criticalPredecessors physicalFluxBelowLowGradientTimesWeightedEnergy =
  sourceEnergyDominatedByCommonSchurWeightedEnergy ∷ []
criticalPredecessors officialEquation42 =
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷ []
criticalPredecessors physicalRHSMatchesTotalInteractionFold =
  rp1PairCoefficientIdentification ∷
  rp2PairCoefficientIdentification ∷
  tailPairCoefficientIdentification ∷
  officialEquation42 ∷
  []
criticalPredecessors physicalJ11LowerBound =
  physicalRHSMatchesTotalInteractionFold ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  []
criticalPredecessors physicalJ11UpperBound =
  physicalRHSMatchesTotalInteractionFold ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  []
criticalPredecessors physicalJ12Bound =
  physicalRHSMatchesTotalInteractionFold ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  []
criticalPredecessors physicalJ2Bound =
  physicalRHSMatchesTotalInteractionFold ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  []
criticalPredecessors analyticFourShellRatioEqualsQuarter = []
criticalPredecessors integralGronwall =
  officialEquation42 ∷
  physicalJ11LowerBound ∷
  physicalJ11UpperBound ∷
  physicalJ12Bound ∷
  physicalJ2Bound ∷
  analyticFourShellRatioEqualsQuarter ∷
  []
criticalPredecessors integratedCutoffEnergyInequality =
  officialEquation42 ∷ integralGronwall ∷ []
criticalPredecessors fluxCorrectionAbsorbedUniformly =
  integratedCutoffEnergyInequality ∷
  physicalJ11LowerBound ∷
  physicalJ11UpperBound ∷
  physicalJ12Bound ∷
  physicalJ2Bound ∷
  analyticFourShellRatioEqualsQuarter ∷
  []
criticalPredecessors physicalBlockDecayCertificate =
  fluxCorrectionAbsorbedUniformly ∷ []
criticalPredecessors shellDecayImpliesContinuationRegularity =
  physicalBlockDecayCertificate ∷
  analyticFourShellRatioEqualsQuarter ∷
  []
criticalPredecessors canonicalAnalyticPhysicalLeaves =
  officialWeightedSpatialIntegralFourierIdentity ∷
  officialMultiplierReceiptsInhabited ∷
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  officialEquation42 ∷
  physicalJ11LowerBound ∷
  physicalJ11UpperBound ∷
  physicalJ12Bound ∷
  physicalJ2Bound ∷
  integralGronwall ∷
  physicalBlockDecayCertificate ∷
  shellDecayImpliesContinuationRegularity ∷
  []
criticalPredecessors finiteMaximalTimeExcludedForEveryDatum =
  canonicalAnalyticPhysicalLeaves ∷ []
criticalPredecessors officialInfiniteRealAnalyticInputs =
  physicalFluxBelowLowGradientTimesWeightedEnergy ∷
  officialEquation42 ∷
  physicalJ11LowerBound ∷
  physicalJ11UpperBound ∷
  physicalJ12Bound ∷
  physicalJ2Bound ∷
  physicalBlockDecayCertificate ∷
  []
criticalPredecessors globalStrongSolutionForEveryAdmissibleDatum =
  finiteMaximalTimeExcludedForEveryDatum ∷
  officialInfiniteRealAnalyticInputs ∷
  []
criticalPredecessors globalVelocitySmooth =
  globalStrongSolutionForEveryAdmissibleDatum ∷
  shellDecayImpliesContinuationRegularity ∷
  []
criticalPredecessors globalPressureSmooth =
  globalVelocitySmooth ∷ []
criticalPredecessors submissionAuditReceiptComplete =
  canonicalAnalyticPhysicalLeaves ∷
  finiteMaximalTimeExcludedForEveryDatum ∷
  officialInfiniteRealAnalyticInputs ∷
  globalStrongSolutionForEveryAdmissibleDatum ∷
  globalVelocitySmooth ∷
  globalPressureSmooth ∷
  []

criticalLemmaCount : Nat
criticalLemmaCount = 28

criticalPhaseCount : Nat
criticalPhaseCount = 10

highestAlphaCriticalCutsetConstructed : Bool
highestAlphaCriticalCutsetConstructed = true

highestAlphaCriticalCutsetInhabited : Bool
highestAlphaCriticalCutsetInhabited = false

canonicalAnalyticPhysicalLeavesInhabited : Bool
canonicalAnalyticPhysicalLeavesInhabited = false

periodicNavierStokesGlobalRegularityProved : Bool
periodicNavierStokesGlobalRegularityProved = false

submissionPackageComplete : Bool
submissionPackageComplete = false

highestAlphaCriticalCutsetConstructedIsTrue :
  highestAlphaCriticalCutsetConstructed ≡ true
highestAlphaCriticalCutsetConstructedIsTrue = refl

highestAlphaCriticalCutsetInhabitedIsFalse :
  highestAlphaCriticalCutsetInhabited ≡ false
highestAlphaCriticalCutsetInhabitedIsFalse = refl

periodicNavierStokesGlobalRegularityRemainsFalse :
  periodicNavierStokesGlobalRegularityProved ≡ false
periodicNavierStokesGlobalRegularityRemainsFalse = refl

submissionPackageRemainsIncomplete :
  submissionPackageComplete ≡ false
submissionPackageRemainsIncomplete = refl
