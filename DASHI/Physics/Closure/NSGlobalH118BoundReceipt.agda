module DASHI.Physics.Closure.NSGlobalH118BoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent
import DASHI.Physics.Closure.NSCarrierEnergyInequalityReceipt as Energy
import DASHI.Physics.Closure.NSCombinedRegularityMechanismReceipt as Combined
import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt as Flow
import DASHI.Physics.Closure.NSH118GlobalRegularityReceipt as Global
import DASHI.Physics.Closure.NSH118ThresholdReceipt as Threshold
import DASHI.Physics.Closure.NSLargeDataGapReframingReceipt as Gap

------------------------------------------------------------------------
-- Global H^{11/8} bound receipt for carrier-structured NS data.
--
-- This A6 receipt combines the A1--A5 surfaces into one explicit
-- candidate bound.  It records the split
--
--   ||u(t)||^2_H118 <= E_low + E_high <= E_MAX(nu,M0,p)
--
-- for carrier-structured u0 in H^{11/8}, ||u0||_L2 = M0, and fixed
-- nu > 0.  The formula is finite for each fixed positive viscosity but
-- diverges as nu -> 0.  The receipt explicitly depends on adjacent-only
-- structure and the Leray L2 bound.  The Prodi-Serrin route is recorded as
-- a candidate regularity route only: H118 bound -> u in
-- L^{16/7}(0,T;L^{24}) -> smoothness for each finite T; T -> infinity
-- gives a global smooth solution candidate.
--
-- Status remains candidate pending Bernoulli band rigour.  Clay promotion
-- is false.

data NSGlobalH118BoundStatus : Set where
  candidatePendingBernoulliRigour :
    NSGlobalH118BoundStatus

data NSGlobalH118BoundDependency : Set where
  a1AdjacentOnlyStructure :
    NSGlobalH118BoundDependency

  a2FlowPreservationSuppression :
    NSGlobalH118BoundDependency

  a3H118ThresholdLargeDataAllowed :
    NSGlobalH118BoundDependency

  a4CombinedHighLowMechanism :
    NSGlobalH118BoundDependency

  a5LargeDataGapReframedAsEnergyBound :
    NSGlobalH118BoundDependency

  lerayL2Bound :
    NSGlobalH118BoundDependency

canonicalNSGlobalH118BoundDependencies :
  List NSGlobalH118BoundDependency
canonicalNSGlobalH118BoundDependencies =
  a1AdjacentOnlyStructure
  ∷ a2FlowPreservationSuppression
  ∷ a3H118ThresholdLargeDataAllowed
  ∷ a4CombinedHighLowMechanism
  ∷ a5LargeDataGapReframedAsEnergyBound
  ∷ lerayL2Bound
  ∷ []

data NSProdiSerrinRouteStep : Set where
  h118Bound :
    NSProdiSerrinRouteStep

  uInL167TimeL24Space :
    NSProdiSerrinRouteStep

  smoothnessForEachFiniteT :
    NSProdiSerrinRouteStep

  tToInfinityGlobalSmoothCandidate :
    NSProdiSerrinRouteStep

canonicalNSProdiSerrinRoute :
  List NSProdiSerrinRouteStep
canonicalNSProdiSerrinRoute =
  h118Bound
  ∷ uInL167TimeL24Space
  ∷ smoothnessForEachFiniteT
  ∷ tToInfinityGlobalSmoothCandidate
  ∷ []

data NSGlobalH118BoundPromotion : Set where

nsGlobalH118BoundPromotionImpossibleHere :
  NSGlobalH118BoundPromotion →
  ⊥
nsGlobalH118BoundPromotionImpossibleHere ()

eMaxFormulaLabel : String
eMaxFormulaLabel =
  "E_MAX(nu,M0,p) = M0^2*(C/nu)^{11/4}/(p^{11/4}-1)+2E(0)+2C^2 M0^2 (C/nu)^{11/4-2}/(nu^2(1-p^{-2}))"

nsGlobalH118BoundInequalityLabel : String
nsGlobalH118BoundInequalityLabel =
  "||u(t)||^2_H118 <= E_low+E_high <= E_MAX(nu,M0,p)"

nsGlobalH118ProdiSerrinRouteLabel : String
nsGlobalH118ProdiSerrinRouteLabel =
  "H118 bound -> u in L^{16/7}(0,T;L^{24}) -> smoothness for each finite T; T->infty gives global smooth solution candidate"

nsGlobalH118BoundStatement : String
nsGlobalH118BoundStatement =
  "Candidate A6 receipt: for carrier-structured u0 in H^{11/8}, ||u0||_L2=M0, and any nu>0, ||u(t)||^2_H118 <= E_low+E_high <= E_MAX(nu,M0,p), with E_MAX(nu,M0,p) = M0^2*(C/nu)^{11/4}/(p^{11/4}-1)+2E(0)+2C^2 M0^2 (C/nu)^{11/4-2}/(nu^2(1-p^{-2})). The bound is finite for each fixed nu>0 and diverges as nu->0. It requires adjacent-only structure and the Leray L2 bound. Prodi-Serrin route: H118 bound -> u in L^{16/7}(0,T;L^{24}) -> smoothness for each finite T; T->infty gives a global smooth solution candidate. Status: candidate pending Bernoulli rigour; Clay promotion false."

record NSGlobalH118BoundReceipt : Setω where
  field
    status :
      NSGlobalH118BoundStatus

    statusIsCandidatePendingBernoulliRigour :
      status ≡ candidatePendingBernoulliRigour

    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyStructureRequiredFromReceipt :
      Adjacent.sameBaseResonancesAdjacentBandOnly adjacentOnlyReceipt ≡ true

    adjacentOnlyNoClayPromotion :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt ≡ false

    flowPreservationReceipt :
      Flow.NSFlowPreservationBoundReceipt

    flowSuppressionFromReceipt :
      Flow.offCarrierTermGoesToZero flowPreservationReceipt ≡ true

    flowSummabilityFromReceipt :
      Flow.summableForHsWithS>0 flowPreservationReceipt ≡ true

    thresholdReceipt :
      Threshold.NSH118ThresholdReceipt

    thresholdAt11/8 :
      Threshold.carrierThreshold thresholdReceipt ≡ Threshold.nsCarrierThreshold

    thresholdAllowsLargeDataAt11/8 :
      Threshold.sAtLeastElevenEighthsLargeDataAllowed thresholdReceipt ≡ true

    combinedReceipt :
      Combined.NSCombinedRegularityMechanismReceipt

    combinedMechanismCandidate :
      Combined.globalRegularityFromCombination combinedReceipt
      ≡
      Combined.candidate

    largeDataGapReceipt :
      Gap.NSLargeDataGapReframingReceipt

    largeDataGapIsGlobalEnergyBound :
      Gap.correctApproach largeDataGapReceipt ≡ Gap.globalEnergyBound

    energyReceipt :
      Energy.NSCarrierEnergyInequalityReceipt

    lerayL2BoundRequired :
      Energy.lerayEnergyInequalityScoped energyReceipt ≡ true

    carrierStructuredU0InH118 :
      Bool

    carrierStructuredU0InH118IsTrue :
      carrierStructuredU0InH118 ≡ true

    l2MassLabel :
      String

    l2MassLabelIsCanonical :
      l2MassLabel ≡ "||u0||_L2 = M0"

    viscosityPositiveLabel :
      String

    viscosityPositiveLabelIsCanonical :
      viscosityPositiveLabel ≡ "nu > 0"

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ 11

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ 8

    dependencies :
      List NSGlobalH118BoundDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSGlobalH118BoundDependencies

    inequalityLabel :
      String

    inequalityLabelIsCanonical :
      inequalityLabel ≡ nsGlobalH118BoundInequalityLabel

    eMaxLabel :
      String

    eMaxLabelIsCanonical :
      eMaxLabel ≡ eMaxFormulaLabel

    eLowEHighSplitRecorded :
      Bool

    eLowEHighSplitRecordedIsTrue :
      eLowEHighSplitRecorded ≡ true

    boundFiniteForEachFixedPositiveNu :
      Bool

    boundFiniteForEachFixedPositiveNuIsTrue :
      boundFiniteForEachFixedPositiveNu ≡ true

    boundDivergesAsNuToZero :
      Bool

    boundDivergesAsNuToZeroIsTrue :
      boundDivergesAsNuToZero ≡ true

    adjacentOnlyStructureRequired :
      Bool

    adjacentOnlyStructureRequiredIsTrue :
      adjacentOnlyStructureRequired ≡ true

    lerayL2BoundRequiredFlag :
      Bool

    lerayL2BoundRequiredFlagIsTrue :
      lerayL2BoundRequiredFlag ≡ true

    prodiSerrinRoute :
      List NSProdiSerrinRouteStep

    prodiSerrinRouteIsCanonical :
      prodiSerrinRoute ≡ canonicalNSProdiSerrinRoute

    prodiSerrinRouteLabel :
      String

    prodiSerrinRouteLabelIsCanonical :
      prodiSerrinRouteLabel ≡ nsGlobalH118ProdiSerrinRouteLabel

    finiteTRegularityCandidate :
      Bool

    finiteTRegularityCandidateIsTrue :
      finiteTRegularityCandidate ≡ true

    globalSmoothSolutionCandidate :
      Bool

    globalSmoothSolutionCandidateIsTrue :
      globalSmoothSolutionCandidate ≡ true

    bernoulliBandRigourPending :
      Bool

    bernoulliBandRigourPendingIsTrue :
      bernoulliBandRigourPending ≡ true

    globalH118BoundFullyProved :
      Bool

    globalH118BoundFullyProvedIsFalseHere :
      globalH118BoundFullyProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsGlobalH118BoundStatement

    promotionFlags :
      List NSGlobalH118BoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSGlobalH118BoundReceipt public

canonicalNSGlobalH118BoundReceipt :
  NSGlobalH118BoundReceipt
canonicalNSGlobalH118BoundReceipt =
  record
    { status =
        candidatePendingBernoulliRigour
    ; statusIsCandidatePendingBernoulliRigour =
        refl
    ; adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyStructureRequiredFromReceipt =
        refl
    ; adjacentOnlyNoClayPromotion =
        refl
    ; flowPreservationReceipt =
        Flow.canonicalNSFlowPreservationBoundReceipt
    ; flowSuppressionFromReceipt =
        refl
    ; flowSummabilityFromReceipt =
        refl
    ; thresholdReceipt =
        Threshold.canonicalNSH118ThresholdReceipt
    ; thresholdAt11/8 =
        refl
    ; thresholdAllowsLargeDataAt11/8 =
        refl
    ; combinedReceipt =
        Combined.canonicalNSCombinedRegularityMechanismReceipt
    ; combinedMechanismCandidate =
        refl
    ; largeDataGapReceipt =
        Gap.canonicalNSLargeDataGapReframingReceipt
    ; largeDataGapIsGlobalEnergyBound =
        refl
    ; energyReceipt =
        Energy.canonicalNSCarrierEnergyInequalityReceipt
    ; lerayL2BoundRequired =
        refl
    ; carrierStructuredU0InH118 =
        true
    ; carrierStructuredU0InH118IsTrue =
        refl
    ; l2MassLabel =
        "||u0||_L2 = M0"
    ; l2MassLabelIsCanonical =
        refl
    ; viscosityPositiveLabel =
        "nu > 0"
    ; viscosityPositiveLabelIsCanonical =
        refl
    ; sobolevNumerator =
        11
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        8
    ; sobolevDenominatorIs8 =
        refl
    ; dependencies =
        canonicalNSGlobalH118BoundDependencies
    ; dependenciesAreCanonical =
        refl
    ; inequalityLabel =
        nsGlobalH118BoundInequalityLabel
    ; inequalityLabelIsCanonical =
        refl
    ; eMaxLabel =
        eMaxFormulaLabel
    ; eMaxLabelIsCanonical =
        refl
    ; eLowEHighSplitRecorded =
        true
    ; eLowEHighSplitRecordedIsTrue =
        refl
    ; boundFiniteForEachFixedPositiveNu =
        true
    ; boundFiniteForEachFixedPositiveNuIsTrue =
        refl
    ; boundDivergesAsNuToZero =
        true
    ; boundDivergesAsNuToZeroIsTrue =
        refl
    ; adjacentOnlyStructureRequired =
        true
    ; adjacentOnlyStructureRequiredIsTrue =
        refl
    ; lerayL2BoundRequiredFlag =
        true
    ; lerayL2BoundRequiredFlagIsTrue =
        refl
    ; prodiSerrinRoute =
        canonicalNSProdiSerrinRoute
    ; prodiSerrinRouteIsCanonical =
        refl
    ; prodiSerrinRouteLabel =
        nsGlobalH118ProdiSerrinRouteLabel
    ; prodiSerrinRouteLabelIsCanonical =
        refl
    ; finiteTRegularityCandidate =
        true
    ; finiteTRegularityCandidateIsTrue =
        refl
    ; globalSmoothSolutionCandidate =
        true
    ; globalSmoothSolutionCandidateIsTrue =
        refl
    ; bernoulliBandRigourPending =
        true
    ; bernoulliBandRigourPendingIsTrue =
        refl
    ; globalH118BoundFullyProved =
        false
    ; globalH118BoundFullyProvedIsFalseHere =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsGlobalH118BoundStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "A6 combines A1-A5 plus Leray L2 energy"
        ∷ "Scope: carrier-structured u0 in H^{11/8} with ||u0||_L2=M0 and nu>0"
        ∷ "Bound: ||u(t)||^2_H118 <= E_low+E_high <= E_MAX(nu,M0,p)"
        ∷ "E_MAX formula includes M0^2*(C/nu)^{11/4}/(p^{11/4}-1)+2E(0)+2C^2 M0^2 (C/nu)^{11/4-2}/(nu^2(1-p^{-2}))"
        ∷ "E_MAX is finite for each fixed nu>0 and diverges as nu->0"
        ∷ "Adjacent-only structure and Leray L2 bound are required"
        ∷ "Prodi-Serrin route: H118 bound -> L^{16/7}_t L^{24}_x -> finite-T smoothness -> T->infty candidate"
        ∷ "Status: candidate pending Bernoulli rigour"
        ∷ "Clay promotion remains false"
        ∷ []
    }

canonicalNSGlobalH118BoundStatusIsCandidate :
  status canonicalNSGlobalH118BoundReceipt
  ≡
  candidatePendingBernoulliRigour
canonicalNSGlobalH118BoundStatusIsCandidate =
  refl

canonicalNSGlobalH118BoundFormulaRecorded :
  eMaxLabel canonicalNSGlobalH118BoundReceipt
  ≡
  eMaxFormulaLabel
canonicalNSGlobalH118BoundFormulaRecorded =
  refl

canonicalNSGlobalH118BoundFiniteForFixedNu :
  boundFiniteForEachFixedPositiveNu canonicalNSGlobalH118BoundReceipt
  ≡
  true
canonicalNSGlobalH118BoundFiniteForFixedNu =
  refl

canonicalNSGlobalH118BoundDivergesAsNuToZero :
  boundDivergesAsNuToZero canonicalNSGlobalH118BoundReceipt
  ≡
  true
canonicalNSGlobalH118BoundDivergesAsNuToZero =
  refl

canonicalNSGlobalH118ProdiSerrinRouteRecorded :
  prodiSerrinRoute canonicalNSGlobalH118BoundReceipt
  ≡
  canonicalNSProdiSerrinRoute
canonicalNSGlobalH118ProdiSerrinRouteRecorded =
  refl

canonicalNSGlobalH118BoundPendingBernoulliRigour :
  bernoulliBandRigourPending canonicalNSGlobalH118BoundReceipt
  ≡
  true
canonicalNSGlobalH118BoundPendingBernoulliRigour =
  refl

canonicalNSGlobalH118BoundDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSGlobalH118BoundReceipt
  ≡
  false
canonicalNSGlobalH118BoundDoesNotPromoteClay =
  refl

nsGlobalH118BoundNoPromotion :
  NSGlobalH118BoundPromotion →
  ⊥
nsGlobalH118BoundNoPromotion =
  nsGlobalH118BoundPromotionImpossibleHere
