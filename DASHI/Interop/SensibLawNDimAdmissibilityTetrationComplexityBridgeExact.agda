module DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Admissibility
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Tetration
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as Monster369

AdmissibilityAxisAt : Nat → Set
AdmissibilityAxisAt = Tetration.ParetoAxisAt

admissibilityAxisCount : Nat → Nat
admissibilityAxisCount = Tetration.paretoAxisCount

AdmissibilityProfileAt : Nat → Set
AdmissibilityProfileAt n = AdmissibilityAxisAt n → SSP.SSPTrit

admissibilityAxisCountZero : admissibilityAxisCount zero ≡ 1
admissibilityAxisCountZero = Tetration.paretoAxisCountZero

admissibilityAxisCountOne : admissibilityAxisCount (suc zero) ≡ 9
admissibilityAxisCountOne = Tetration.paretoAxisCountOne

admissibilityAxisCountRecurrence :
  (n : Nat) →
  admissibilityAxisCount (suc n) ≡
  Hyper.powNat 9 (admissibilityAxisCount n)
admissibilityAxisCountRecurrence = Tetration.paretoAxisCountRecurrence

levelOneAdmissibilityProfileCountMatchesBase369 :
  Tetration.ternaryObjectiveProfileCount 1 ≡ Geometry.hyperfabricStateCount
levelOneAdmissibilityProfileCountMatchesBase369 =
  Tetration.levelOneTernaryProfilesMatchBase369FabricCount

record SelfIndexedAdmissibilityBraid : Set₁ where
  constructor selfIndexedAdmissibilityBraid
  field
    Level : Nat
    Stage : Set
    stageReference : Stage → String
    stateAt : Stage → AdmissibilityAxisAt Level → Admissibility.AdmissibilityState
    braidReference : String
open SelfIndexedAdmissibilityBraid public

record AdmissibilityComplexityBundle : Set₁ where
  constructor admissibilityComplexityBundle
  field
    admissibility : Admissibility.NDimAdmissibilityFibre
    complexity : Admissibility.FibreComplexityProfile admissibility
    complexityConsumerReference : String
    descriptionLengthIsOnlyOnePossibleAxis : Bool
    descriptionLengthIsOnlyOnePossibleAxisIsTrue :
      descriptionLengthIsOnlyOnePossibleAxis ≡ true
open AdmissibilityComplexityBundle public

record MDLAdmissibilityCompatibility : Set₁ where
  constructor mdlAdmissibilityCompatibility
  field
    Problem : MDL.ConsumerMDLProblem
    costs : MDL.CostHyperfabric Problem
    ndimView : NDim.NDimParetoView costs
    hardAdmissibilityPrecedesDescriptionRanking : Bool
    hardAdmissibilityPrecedesDescriptionRankingIsTrue :
      hardAdmissibilityPrecedesDescriptionRanking ≡ true
    consumerAdequacyPrecedesDescriptionRanking : Bool
    consumerAdequacyPrecedesDescriptionRankingIsTrue :
      consumerAdequacyPrecedesDescriptionRanking ≡ true
open MDLAdmissibilityCompatibility public

monster369LevelOneBoundary : Monster369.Monster369NDimParetoTetrationBoundary
monster369LevelOneBoundary = Monster369.canonicalMonster369NDimParetoTetrationBoundary

record AdmissibilityTetrationComplexityBoundary : Set where
  constructor admissibilityTetrationComplexityBoundary
  field
    fixedNAxisThreePowerNIsAutomaticallyTetration : Bool
    selfIndexingMayProduceTetrationalAxisGrowth : Bool
    levelOneNineAxesHave19683Profiles : Bool
    admissibilityAndComplexityAreSameCoordinate : Bool
    descriptionLengthMayOverrideHardAdmissibility : Bool
    omittedProjectedAxisIsAutomaticallyIrrelevant : Bool
    base369CarrierAutomaticallyCreatesMonsterSemantics : Bool

canonicalAdmissibilityTetrationComplexityBoundary :
  AdmissibilityTetrationComplexityBoundary
canonicalAdmissibilityTetrationComplexityBoundary =
  admissibilityTetrationComplexityBoundary
    false true true false false false false
