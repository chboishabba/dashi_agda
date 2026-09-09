module DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Admissibility
import DASHI.Biology.SelfIndexedParetoHyperfabricTetrationExact as Tetration
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster369NDimParetoTetrationBridgeExact as Monster369

------------------------------------------------------------------------
-- N-DIMENSIONAL ADMISSIBILITY -> SELF-INDEXED TOWER
--
-- A fixed n-axis admissibility fibre has 3^n nominal balanced-trit profiles.
-- That alone is ordinary exponential profile growth, not tetration.
--
-- Genuine tetrational growth begins only when the level-n carrier itself
-- indexes the independently declared axes of level n+1.  The repository's
-- SelfIndexedPareto owner already owns exactly that recurrence:
--
--   A_0 = 1
--   A_(n+1) = 9 ^ A_n.
--
-- This module does not define another tower. It reuses that owner and reads
-- each self-indexed Pareto axis as one admissibility coordinate.
------------------------------------------------------------------------

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
  DASHI.Biology.TernaryHypercubeHyperfabricExact.powNat 9
    (admissibilityAxisCount n)
admissibilityAxisCountRecurrence = Tetration.paretoAxisCountRecurrence

levelOneAdmissibilityProfileCountMatchesBase369 :
  Tetration.ternaryObjectiveProfileCount 1 ≡ Geometry.hyperfabricStateCount
levelOneAdmissibilityProfileCountMatchesBase369 =
  Tetration.levelOneTernaryProfilesMatchBase369FabricCount

------------------------------------------------------------------------
-- BRAID / TIME VIEW
--
-- A proof-search/acquisition history is a stage-indexed trajectory through the
-- same axis family. No state is erased merely because a later stage admits it.
------------------------------------------------------------------------

record SelfIndexedAdmissibilityBraid : Set₁ where
  constructor selfIndexedAdmissibilityBraid
  field
    Level : Nat
    Stage : Set
    stageReference : Stage → String
    stateAt : Stage → AdmissibilityAxisAt Level → Admissibility.AdmissibilityState
    braidReference : String
open SelfIndexedAdmissibilityBraid public

------------------------------------------------------------------------
-- COMPLEXITY IS A SECOND N-DIMENSIONAL FIBRE
--
-- The admissibility state and its execution/representation/proof costs are not
-- collapsed. MDL may rank only after hard admissibility and consumer adequacy.
-- Cost axes remain application-declared, exactly as the existing MDL/Pareto
-- owner requires.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- MONSTER / 369 BOUNDARY
--
-- Level one has nine axes and 3^9 profiles, hence the exact Base369 carrier
-- count. The existing Monster369 bridge permits this chart seam but explicitly
-- refuses to turn signed/carrier symmetry into semantic Pareto automorphism or
-- authority without a further receipt.
------------------------------------------------------------------------

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
