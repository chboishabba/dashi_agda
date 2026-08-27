module DASHI.Environment.ThreeSistersLESRelationalComplementarityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as Kimmerer
import DASHI.Environment.LESResearchCrossPollinationRound7Exact as LES7

------------------------------------------------------------------------
-- THREE SISTERS / LES RELATIONAL COMPLEMENTARITY BRIDGE
--
-- This module links two distinct environmental theorem shapes:
--
--   (1) LES Round 7: history can change the continuation cone / present choice
--       even when a coarse current summary is the same;
--
--   (2) Three Sisters agronomy: the same crop components can have different
--       system-level outcomes depending on their relational arrangement.
--
-- These are related but not identical:
--
--   path dependence != ecological complementarity.
--
-- No private legal, commercial, agricultural, family, client, or case facts
-- are encoded here.  The management-history carrier is the synthetic public
-- LES witness already present in the repository.
------------------------------------------------------------------------

data SourceRole : Set where
  historicalThreeSistersProductivity
  rootForagingComplementarity
  : SourceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    role : SourceRole
    boundedReading : String

open SourceReference public

pleasantBurt2010 : SourceReference
pleasantBurt2010 =
  sourceReference
    "Jane Pleasant; Robert F. Burt"
    "Estimating Productivity of Traditional Iroquoian Cropping Systems from Field Experiments and Historical Literature"
    "Ethnobiology Letters 30(1):52-79"
    2010
    "10.2993/0278-0771-30.1.52"
    historicalThreeSistersProductivity
    "Provides field/historical evidence on productivity of traditional Iroquoian Three Sisters cropping; it does not supply DASHI non-factorability, game theory, or a universal polyculture-superiority theorem."

zhangPostmaYorkLynch2014 : SourceReference
zhangPostmaYorkLynch2014 =
  sourceReference
    "Chaochun Zhang; Johannes A. Postma; Larry M. York; Jonathan P. Lynch"
    "Root foraging elicits niche complementarity-dependent yield advantage in the ancient 'three sisters' (maize/bean/squash) polyculture"
    "Annals of Botany 114(8):1719-1733"
    2014
    "10.1093/aob/mcu191"
    rootForagingComplementarity
    "Reports greater yield and biomass on a land-equivalent basis in the studied Three Sisters polyculture and attributes much of the biomass advantage to complementarity rather than selection; no universal or game-theoretic claim is inferred."

------------------------------------------------------------------------
-- Relational arrangement witness.
--
-- The coarse component projection keeps only 'maize + bean + squash present'.
-- It forgets whether those components are represented as a co-cultivated
-- relational system or merely as isolated component stands.  The system-level
-- outcome is therefore not recoverable from the component list alone.
------------------------------------------------------------------------

data CroppingRelation : Set where
  isolatedComponentStands coCultivatedThreeSisters : CroppingRelation

data ComponentInventory : Set where
  maizeBeanSquashPresent : ComponentInventory

data RelationalOutcomeCode : Set where
  isolatedReferenceOutcome complementarityAdvantageObserved : RelationalOutcomeCode

componentInventory : CroppingRelation → ComponentInventory
componentInventory _ = maizeBeanSquashPresent

relationalOutcome : CroppingRelation → RelationalOutcomeCode
relationalOutcome isolatedComponentStands = isolatedReferenceOutcome
relationalOutcome coCultivatedThreeSisters = complementarityAdvantageObserved

sameComponentsDifferentRelationalOutcome :
  NonFactor.NonFactorabilityWitness componentInventory relationalOutcome
sameComponentsDifferentRelationalOutcome =
  NonFactor.nonFactorabilityWitness
    isolatedComponentStands
    coCultivatedThreeSisters
    refl
    (λ ())

componentInventoryAloneCannotRecoverRelationalOutcome :
  NonFactor.FactorsThrough componentInventory relationalOutcome → ⊥
componentInventoryAloneCannotRecoverRelationalOutcome =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    sameComponentsDifferentRelationalOutcome

------------------------------------------------------------------------
-- Orthogonal LES history axis.
--
-- This deliberately does not turn Three Sisters complementarity into path
-- dependence.  The existing LES witness owns management-history effects;
-- this bridge merely records that both axes may matter in one environmental
-- planning state.
------------------------------------------------------------------------

record AgroecologicalPlanningState : Set where
  constructor agroecologicalPlanningState
  field
    managementHistory : LES7.ManagementHistory
    croppingRelation : CroppingRelation

open AgroecologicalPlanningState public

syntheticShortIsolated : AgroecologicalPlanningState
syntheticShortIsolated =
  agroecologicalPlanningState
    LES7.shortHorizonConfiguration
    isolatedComponentStands

syntheticLongRelated : AgroecologicalPlanningState
syntheticLongRelated =
  agroecologicalPlanningState
    LES7.longHorizonConfiguration
    coCultivatedThreeSisters

kimmererInterpretiveReading : String
kimmererInterpretiveReading =
  "Kimmerer's Three Sisters teaching motivates attention to reciprocal and relational ecological organization. The empirical complementarity claim here is attributed to agronomy sources, while the factorisation theorem is a DASHI formal extension."

kimmererBridgeSourceReading : String
kimmererBridgeSourceReading = Kimmerer.braidingReading

------------------------------------------------------------------------
-- Attribution / privacy boundary.
------------------------------------------------------------------------

record ThreeSistersLESBoundary : Set where
  constructor threeSistersLESBoundary
  field
    pathDependenceIsSameAsComplementarity : Bool
    pathDependenceIsSameAsComplementarityIsFalse :
      pathDependenceIsSameAsComplementarity ≡ false

    sameComponentsGuaranteeSameSystemOutcome : Bool
    sameComponentsGuaranteeSameSystemOutcomeIsFalse :
      sameComponentsGuaranteeSameSystemOutcome ≡ false

    threeSistersEvidenceProvesUniversalPolycultureSuperiority : Bool
    threeSistersEvidenceProvesUniversalPolycultureSuperiorityIsFalse :
      threeSistersEvidenceProvesUniversalPolycultureSuperiority ≡ false

    threeSistersEvidenceIsGameTheoryProof : Bool
    threeSistersEvidenceIsGameTheoryProofIsFalse :
      threeSistersEvidenceIsGameTheoryProof ≡ false

    kimmererIsCreditedWithDASHINonFactorability : Bool
    kimmererIsCreditedWithDASHINonFactorabilityIsFalse :
      kimmererIsCreditedWithDASHINonFactorability ≡ false

    privateCaseFactsEncoded : Bool
    privateCaseFactsEncodedIsFalse :
      privateCaseFactsEncoded ≡ false

canonicalThreeSistersLESBoundary : ThreeSistersLESBoundary
canonicalThreeSistersLESBoundary =
  threeSistersLESBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
