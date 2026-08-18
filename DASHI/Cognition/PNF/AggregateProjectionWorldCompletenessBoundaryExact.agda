module DASHI.Cognition.PNF.AggregateProjectionWorldCompletenessBoundaryExact where

------------------------------------------------------------------------
-- REPO-NATIVE DETERMINISTIC COMPRESSION WELD
--
-- This module deliberately stops before any probabilistic limit theorem.
-- It combines three already-independent DASHI facts:
--
-- 1. Base369InteractionAntipodalFibreExact gives a many-to-one aggregate on
--    the literal 27^3 = 3^9 interaction/appraisal carrier;
-- 2. ConditionalNormalizationBoundary gives a selected subset which carries
--    unit mass only after conditional renormalisation, not in the cohort;
-- 3. QueryFactorisationSufficiency gives a quotient exactly sufficient for
--    every authorised present query while refusing to manufacture world
--    coverage.
--
-- Thus aggregate regularity, normalized unit mass, and query sufficiency are
-- differently typed surfaces.  A future LLN/CLT theorem may describe a
-- statistic's concentration, but concentration cannot by itself supply an
-- inverse/reopening map for the aggregate fibre or a world-coverage witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.ConditionalNormalizationBoundary as Normalization
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction

------------------------------------------------------------------------
-- Literal aggregate fibre collision on the 3^9 carrier.
------------------------------------------------------------------------

aggregateCollision :
  Interaction.aggregateSum Interaction.structuralZeroRound
  ≡ Interaction.aggregateSum Interaction.cancellationZeroRound
aggregateCollision =
  proj₁ Interaction.cancellationToNeutralDoesNotImplyTrivialFineState

aggregateCollisionFineStatesDistinct :
  Interaction.structuralZeroRound ≡ Interaction.cancellationZeroRound → ⊥
aggregateCollisionFineStatesDistinct =
  proj₂ Interaction.cancellationToNeutralDoesNotImplyTrivialFineState

------------------------------------------------------------------------
-- Existing conditional-normalisation countermodel, reused literally.
------------------------------------------------------------------------

conditionalSubsetRenormalizesToUnit :
  Normalization.ConditionalNormalizationCounterexample
conditionalSubsetRenormalizesToUnit =
  Normalization.canonicalConditionalNormalizationCounterexample

------------------------------------------------------------------------
-- Existing exact query-sufficient quotient, reused literally.
------------------------------------------------------------------------

presentQueryProjectionIsSufficient :
  Query.StaticSufficient Query.demoQuestions Query.demoProject
presentQueryProjectionIsSufficient = Query.demoProjectionIsStaticallySufficient

querySufficiencyCannotCreateWorldCoverage :
  Query.StaticSufficiencyWorldCoveragePermission → ⊥
querySufficiencyCannotCreateWorldCoverage =
  Query.staticSufficiencyCannotManufactureWorldCoverage

------------------------------------------------------------------------
-- One package containing all three deterministic facts simultaneously.
------------------------------------------------------------------------

record DeterministicCompressionSeparation : Set₁ where
  constructor deterministicCompressionSeparation
  field
    aggregateSurfaceHasNontrivialFibre :
      Interaction.aggregateSum Interaction.structuralZeroRound
      ≡ Interaction.aggregateSum Interaction.cancellationZeroRound
      × (Interaction.structuralZeroRound
          ≡ Interaction.cancellationZeroRound → ⊥)
    conditionalUnitDoesNotMeanCohortUnit :
      Normalization.ConditionalNormalizationCounterexample
    authorisedPresentQueryFactorsExactly :
      Query.StaticSufficient Query.demoQuestions Query.demoProject
    staticSufficiencyStillCannotMintCoverage :
      Query.StaticSufficiencyWorldCoveragePermission → ⊥

open DeterministicCompressionSeparation public

canonicalDeterministicCompressionSeparation :
  DeterministicCompressionSeparation
canonicalDeterministicCompressionSeparation =
  deterministicCompressionSeparation
    Interaction.cancellationToNeutralDoesNotImplyTrivialFineState
    Normalization.canonicalConditionalNormalizationCounterexample
    Query.demoProjectionIsStaticallySufficient
    Query.staticSufficiencyCannotManufactureWorldCoverage

record AggregateProjectionWorldCompletenessBoundary : Set where
  field
    aggregateEqualityImpliesFineIdentity : Bool
    conditionalUnitImpliesWholeCohort : Bool
    staticQuerySufficiencyImpliesWorldCoverage : Bool
    concentrationWouldReopenAggregateFibreWithoutResidual : Bool
    centralLimitTheoremConstructedHere : Bool

canonicalAggregateProjectionWorldCompletenessBoundary :
  AggregateProjectionWorldCompletenessBoundary
canonicalAggregateProjectionWorldCompletenessBoundary = record
  { aggregateEqualityImpliesFineIdentity = false
  ; conditionalUnitImpliesWholeCohort = false
  ; staticQuerySufficiencyImpliesWorldCoverage = false
  ; concentrationWouldReopenAggregateFibreWithoutResidual = false
  ; centralLimitTheoremConstructedHere = false
  }
