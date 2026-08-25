module DASHI.Mathematics.NumberTheory.PartitionHardyRamanujanErdosBridgeExact where

------------------------------------------------------------------------
-- Partition asymptotics integration surface.
--
-- This owner connects the already-machine-checked finite partition/Euler
-- coefficient bridge to the two historically distinct asymptotic routes.
-- It deliberately does not promote the infinite generating-function or
-- asymptotic boundaries until their analytic obligations are discharged.
--
-- Sources:
--   G. H. Hardy and S. Ramanujan (1918), "Asymptotic Formulae in
--   Combinatory Analysis", Proc. London Math. Soc. (2) 17, 75--115.
--   DOI: 10.1112/plms/s2-17.1.75.
--
--   P. Erdos (1942), "On an Elementary Proof of Some Asymptotic Formulas in
--   the Theory of Partitions", Ann. Math. (2) 43, 437--450.
--   DOI: 10.2307/1968802.
--
--   D. J. Newman (1951), "The Evaluation of the Constant in the Formula for
--   the Number of Partitions of n", Amer. J. Math. 73, 599--601.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Mathematics.NumberTheory.PartitionGeneratingFunctionExact as GF
import DASHI.Mathematics.NumberTheory.PartitionAsymptoticRouteSeparationExact as Routes
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as BishopSeries
import DASHI.Foundations.SpectralCountingComplexity as Counting
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The finite combinatorial bridge is already closed.

partitionPrefix : List Nat
partitionPrefix = GF.partitionCoefficientPrefix

eulerPrefix : List Nat
eulerPrefix = GF.eulerProductCoefficientPrefix

finitePartitionEulerBridge : partitionPrefix ≡ eulerPrefix
finitePartitionEulerBridge = GF.partitionPrefixEqualsEulerProductPrefix

finitePartitionEulerBridgeLevel : ProofLevel
finitePartitionEulerBridgeLevel = machineChecked

------------------------------------------------------------------------
-- Proof-method independence is also closed at the route-identity level.

hardyRamanujanRouteIsNotErdosRoute :
  Routes.hardyRamanujanCircleRoute ≡ Routes.erdosElementaryRoute → ⊥
hardyRamanujanRouteIsNotErdosRoute = Routes.circleRouteIsNotErdosRoute

hardyRamanujanAndNewmanShareResolution :
  Routes.routeResolution Routes.hardyRamanujanCircleRoute
  ≡ Routes.routeResolution Routes.newmanElementaryConstantRoute
hardyRamanujanAndNewmanShareResolution = GF.refl

routeSeparationLevel : ProofLevel
routeSeparationLevel = machineChecked

------------------------------------------------------------------------
-- Cross-pollination dependencies.
--
-- BishopPowerSeriesElementaryBridgeExact already owns constructive convergent
-- series and the exp/log elementary-function boundary.  SpectralCountingComplexity
-- already owns the repo pattern "principal term + controlled remainder".
-- Importing those owners here records the intended reuse; neither one is
-- claimed to prove the partition-specific estimates by itself.

record PartitionAsymptoticCompletion : Set₁ where
  field
    generatingFunctionCompletion : GF.PartitionGeneratingFunctionCompletion

    -- Hardy--Ramanujan / complex route.
    circleDecomposition : Set
    majorArcEstimate : Set
    minorArcRemainderControl : Set
    etaTransformationInstantiated : Set
    hardyRamanujanSharpLimit : Set

    -- Erdos / elementary route.
    erdosCountingIdentity : Set
    elementaryRealUpperBound : Set
    elementaryRealLowerBound : Set
    positiveUnknownConstantLimit : Set

    -- Newman completion of the elementary constant.
    newmanConstantEvaluation : Set

    -- Common endpoint, with route provenance retained.
    commonSharpPartitionAsymptotic : Set

open PartitionAsymptoticCompletion public

partitionAsymptoticCompletionLevel : ProofLevel
partitionAsymptoticCompletionLevel = conditional

------------------------------------------------------------------------
-- Promotion boundary: finite coefficient agreement is not the asymptotic.

data PartitionPromotionStage : Set where
  finiteCoefficientStage : PartitionPromotionStage
  infiniteGeneratingFunctionStage : PartitionPromotionStage
  sharpAsymptoticStage : PartitionPromotionStage

finiteStageIsNotSharpAsymptotic :
  finiteCoefficientStage ≡ sharpAsymptoticStage → ⊥
finiteStageIsNotSharpAsymptotic ()

infiniteGeneratingFunctionIsNotSharpAsymptotic :
  infiniteGeneratingFunctionStage ≡ sharpAsymptoticStage → ⊥
infiniteGeneratingFunctionIsNotSharpAsymptotic ()
