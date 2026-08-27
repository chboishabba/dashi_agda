module DASHI.Mathematics.NumberTheory.PartitionHardyRamanujanErdosBridgeExact where

------------------------------------------------------------------------
-- Partition asymptotics integration surface.
--
-- This owner connects the finite partition/Euler coefficient bridge to the
-- historically distinct Hardy--Ramanujan, Erdos and Newman routes.  Analytic
-- promotion remains explicit and typed.
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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)

import DASHI.Mathematics.NumberTheory.PartitionGeneratingFunctionExact as GF
import DASHI.Mathematics.NumberTheory.PartitionAsymptoticRouteSeparationExact as Routes
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact as Erdos
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopUpperMajorantBoundaryExact as ErdosUpper
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as BishopSeries
import DASHI.Foundations.SpectralCountingComplexity as Counting
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The finite coefficient bridge is closed on its current certified prefix.

partitionPrefix : List Nat
partitionPrefix = GF.partitionCoefficientPrefix

eulerPrefix : List Nat
eulerPrefix = GF.eulerProductCoefficientPrefix

finitePartitionEulerBridge : partitionPrefix ≡ eulerPrefix
finitePartitionEulerBridge = GF.partitionPrefixEqualsEulerProductPrefix

finitePartitionEulerBridgeLevel : ProofLevel
finitePartitionEulerBridgeLevel = machineChecked

------------------------------------------------------------------------
-- Proof-method independence is closed at the route-identity level.

hardyRamanujanRouteIsNotErdosRoute :
  Routes.hardyRamanujanCircleRoute ≡ Routes.erdosElementaryRoute → ⊥
hardyRamanujanRouteIsNotErdosRoute = Routes.circleRouteIsNotErdosRoute

hardyRamanujanAndNewmanShareResolution :
  Routes.routeResolution Routes.hardyRamanujanCircleRoute
  ≡ Routes.routeResolution Routes.newmanElementaryConstantRoute
hardyRamanujanAndNewmanShareResolution = refl

routeSeparationLevel : ProofLevel
routeSeparationLevel = machineChecked

------------------------------------------------------------------------
-- Completion interface.
--
-- The Erdos upper stage is no longer one opaque Set.  It must supply concrete
-- Bishop majorant data and the typed recurrence/kernel/cancellation obligations
-- isolated by PartitionErdosBishopUpperMajorantBoundaryExact.

record PartitionAsymptoticCompletion : Set₁ where
  field
    generatingFunctionCompletion : GF.PartitionGeneratingFunctionCompletion

    -- Hardy--Ramanujan / complex route.
    circleDecomposition : Set
    majorArcEstimate : Set
    minorArcRemainderControl : Set
    etaTransformationInstantiated : Set
    hardyRamanujanSharpLimit : Set

    -- Erdos / elementary route.  The finite residual identity itself is
    -- derived from the explicit deletion-fibre system; the upper exponential
    -- stage is typed over the concrete Bishop carrier.
    erdosDeletionFibreSystem : Erdos.ErdosDeletionFibreSystem
    erdosUpperMajorantData : ErdosUpper.ErdosBishopUpperMajorantData
    erdosUpperMajorantAnalyticInputs :
      ErdosUpper.ErdosBishopUpperMajorantAnalyticInputs erdosUpperMajorantData

    -- Lower exponential control and convergence to a positive unknown
    -- prefactor remain to be decomposed at the same level of precision.
    elementaryRealLowerBound : Set
    positiveUnknownConstantLimit : Set

    -- Newman completion of the elementary constant.
    newmanConstantEvaluation : Set

    -- Common endpoint, with route provenance retained.
    commonSharpPartitionAsymptotic : Set

open PartitionAsymptoticCompletion public

------------------------------------------------------------------------
-- Any completed Erdos deletion-fibre owner automatically supplies the
-- arbitrary-n finite residual identity needed by the elementary route.

erdosCountingIdentity :
  (completion : PartitionAsymptoticCompletion) →
  (n : Nat) →
  n * Erdos.PartitionCount (erdosDeletionFibreSystem completion) n
  ≡ Erdos.ErdosResidualDoubleSum (erdosDeletionFibreSystem completion) n
erdosCountingIdentity completion =
  Erdos.erdosIdentityFromDeletionFibre
    (erdosDeletionFibreSystem completion)

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
