module DASHI.Biology.Agriculture.ConstructiveNitrogenTransportKernelExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE NITROGEN TRANSPORT KERNEL MATHEMATICS
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- This owner imports the application-neutral convergence mathematics developed
-- in the Moonshine/Analysis lane into the agriculture lane without importing
-- Moonshine semantics.
--
-- The stage equations are literal finite convolutions using the pre-existing
-- ConstructiveSeries convolution coefficient:
--
--   M_t = sum_{j=0}^t F_j K_M(t-j)
--   C_t = sum_{j=0}^t M_j K_C(t-j).
--
-- Route-specific tails then reuse ContractiveCompartmentTail:
--
--   actualRoute(n) <= majorantRoute(n)
--       + majorant tail vanishes
--       -> actual route tail vanishes.
--
-- A Bishop polynomial-geometric route majorant additionally has constructive
-- absolute convergence for every fixed degree:
--
--   scale * (n+1)^k * r^(n+1),   0 <= r < 1.
--
-- EMPIRICAL FIREWALL
--
-- No source currently imported here is asserted to obey such a kernel.
-- A source/model consumer must separately establish its pointwise bound,
-- route identity, time unit, scale, contraction ratio and observational scope.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.PolynomialGeometricTailDominationExact as Tail
import DASHI.Analysis.TailModulusCauchyBridgeExact as Bridge
import DASHI.Analysis.ContractiveCompartmentTailExact as Compartment
import DASHI.Analysis.BishopContractiveCompartmentSeriesExact as BishopCompartment

------------------------------------------------------------------------
-- Typed route / stage coordinates.
------------------------------------------------------------------------

data NitrogenTransportRoute : Set where
  livingBelowGroundRoute : NitrogenTransportRoute
  residueMineralisationRoute : NitrogenTransportRoute
  excretaRedistributionRoute : NitrogenTransportRoute
  soilStockReleaseRoute : NitrogenTransportRoute

data NitrogenTransportStage : Set where
  fixedNitrogenInput : NitrogenTransportStage
  accumulatedSystemNitrogen : NitrogenTransportStage
  mineralisedNitrogenStage : NitrogenTransportStage
  consumerCapturedNitrogen : NitrogenTransportStage

------------------------------------------------------------------------
-- Literal serial-compartment equations.
------------------------------------------------------------------------

mineralisedNitrogen :
  (R : Real.ConstructedOrderedCompleteReal) →
  (fixedInput : Nat → Real.Real R) →
  (mineralisationKernel : Nat → Real.Real R) →
  Nat →
  Real.Real R
mineralisedNitrogen R fixedInput mineralisationKernel =
  Series.convolutionCoefficient R fixedInput mineralisationKernel

capturedNitrogen :
  (R : Real.ConstructedOrderedCompleteReal) →
  (fixedInput : Nat → Real.Real R) →
  (mineralisationKernel : Nat → Real.Real R) →
  (captureKernel : Nat → Real.Real R) →
  Nat →
  Real.Real R
capturedNitrogen R fixedInput mineralisationKernel captureKernel =
  Series.convolutionCoefficient R
    (mineralisedNitrogen R fixedInput mineralisationKernel)
    captureKernel

record SerialNitrogenTransportSystem
    (R : Real.ConstructedOrderedCompleteReal) : Set₁ where
  field
    fixedInput : Nat → Real.Real R
    mineralisationKernel : Nat → Real.Real R
    captureKernel : Nat → Real.Real R

open SerialNitrogenTransportSystem public

systemMineralisedNitrogen :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  SerialNitrogenTransportSystem R →
  Nat →
  Real.Real R
systemMineralisedNitrogen {R} system =
  mineralisedNitrogen R
    (fixedInput system)
    (mineralisationKernel system)

systemCapturedNitrogen :
  ∀ {R : Real.ConstructedOrderedCompleteReal} →
  SerialNitrogenTransportSystem R →
  Nat →
  Real.Real R
systemCapturedNitrogen {R} system =
  capturedNitrogen R
    (fixedInput system)
    (mineralisationKernel system)
    (captureKernel system)

------------------------------------------------------------------------
-- Route-specific generic tail compiler.
------------------------------------------------------------------------

record NitrogenRouteTailProblem
    {Scalar : Set}
    (K : Tail.OrderedTailKernel Scalar)
    (S : Tail.TailSmallness K) : Set₁ where
  field
    route : NitrogenTransportRoute
    routeContribution : Nat → Scalar
    routeMajorant : Nat → Scalar

    routeBelowMajorant :
      ∀ index →
      Tail.LessEqual K
        (routeContribution index)
        (routeMajorant index)

    routeMajorantTailVanishes :
      Tail.TailVanishes K S routeMajorant

open NitrogenRouteTailProblem public

asContractiveCompartment :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  NitrogenRouteTailProblem K S →
  Compartment.ContractiveCompartmentProblem K S
asContractiveCompartment problem = record
  { Compartment.actualContribution = routeContribution problem
  ; Compartment.majorantContribution = routeMajorant problem
  ; Compartment.actualBelowMajorant = routeBelowMajorant problem
  ; Compartment.majorantTailVanishes = routeMajorantTailVanishes problem
  }

routeFiniteTailBelowMajorant :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : NitrogenRouteTailProblem K S) →
  ∀ start count →
  Tail.LessEqual K
    (Tail.finiteTail K
      (routeContribution problem) start count)
    (Tail.finiteTail K
      (routeMajorant problem) start count)
routeFiniteTailBelowMajorant problem =
  Compartment.actualFiniteTailBelowMajorant
    (asContractiveCompartment problem)

routeTailVanishes :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K} →
  (problem : NitrogenRouteTailProblem K S) →
  Tail.TailVanishes K S
    (routeContribution problem)
routeTailVanishes problem =
  Compartment.actualTailVanishes
    (asContractiveCompartment problem)

compileRouteCauchy :
  ∀ {Scalar : Set}
    {K : Tail.OrderedTailKernel Scalar}
    {S : Tail.TailSmallness K}
    {R : Real.ConstructedOrderedCompleteReal}
    {sequence : Real.Sequence R} →
  (problem : NitrogenRouteTailProblem K S) →
  Bridge.TailVanishesToCauchyBridge
    R K S (routeContribution problem) sequence →
  Real.IsCauchy R sequence
compileRouteCauchy problem bridge =
  Compartment.compileContractiveCompartmentCauchy
    (asContractiveCompartment problem)
    bridge

------------------------------------------------------------------------
-- Constructive Bishop polynomial-geometric route majorants.
------------------------------------------------------------------------

record BishopNitrogenRouteMajorant : Set where
  field
    route : NitrogenTransportRoute
    compartment :
      BishopCompartment.BishopPolynomialGeometricCompartment

open BishopNitrogenRouteMajorant public

bishopRouteMajorantTerm :
  BishopNitrogenRouteMajorant →
  Nat →
  BishopReal.ℝ
bishopRouteMajorantTerm problem =
  BishopCompartment.compartmentMajorantTerm
    (compartment problem)

bishopRouteMajorantConvergent :
  (problem : BishopNitrogenRouteMajorant) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (bishopRouteMajorantTerm problem))
bishopRouteMajorantConvergent problem =
  BishopCompartment.compartmentMajorantConvergent
    (compartment problem)

bishopRouteMajorantAbsolutelyConvergent :
  (problem : BishopNitrogenRouteMajorant) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (bishopRouteMajorantTerm problem)
bishopRouteMajorantAbsolutelyConvergent problem =
  BishopCompartment.compartmentMajorantAbsolutelyConvergent
    (compartment problem)


record BishopNitrogenRouteDominatedSeries : Set where
  field
    route : NitrogenTransportRoute
    dominatedSeries :
      BishopCompartment.BishopDominatedCompartmentSeries

open BishopNitrogenRouteDominatedSeries public

bishopRouteActualContribution :
  BishopNitrogenRouteDominatedSeries →
  Nat →
  BishopReal.ℝ
bishopRouteActualContribution problem =
  BishopCompartment.actualContribution
    (dominatedSeries problem)

bishopRouteActualSeriesConvergent :
  (problem : BishopNitrogenRouteDominatedSeries) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (bishopRouteActualContribution problem))
bishopRouteActualSeriesConvergent problem =
  BishopCompartment.dominatedCompartmentSeriesConvergent
    (dominatedSeries problem)

bishopRouteActualPartialSumsCauchy :
  (problem : BishopNitrogenRouteDominatedSeries) →
  BishopSequence._isCauchy
    (BishopSequence.SeriesOf
      (bishopRouteActualContribution problem))
bishopRouteActualPartialSumsCauchy problem =
  BishopCompartment.dominatedCompartmentPartialSumsCauchy
    (dominatedSeries problem)

------------------------------------------------------------------------
-- Mathematical / empirical boundary.
------------------------------------------------------------------------

record NitrogenTransportMathBoundary : Set where
  field
    finiteConvolutionEquationsOwned : Bool
    genericDominatedTailCompilerOwned : Bool
    genericTailToCauchyCompositionOwned : Bool
    arbitraryDegreeBishopMajorantConvergenceOwned : Bool
    dominatedActualRouteCauchyCompilerOwned : Bool

    empiricalKernelBoundAutomaticallyOwned : Bool
    geometricLawAssertedForQueenslandSources : Bool
    routeIdentityErasedByConvergenceProof : Bool
    absoluteConvergenceEqualsFertilizerReplacement : Bool

open NitrogenTransportMathBoundary public

canonicalNitrogenTransportMathBoundary : NitrogenTransportMathBoundary
canonicalNitrogenTransportMathBoundary = record
  { finiteConvolutionEquationsOwned = true
  ; genericDominatedTailCompilerOwned = true
  ; genericTailToCauchyCompositionOwned = true
  ; arbitraryDegreeBishopMajorantConvergenceOwned = true
  ; dominatedActualRouteCauchyCompilerOwned = true
  ; empiricalKernelBoundAutomaticallyOwned = false
  ; geometricLawAssertedForQueenslandSources = false
  ; routeIdentityErasedByConvergenceProof = false
  ; absoluteConvergenceEqualsFertilizerReplacement = false
  }
