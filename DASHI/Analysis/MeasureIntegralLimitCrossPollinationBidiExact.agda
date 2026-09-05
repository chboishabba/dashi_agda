module DASHI.Analysis.MeasureIntegralLimitCrossPollinationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL

------------------------------------------------------------------------
-- BIDI CROSS-POLLINATION MAP FOR ANALYTIC LIMIT / INTEGRAL STRUCTURE
--
-- Neighboring lanes contribute theorem shapes, not application receipts.
-- The generic owner sits above all applications and each application must
-- instantiate it on its own measure, integrand, regulator and limit object.
------------------------------------------------------------------------

data AnalyticLane : Set where
  moonshineLane
  riemannLane
  yangMillsLane
  casimirLane
  navierStokesLane
  : AnalyticLane

data AnalyticShape : Set where
  regularisationParameterShape
  localConvergenceDomainShape
  measureIntegrabilityShape
  dominationShape
  operationInterchangeShape
  parameterisedLimitShape
  cutoffRemovalShape
  subtractionBeforeLimitShape
  : AnalyticShape

record AnalyticCrossPollinationEdge : Set where
  field
    source target : AnalyticLane
    shape : AnalyticShape
    theoremShapeReusable : Bool
    applicationReceiptReusable : Bool
    reading : String

open AnalyticCrossPollinationEdge public

moonshineToGenericRegularisation : AnalyticCrossPollinationEdge
moonshineToGenericRegularisation = record
  { source = moonshineLane
  ; target = casimirLane
  ; shape = regularisationParameterShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse explicit regularisation-parameter and convergence-domain architecture; Moonshine theta-integral convergence is not a Casimir receipt."
  }

riemannToGenericInterchange : AnalyticCrossPollinationEdge
riemannToGenericInterchange = record
  { source = riemannLane
  ; target = casimirLane
  ; shape = operationInterchangeShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse transform/interchange obligation discipline; Riemann Poisson receipts do not prove Casimir sum-integral or limit-integral exchange."
  }

yangMillsToGenericCutoff : AnalyticCrossPollinationEdge
yangMillsToGenericCutoff = record
  { source = yangMillsLane
  ; target = casimirLane
  ; shape = cutoffRemovalShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse explicit cutoff-removal obligation structure; exact eventual stabilization is not a Casimir dominated-limit theorem."
  }

casimirToGenericSubtractionBeforeLimit : AnalyticCrossPollinationEdge
casimirToGenericSubtractionBeforeLimit = record
  { source = casimirLane
  ; target = casimirLane
  ; shape = subtractionBeforeLimitShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = true
  ; reading = "Casimir motivates the generic matched-difference-before-limit theorem shape once represented application-neutrally."
  }

navierStokesToGenericParameterizedIntegral : AnalyticCrossPollinationEdge
navierStokesToGenericParameterizedIntegral = record
  { source = navierStokesLane
  ; target = casimirLane
  ; shape = parameterisedLimitShape
  ; theoremShapeReusable = true
  ; applicationReceiptReusable = false
  ; reading = "Reuse time-parameter/integral bookkeeping shape only; Navier-Stokes integral estimates do not close Casimir transverse measure theory."
  }

------------------------------------------------------------------------
-- Reverse direction: any lane may consume the generic kernel, but only by
-- constructing a local problem and local receipts.
------------------------------------------------------------------------

record LocalMeasureIntegralConsumer : Set₁ where
  field
    lane : AnalyticLane
    problem : MIL.MeasureIntegralProblem
    localObligations : MIL.MeasureIntegralLimitObligations problem
    consumerReading : String

open LocalMeasureIntegralConsumer public

record LocalInterchangeConsumer : Set₁ where
  field
    lane : AnalyticLane
    problem : MIL.OperationInterchangeProblem
    localReceiptRequired : Set
    consumerReading : String

open LocalInterchangeConsumer public

------------------------------------------------------------------------
-- Sideways receipt leakage is forbidden.
------------------------------------------------------------------------

data MoonshineIntegralClosesCasimirPermission : Set where

data RiemannInterchangeClosesCasimirPermission : Set where

data YangMillsCutoffClosesCasimirMeasurePermission : Set where

data NavierStokesIntegralClosesCasimirPermission : Set where

moonshineReceiptCannotAutoCloseCasimir :
  MoonshineIntegralClosesCasimirPermission → ⊥
moonshineReceiptCannotAutoCloseCasimir ()

riemannReceiptCannotAutoCloseCasimir :
  RiemannInterchangeClosesCasimirPermission → ⊥
riemannReceiptCannotAutoCloseCasimir ()

yangMillsReceiptCannotAutoCloseCasimirMeasure :
  YangMillsCutoffClosesCasimirMeasurePermission → ⊥
yangMillsReceiptCannotAutoCloseCasimirMeasure ()

navierStokesReceiptCannotAutoCloseCasimir :
  NavierStokesIntegralClosesCasimirPermission → ⊥
navierStokesReceiptCannotAutoCloseCasimir ()

record MeasureIntegralCrossPollinationStatus : Set where
  field
    genericKernelOwned : Bool
    moonshineShapeDonorRegistered : Bool
    riemannShapeDonorRegistered : Bool
    yangMillsShapeDonorRegistered : Bool
    navierStokesShapeDonorRegistered : Bool
    casimirConsumerInterfaceOwned : Bool
    foreignReceiptsImported : Bool

    genericKernelOwnedIsTrue : genericKernelOwned ≡ true
    moonshineShapeDonorRegisteredIsTrue : moonshineShapeDonorRegistered ≡ true
    riemannShapeDonorRegisteredIsTrue : riemannShapeDonorRegistered ≡ true
    yangMillsShapeDonorRegisteredIsTrue : yangMillsShapeDonorRegistered ≡ true
    navierStokesShapeDonorRegisteredIsTrue : navierStokesShapeDonorRegistered ≡ true
    casimirConsumerInterfaceOwnedIsTrue : casimirConsumerInterfaceOwned ≡ true
    foreignReceiptsImportedIsFalse : foreignReceiptsImported ≡ false

open MeasureIntegralCrossPollinationStatus public

canonicalMeasureIntegralCrossPollinationStatus : MeasureIntegralCrossPollinationStatus
canonicalMeasureIntegralCrossPollinationStatus = record
  { genericKernelOwned = true
  ; moonshineShapeDonorRegistered = true
  ; riemannShapeDonorRegistered = true
  ; yangMillsShapeDonorRegistered = true
  ; navierStokesShapeDonorRegistered = true
  ; casimirConsumerInterfaceOwned = true
  ; foreignReceiptsImported = false
  ; genericKernelOwnedIsTrue = refl
  ; moonshineShapeDonorRegisteredIsTrue = refl
  ; riemannShapeDonorRegisteredIsTrue = refl
  ; yangMillsShapeDonorRegisteredIsTrue = refl
  ; navierStokesShapeDonorRegisteredIsTrue = refl
  ; casimirConsumerInterfaceOwnedIsTrue = refl
  ; foreignReceiptsImportedIsFalse = refl
  }
