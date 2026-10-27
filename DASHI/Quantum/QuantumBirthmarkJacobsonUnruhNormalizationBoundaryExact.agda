{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonUnruhNormalizationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- BISOGNANO-WICHMANN -> UNRUH NORMALIZATION BOUNDARY
--
-- The sibling Lean producer now pays only the scalar normalization step:
-- once a selected wedge/vacuum modular flow is physically identified with
-- Lorentz boosts with the Bisognano-Wichmann 2*pi modular normalization, and
-- the boost parameter is identified with accelerated proper time at surface
-- gravity/acceleration kappa, the inverse-temperature conversion gives
--
--   T = hbar * kappa / (2*pi)
--
-- in c = k_B = 1 units.
--
-- This file does NOT import the Lean proof term into Agda. It records the
-- cross-kernel theorem-source boundary and keeps the genuinely physical AQFT
-- premises live.
------------------------------------------------------------------------

BisognanoWichmann1975 : Source.AttributedSource
BisognanoWichmann1975 =
  Source.mkDOISource
    "Joseph J. Bisognano; Eyvind H. Wichmann"
    "On the duality condition for a Hermitian scalar field"
    "Journal of Mathematical Physics 16, 985-1007"
    "1975"
    "10.1063/1.522605"
    "https://doi.org/10.1063/1.522605"
    Source.academicArticleSource
    "Primary Bisognano-Wichmann source for the wedge modular/Lorentz structure; citation does not import an Agda theorem."
    Source.publicAttribution

BisognanoWichmann1976 : Source.AttributedSource
BisognanoWichmann1976 =
  Source.mkDOISource
    "Joseph J. Bisognano; Eyvind H. Wichmann"
    "On the duality condition for quantum fields"
    "Journal of Mathematical Physics 17, 303-321"
    "1976"
    "10.1063/1.522898"
    "https://doi.org/10.1063/1.522898"
    Source.academicArticleSource
    "General quantum-field extension of the Bisognano-Wichmann wedge modular theorem; citation does not import an Agda theorem."
    Source.publicAttribution

record UnruhNormalizationCrossKernelBoundary : Set where
  constructor unruhNormalizationCrossKernelBoundary
  field
    boostKMSNormalizationSourceWritten : Bool
    siblingLeanScalarNormalizationProducerExists : Bool
    physicalBisognanoWichmannStillRequired : Bool
    physicalWedgeVacuumStateStillRequired : Bool
    accelerationProperTimeIdentificationStillRequired : Bool
    modularKMSAnalyticStripStillRequired : Bool
    scalarNormalizationDoesNotProveAQFTTheorem : Bool
    unruhTemperatureDoesNotIdentifyBirthmarkObservable : Bool
    unruhTemperatureDoesNotIdentifyRyuTakayanagiEntropy : Bool
    scope : String

canonicalUnruhNormalizationCrossKernelBoundary :
  UnruhNormalizationCrossKernelBoundary
canonicalUnruhNormalizationCrossKernelBoundary =
  unruhNormalizationCrossKernelBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    "The 2*pi boost-KMS to proper-time Unruh scalar normalization is source-written in sibling Lean. Physical Bisognano-Wichmann/wedge-state/KMS and acceleration-to-proper-time identification remain independent same-object QFT/geometric payments."

boostKMSNormalizationSourceWritten : Bool
boostKMSNormalizationSourceWritten = true

physicalBisognanoWichmannStillRequired : Bool
physicalBisognanoWichmannStillRequired = true

accelerationProperTimeIdentificationStillRequired : Bool
accelerationProperTimeIdentificationStillRequired = true

modularKMSAnalyticStripStillRequired : Bool
modularKMSAnalyticStripStillRequired = true

unruhScalarNormalizationDoesNotCloseQFT : Bool
unruhScalarNormalizationDoesNotCloseQFT = true
