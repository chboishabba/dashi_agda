{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVOptics.MultilayerReflectionCascadeExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- ZEISS publicly describes EUV Bragg mirrors using alternating silicon and
-- molybdenum multilayers and reports reflectivity up to about 70%.
--
-- This module does NOT attempt to reconstruct coating thicknesses, interface
-- roughness, incidence-angle tuning, capping layers, oxidation barriers or
-- current production deposition recipes.  It only gives a finite cascade for
-- an idealized equal-retention reflection chain.

record PercentRetention : Set where
  constructor percentRetention
  field
    numerator   : Nat
    denominator : Nat

open PercentRetention public

zeissPublicIdealMirrorRetention : PercentRetention
zeissPublicIdealMirrorRetention = percentRetention 70 100

pow : Nat → Nat → Nat
pow x zero = 1
pow x (suc n) = x * pow x n

record ReflectionCascade : Set where
  constructor reflectionCascade
  field
    mirrorCount : Nat
    retention   : PercentRetention

open ReflectionCascade public

CascadeNumerator : ReflectionCascade → Nat
CascadeNumerator c = pow (numerator (retention c)) (mirrorCount c)

CascadeDenominator : ReflectionCascade → Nat
CascadeDenominator c = pow (denominator (retention c)) (mirrorCount c)

-- A six-reflection idealized chain at 70% per reflection retains
--
--   0.7^6 = 117649 / 1000000 ≈ 11.7649%.
--
-- This is an accounting fixture, not a statement that a particular ASML
-- optical path has exactly six 70%-reflective elements.

sixMirrorIdealCascade : ReflectionCascade
sixMirrorIdealCascade = reflectionCascade 6 zeissPublicIdealMirrorRetention

sixMirrorNumeratorExact : CascadeNumerator sixMirrorIdealCascade ≡ 117649
sixMirrorNumeratorExact = refl

sixMirrorDenominatorExact : CascadeDenominator sixMirrorIdealCascade ≡ 1000000
sixMirrorDenominatorExact = refl

-- The main scientific lesson owned here is multiplicative loss: even a high
-- single-mirror reflectivity compounds strongly over several reflections.
-- Actual source-to-wafer throughput needs the real optical topology and each
-- element's wavelength/angle/state-dependent transfer function.
