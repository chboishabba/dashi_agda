module Ontology.Hecke.ForcedStableCountDecomposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

open import Ontology.Hecke.CurrentSaturatedForcedStableCollapse
  using
    ( CurrentSaturatedGenerator
    ; saturatedForcedStableCountAt
    ; saturatedForcedStableCount≡15
    ; saturatedSummaryFieldAt
    ; saturatedSummaryField≡15
    )
open import Ontology.Hecke.DefectOrbitSummaryRefinement
  using
    ( DefectHistogram
    ; canonicalSaturatedHistogram
    ; saturatedHistogramAt
    ; saturatedHistogram≡canonical
    )

------------------------------------------------------------------------
-- Current saturated decomposition surface.
--
-- The repo now knows that the whole current saturated generator branch lands
-- at `forcedStableCount = 15` and that the full current `DefectOrbitSummary`
-- already collapses there as well.  This module does not claim that `9 + 6`
-- is the true structural explanation of that value.  It packages the
-- decomposition as the smallest theorem-bearing candidate surface so later
-- work can either derive it from a richer Hecke-side summary or reject it.

record ForcedStableCountDecomposition : Set where
  constructor forcedStableCountDecomposition
  field
    triadicCoreCount : Nat
    interfaceCount : Nat

  totalCount : Nat
  totalCount = triadicCoreCount + interfaceCount

open ForcedStableCountDecomposition public

candidateSaturatedDecomposition : ForcedStableCountDecomposition
candidateSaturatedDecomposition =
  forcedStableCountDecomposition 9 6

candidateSaturatedTriadicCoreCount : Nat
candidateSaturatedTriadicCoreCount =
  triadicCoreCount candidateSaturatedDecomposition

candidateSaturatedInterfaceCount : Nat
candidateSaturatedInterfaceCount =
  interfaceCount candidateSaturatedDecomposition

candidateSaturatedTotalCount : Nat
candidateSaturatedTotalCount =
  totalCount candidateSaturatedDecomposition

candidateSaturatedTriadicCore≡9 :
  candidateSaturatedTriadicCoreCount ≡ 9
candidateSaturatedTriadicCore≡9 = refl

candidateSaturatedInterface≡6 :
  candidateSaturatedInterfaceCount ≡ 6
candidateSaturatedInterface≡6 = refl

candidateSaturatedTotal≡15 :
  candidateSaturatedTotalCount ≡ 15
candidateSaturatedTotal≡15 = refl

record ForcedStableCountFactorization : Set where
  constructor forcedStableCountFactorization
  field
    triadicSectorCount : Nat
    symmetryClassCount : Nat

  totalProduct : Nat
  totalProduct = triadicSectorCount * symmetryClassCount

open ForcedStableCountFactorization public

candidateSaturatedFactorization : ForcedStableCountFactorization
candidateSaturatedFactorization =
  forcedStableCountFactorization 3 5

candidateSaturatedTriadicSectorCount : Nat
candidateSaturatedTriadicSectorCount =
  triadicSectorCount candidateSaturatedFactorization

candidateSaturatedSymmetryClassCount : Nat
candidateSaturatedSymmetryClassCount =
  symmetryClassCount candidateSaturatedFactorization

candidateSaturatedTotalProduct : Nat
candidateSaturatedTotalProduct =
  totalProduct candidateSaturatedFactorization

candidateSaturatedTriadicSectorCount≡3 :
  candidateSaturatedTriadicSectorCount ≡ 3
candidateSaturatedTriadicSectorCount≡3 = refl

candidateSaturatedSymmetryClassCount≡5 :
  candidateSaturatedSymmetryClassCount ≡ 5
candidateSaturatedSymmetryClassCount≡5 = refl

candidateSaturatedTotalProduct≡15 :
  candidateSaturatedTotalProduct ≡ 15
candidateSaturatedTotalProduct≡15 = refl

currentSaturatedDecompositionAt :
  CurrentSaturatedGenerator → ForcedStableCountDecomposition
currentSaturatedDecompositionAt _ = candidateSaturatedDecomposition

currentSaturatedFactorizationAt :
  CurrentSaturatedGenerator → ForcedStableCountFactorization
currentSaturatedFactorizationAt _ = candidateSaturatedFactorization

currentSaturatedTriadicCoreCountAt :
  CurrentSaturatedGenerator → Nat
currentSaturatedTriadicCoreCountAt c =
  triadicCoreCount (currentSaturatedDecompositionAt c)

currentSaturatedInterfaceCountAt :
  CurrentSaturatedGenerator → Nat
currentSaturatedInterfaceCountAt c =
  interfaceCount (currentSaturatedDecompositionAt c)

currentSaturatedDecompositionTotalAt :
  CurrentSaturatedGenerator → Nat
currentSaturatedDecompositionTotalAt c =
  totalCount (currentSaturatedDecompositionAt c)

currentSaturatedFactorizationTotalAt :
  CurrentSaturatedGenerator → Nat
currentSaturatedFactorizationTotalAt c =
  totalProduct (currentSaturatedFactorizationAt c)

currentSaturatedTriadicCoreCount≡9 :
  ∀ c →
  currentSaturatedTriadicCoreCountAt c ≡ 9
currentSaturatedTriadicCoreCount≡9 _ = refl

currentSaturatedInterfaceCount≡6 :
  ∀ c →
  currentSaturatedInterfaceCountAt c ≡ 6
currentSaturatedInterfaceCount≡6 _ = refl

currentSaturatedTriadicSectorCount≡3 :
  ∀ c →
  triadicSectorCount (currentSaturatedFactorizationAt c) ≡ 3
currentSaturatedTriadicSectorCount≡3 _ = refl

currentSaturatedSymmetryClassCount≡5 :
  ∀ c →
  symmetryClassCount (currentSaturatedFactorizationAt c) ≡ 5
currentSaturatedSymmetryClassCount≡5 _ = refl

currentSaturatedForcedStableCount-decomposes :
  ∀ c →
  saturatedForcedStableCountAt c
    ≡
  currentSaturatedTriadicCoreCountAt c
    + currentSaturatedInterfaceCountAt c
currentSaturatedForcedStableCount-decomposes c
  rewrite candidateSaturatedTotal≡15 =
    saturatedForcedStableCount≡15 c

currentSaturatedSummaryField-decomposes :
  ∀ c →
  saturatedSummaryFieldAt c
    ≡
  currentSaturatedTriadicCoreCountAt c
    + currentSaturatedInterfaceCountAt c
currentSaturatedSummaryField-decomposes c
  rewrite candidateSaturatedTotal≡15 =
    saturatedSummaryField≡15 c

currentSaturatedForcedStableCount-factorizes :
  ∀ c →
  saturatedForcedStableCountAt c
    ≡
  currentSaturatedFactorizationTotalAt c
currentSaturatedForcedStableCount-factorizes c
  rewrite candidateSaturatedTotalProduct≡15 =
    saturatedForcedStableCount≡15 c

currentSaturatedSummaryField-factorizes :
  ∀ c →
  saturatedSummaryFieldAt c
    ≡
  currentSaturatedFactorizationTotalAt c
currentSaturatedSummaryField-factorizes c
  rewrite candidateSaturatedTotalProduct≡15 =
    saturatedSummaryField≡15 c

currentSaturatedHistogram-collapses :
  ∀ c →
  saturatedHistogramAt c ≡ canonicalSaturatedHistogram
currentSaturatedHistogram-collapses = saturatedHistogram≡canonical

record CurrentSaturatedForcedStableCountDecompositionFactorization : Set₁ where
  field
    decomposition : CurrentSaturatedGenerator → ForcedStableCountDecomposition
    factorization : CurrentSaturatedGenerator → ForcedStableCountFactorization
    histogram : CurrentSaturatedGenerator → DefectHistogram
    count-factor :
      ∀ c →
      saturatedForcedStableCountAt c ≡ totalCount (decomposition c)
    summary-factor :
      ∀ c →
      saturatedSummaryFieldAt c ≡ totalCount (decomposition c)
    count-product-factor :
      ∀ c →
      saturatedForcedStableCountAt c ≡ totalProduct (factorization c)
    summary-product-factor :
      ∀ c →
      saturatedSummaryFieldAt c ≡ totalProduct (factorization c)
    histogram-factor :
      ∀ c →
      histogram c ≡ canonicalSaturatedHistogram

canonicalCurrentSaturatedForcedStableCountDecompositionFactorization :
  CurrentSaturatedForcedStableCountDecompositionFactorization
canonicalCurrentSaturatedForcedStableCountDecompositionFactorization =
  record
    { decomposition = currentSaturatedDecompositionAt
    ; factorization = currentSaturatedFactorizationAt
    ; histogram = saturatedHistogramAt
    ; count-factor = currentSaturatedForcedStableCount-decomposes
    ; summary-factor = currentSaturatedSummaryField-decomposes
    ; count-product-factor = currentSaturatedForcedStableCount-factorizes
    ; summary-product-factor = currentSaturatedSummaryField-factorizes
    ; histogram-factor = currentSaturatedHistogram-collapses
    }
