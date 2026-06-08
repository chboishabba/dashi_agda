module DASHI.Physics.Closure.NSAbelTriadicStationarityProxyHarnessResult where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS Abel-triadic stationarity proxy harness result receipt.
--
-- Source harness:
--
--   scripts/ns_abel_triadic_stationarity_proxy_harness.py
--
-- Scope:
--
--   finite Abel-weighted triadic proxy diagnostics only.
--
-- This module records that the harness observed bounded mass, a
-- stationarity-delta proxy, and a bias-bound proxy while keeping promotion
-- false.  It deliberately records that the PDE Abel triadic defect-measure
-- construction is not supplied by this harness.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_abel_triadic_stationarity_proxy_harness.py"

receiptScope : String
receiptScope =
  "finite_abel_weighted_triadic_stationarity_proxy_diagnostic_only"

noPdeMeasureConstructionText : String
noPdeMeasureConstructionText =
  "No PDE Abel triadic defect-measure construction is claimed by this harness receipt."

------------------------------------------------------------------------
-- Requested diagnostic observations.

bounded_mass_proxy_observed : Bool
bounded_mass_proxy_observed =
  true

stationarity_delta_proxy_observed : Bool
stationarity_delta_proxy_observed =
  true

bias_bound_proxy_observed : Bool
bias_bound_proxy_observed =
  true

promotion : Bool
promotion =
  false

abel_defect_measure_constructed : Bool
abel_defect_measure_constructed =
  false

pde_promotion : Bool
pde_promotion =
  false

clay_promotion : Bool
clay_promotion =
  false

bounded_mass_proxy_observed_is_true :
  bounded_mass_proxy_observed ≡ true
bounded_mass_proxy_observed_is_true =
  refl

stationarity_delta_proxy_observed_is_true :
  stationarity_delta_proxy_observed ≡ true
stationarity_delta_proxy_observed_is_true =
  refl

bias_bound_proxy_observed_is_true :
  bias_bound_proxy_observed ≡ true
bias_bound_proxy_observed_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

abel_defect_measure_constructed_is_false :
  abel_defect_measure_constructed ≡ false
abel_defect_measure_constructed_is_false =
  refl

pde_promotion_is_false :
  pde_promotion ≡ false
pde_promotion_is_false =
  refl

clay_promotion_is_false :
  clay_promotion ≡ false
clay_promotion_is_false =
  refl

------------------------------------------------------------------------
-- Closed receipt payload.

data HarnessProxyObservation : Set where
  boundedMassProxyObserved :
    HarnessProxyObservation
  stationarityDeltaProxyObserved :
    HarnessProxyObservation
  biasBoundProxyObserved :
    HarnessProxyObservation

canonicalHarnessProxyObservations :
  List HarnessProxyObservation
canonicalHarnessProxyObservations =
  boundedMassProxyObserved
  ∷ stationarityDeltaProxyObserved
  ∷ biasBoundProxyObserved
  ∷ []

harnessProxyObservationCount : Nat
harnessProxyObservationCount =
  listLength canonicalHarnessProxyObservations

harnessProxyObservationCountIs3 :
  harnessProxyObservationCount ≡ 3
harnessProxyObservationCountIs3 =
  refl

data HarnessNonClaimBoundary : Set where
  diagnosticOnlyNotPdeMeasure :
    HarnessNonClaimBoundary
  finiteProxyNotNavierStokesTheorem :
    HarnessNonClaimBoundary
  noResidualDepletionClosure :
    HarnessNonClaimBoundary
  noClayOrTerminalPromotion :
    HarnessNonClaimBoundary

canonicalHarnessNonClaimBoundaries :
  List HarnessNonClaimBoundary
canonicalHarnessNonClaimBoundaries =
  diagnosticOnlyNotPdeMeasure
  ∷ finiteProxyNotNavierStokesTheorem
  ∷ noResidualDepletionClosure
  ∷ noClayOrTerminalPromotion
  ∷ []

harnessNonClaimBoundaryCount : Nat
harnessNonClaimBoundaryCount =
  listLength canonicalHarnessNonClaimBoundaries

harnessNonClaimBoundaryCountIs4 :
  harnessNonClaimBoundaryCount ≡ 4
harnessNonClaimBoundaryCountIs4 =
  refl

record NSAbelTriadicStationarityProxyHarnessResult : Set where
  field
    sourceHarness :
      String
    scope :
      String
    observedProxies :
      List HarnessProxyObservation
    observedProxyCountIs3 :
      listLength observedProxies ≡ 3
    nonClaimBoundaries :
      List HarnessNonClaimBoundary
    nonClaimBoundaryCountIs4 :
      listLength nonClaimBoundaries ≡ 4
    boundedMassProxyObservedProof :
      bounded_mass_proxy_observed ≡ true
    stationarityDeltaProxyObservedProof :
      stationarity_delta_proxy_observed ≡ true
    biasBoundProxyObservedProof :
      bias_bound_proxy_observed ≡ true
    promotionFalse :
      promotion ≡ false
    abelDefectMeasureConstructedFalse :
      abel_defect_measure_constructed ≡ false
    pdePromotionFalse :
      pde_promotion ≡ false
    clayPromotionFalse :
      clay_promotion ≡ false
    noPdeMeasureConstruction :
      String

canonicalNSAbelTriadicStationarityProxyHarnessResult :
  NSAbelTriadicStationarityProxyHarnessResult
canonicalNSAbelTriadicStationarityProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; scope =
        receiptScope
    ; observedProxies =
        canonicalHarnessProxyObservations
    ; observedProxyCountIs3 =
        harnessProxyObservationCountIs3
    ; nonClaimBoundaries =
        canonicalHarnessNonClaimBoundaries
    ; nonClaimBoundaryCountIs4 =
        harnessNonClaimBoundaryCountIs4
    ; boundedMassProxyObservedProof =
        bounded_mass_proxy_observed_is_true
    ; stationarityDeltaProxyObservedProof =
        stationarity_delta_proxy_observed_is_true
    ; biasBoundProxyObservedProof =
        bias_bound_proxy_observed_is_true
    ; promotionFalse =
        promotion_is_false
    ; abelDefectMeasureConstructedFalse =
        abel_defect_measure_constructed_is_false
    ; pdePromotionFalse =
        pde_promotion_is_false
    ; clayPromotionFalse =
        clay_promotion_is_false
    ; noPdeMeasureConstruction =
        noPdeMeasureConstructionText
    }
