module DASHI.Moonshine.FormalLaurentFaberVpDiscrepancyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Remark 1.4 uses the p-th Faber polynomial Phi_p and the dilation operator
-- V_p on the classical j-function through
--
--   m_p = v_p(j | V_p - Phi_p(j)).
--
-- Conway--Norton / replicability context is already represented by
-- DASHI.Moonshine.ConwayNortonTheorem.ReplicabilityPackage, whose
-- `FaberPolynomial` field deliberately remains abstract.
--
-- DASHI CONTRIBUTION
--
-- Add the missing coefficient-level adapter without replacing that existing
-- replicability owner.  A V_p shift is specified exactly on the signed Laurent
-- carrier:
--
--   c_{pk}(f|V_p) = c_k(f),
--   c_n(f|V_p) = 0 when n is not a p-multiple.
--
-- A Faber/V_p surface then carries one p-th Faber object, its evaluation at j,
-- and the exact Laurent discrepancy.  No p-adic valuation theorem is imported
-- here; the later Duncan--Swisher module owns that source boundary.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int

import DASHI.Moonshine.FormalLaurentQSeriesUNExact as Laurent
import DASHI.Moonshine.ConwayNortonTheorem as CN

------------------------------------------------------------------------
-- Exact signed-index V_p coefficient law.
------------------------------------------------------------------------

record NotPMultiple (p : Nat) (n : ℤ) : Set where
  field
    noMultipleWitness :
      (k : ℤ) → n ≡ Int._*_ (+ p) k → ⊥

open NotPMultiple public

record VpCoefficientLaw
    (p : Nat)
    (source shifted : Laurent.FormalLaurentQSeries) : Set where
  field
    atMultiple :
      (k : ℤ) →
      shifted (Int._*_ (+ p) k) ≡ source k

    offMultipleZero :
      (n : ℤ) →
      NotPMultiple p n →
      shifted n ≡ + 0

open VpCoefficientLaw public

------------------------------------------------------------------------
-- Faber/V_p discrepancy on the existing signed Laurent carrier.
------------------------------------------------------------------------

record FaberVpDiscrepancySurface (p : Nat) : Set₁ where
  field
    FaberPolynomial : Set
    pthFaberPolynomial : FaberPolynomial

    jSeries : Laurent.FormalLaurentQSeries
    jVpSeries : Laurent.FormalLaurentQSeries
    vpLaw : VpCoefficientLaw p jSeries jVpSeries

    evaluateAtJ : FaberPolynomial → Laurent.FormalLaurentQSeries

open FaberVpDiscrepancySurface public

faberValueAtJ :
  {p : Nat} →
  FaberVpDiscrepancySurface p →
  Laurent.FormalLaurentQSeries
faberValueAtJ A = evaluateAtJ A (pthFaberPolynomial A)

faberVpDiscrepancy :
  {p : Nat} →
  FaberVpDiscrepancySurface p →
  Laurent.FormalLaurentQSeries
faberVpDiscrepancy A n =
  Int._-_ (jVpSeries A n) (faberValueAtJ A n)

faberVpDiscrepancyCoefficient :
  {p : Nat} →
  (A : FaberVpDiscrepancySurface p) →
  (n : ℤ) →
  faberVpDiscrepancy A n
  ≡ Int._-_ (jVpSeries A n) (evaluateAtJ A (pthFaberPolynomial A) n)
faberVpDiscrepancyCoefficient A n = refl

------------------------------------------------------------------------
-- Adapter to the pre-existing Conway--Norton Faber-polynomial TYPE.
--
-- `ReplicabilityPackage` does not itself contain an evaluator into the current
-- Laurent carrier, so that evaluator remains explicit proof-relevant data.
------------------------------------------------------------------------

record ConwayNortonLaurentFaberAdapter
    {Monster : Set}
    (realization : Monster → Laurent.FormalLaurentQSeries)
    (R : CN.ReplicabilityPackage
      Monster Laurent.FormalLaurentQSeries realization)
    (p : Nat) : Setω where
  field
    jSeries : Laurent.FormalLaurentQSeries
    jVpSeries : Laurent.FormalLaurentQSeries
    vpLaw : VpCoefficientLaw p jSeries jVpSeries

    pthFaberPolynomial : CN.FaberPolynomial R
    evaluateAtJ :
      CN.FaberPolynomial R → Laurent.FormalLaurentQSeries

open ConwayNortonLaurentFaberAdapter public

adapterSurface :
  {Monster : Set} →
  {realization : Monster → Laurent.FormalLaurentQSeries} →
  {R : CN.ReplicabilityPackage
    Monster Laurent.FormalLaurentQSeries realization} →
  {p : Nat} →
  ConwayNortonLaurentFaberAdapter realization R p →
  FaberVpDiscrepancySurface p
adapterSurface {R = R} A = record
  { FaberPolynomial = CN.FaberPolynomial R
  ; pthFaberPolynomial = pthFaberPolynomial A
  ; jSeries = jSeries A
  ; jVpSeries = jVpSeries A
  ; vpLaw = vpLaw A
  ; evaluateAtJ = evaluateAtJ A
  }

record FormalLaurentFaberVpDiscrepancyBoundary : Set where
  field
    signedLaurentCarrierReused : Bool
    exactVpMultipleCoefficientLawConstructed : Bool
    exactVpOffMultipleZeroLawConstructed : Bool
    existingConwayNortonFaberTypeReused : Bool
    faberEvaluationKeptExplicit : Bool
    discrepancySeriesConstructed : Bool
    specificPadicValuationDerivedHere : Bool
    replicabilityIdentityIdentifiedWithDuncanSwisherValuation : Bool

canonicalFormalLaurentFaberVpDiscrepancyBoundary :
  FormalLaurentFaberVpDiscrepancyBoundary
canonicalFormalLaurentFaberVpDiscrepancyBoundary = record
  { signedLaurentCarrierReused = true
  ; exactVpMultipleCoefficientLawConstructed = true
  ; exactVpOffMultipleZeroLawConstructed = true
  ; existingConwayNortonFaberTypeReused = true
  ; faberEvaluationKeptExplicit = true
  ; discrepancySeriesConstructed = true
  ; specificPadicValuationDerivedHere = false
  ; replicabilityIdentityIdentifiedWithDuncanSwisherValuation = false
  }
