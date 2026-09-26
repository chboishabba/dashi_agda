module DASHI.Mathematics.Complexity.PNotEqualsNPAbstractCostModelQuotationNoGoExact where

------------------------------------------------------------------------
-- ABSTRACT COST-MODEL -> PROGRAM QUOTATION NO-GO
--
-- The current PolynomialCostModel is deliberately axiomatic: its
-- polynomialTimeDecider field is an arbitrary predicate on extensional Boolean
-- functions.  Therefore the interface admits a maximally permissive instance
-- which labels EVERY BooleanFormula -> Bool function "polynomial".
--
-- Combining that legal instance with the constructive Cantor quotation no-go
-- proves:
--
--   no theorem using only the current PolynomialCostModel /
--   PolynomialSATDeciderCandidate interface can uniformly recover a Nat code
--   and decoder for every candidate.
--
-- This does NOT say the intended standard machine model is unquoteable.
-- It says self-reference needs a stronger concrete machine/program realization
-- premise than the current abstract cost-model interface exposes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalQuotationNoGoExact as QuoteNoGo

------------------------------------------------------------------------
-- A legal maximally permissive PolynomialCostModel.
------------------------------------------------------------------------

permissiveFormulaCostModel :
  PR.PolynomialCostModel Cook.BooleanFormula
permissiveFormulaCostModel = record
  { PR.polynomialTimeMap =
      λ map → ⊤
  ; PR.polynomialTimeDecider =
      λ decider → ⊤
  ; PR.polynomialTimeVerifier =
      λ verifier → ⊤
  ; PR.polynomialCertificateBound =
      λ admissible → ⊤
  ; PR.identityMapPolynomial =
      tt
  ; PR.deciderClosedUnderPrecomposition =
      λ map decider mapPolynomial deciderPolynomial → tt
  }

everyFormulaConsumerIsCandidateInPermissiveModel :
  (consumer : Cook.BooleanFormula → Bool) →
  Direct.PolynomialSATDeciderCandidate
    permissiveFormulaCostModel
everyFormulaConsumerIsCandidateInPermissiveModel consumer =
  Direct.polynomial-sat-decider-candidate
    consumer
    tt

------------------------------------------------------------------------
-- Generic finite quotation from the current candidate interface is impossible.
------------------------------------------------------------------------

noGenericNatQuotationFromAbstractPolynomialCandidate :
  (quote :
    Direct.PolynomialSATDeciderCandidate
      permissiveFormulaCostModel →
    Nat) →
  (decode : Nat → Cook.BooleanFormula → Bool) →
  ((candidate :
      Direct.PolynomialSATDeciderCandidate
        permissiveFormulaCostModel) →
    QuoteNoGo.PointwiseEqual
      (decode (quote candidate))
      (Direct.decide candidate)) →
  ⊥
noGenericNatQuotationFromAbstractPolynomialCandidate
    quote decode quotationCorrect =
  QuoteNoGo.noNatQuotationOfAllFormulaConsumers
    decode
    allegedSurjectivity
  where
    allegedSurjectivity :
      (consumer : Cook.BooleanFormula → Bool) →
      Σ Nat (λ code →
        QuoteNoGo.PointwiseEqual
          (decode code)
          consumer)
    allegedSurjectivity consumer =
      quote candidate
      ,
      quotationCorrect candidate
      where
        candidate =
          everyFormulaConsumerIsCandidateInPermissiveModel
            consumer

------------------------------------------------------------------------
-- Stronger formulation: even supplying the quotation function and decoder
-- together cannot make the candidate interface self-describing.
------------------------------------------------------------------------

record CandidateNatQuotation : Set₁ where
  field
    quote :
      Direct.PolynomialSATDeciderCandidate
        permissiveFormulaCostModel →
      Nat

    decode :
      Nat → Cook.BooleanFormula → Bool

    correct :
      (candidate :
        Direct.PolynomialSATDeciderCandidate
          permissiveFormulaCostModel) →
      QuoteNoGo.PointwiseEqual
        (decode (quote candidate))
        (Direct.decide candidate)

open CandidateNatQuotation public

abstractPolynomialCandidateCannotCarryUniversalNatQuotation :
  CandidateNatQuotation →
  ⊥
abstractPolynomialCandidateCannotCarryUniversalNatQuotation quotation =
  noGenericNatQuotationFromAbstractPolynomialCandidate
    (quote quotation)
    (decode quotation)
    (correct quotation)

------------------------------------------------------------------------
-- Consequence for the self-diagonal programme.
--
-- A finite code for D must come from extra structure:
--
--   concrete machine syntax
--   + a finite serializer
--   + an interpreter/execution theorem
--   + equality with the candidate decision function.
--
-- It cannot be derived parametrically from PolynomialCostModel alone.
------------------------------------------------------------------------
