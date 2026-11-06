{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopFactorDerivativeChainExact where

------------------------------------------------------------------------
-- DIVISION-FREE BISHOP CHAIN RULE, ON THE ORIGINAL PINNED REAL.
--
-- If g is factor-differentiable at x, and f is factor-differentiable
-- at g(x), then f∘g is factor-differentiable at x, with derivative
-- f'(g(x))*g'(x).  No nonzero increment or quotient division:
--
-- Δg(h) = g(x+h)-g(x)
-- f(g(x+h))-f(g(x)) = Δg(h)*qf(Δg(h))
--                   = h*(qg(h)*qf(Δg(h))).
--
-- The proof of Δg(h_n)->0 uses the already-proved original Bishop
-- factor derivative sequential continuity; the quotient limit uses
-- only the original pinned Sequence product and equivalence rules.
-- This is a reusable SOURCE calculus theorem, not a new interchange
-- authority for an infinite series.
--
-- Attribution: Bishop/Bridges constructive analysis; Murray/Csimma
-- pinned vendor/bishop; DASHI original factor derivative/product.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopFactorDerivativeProductExact as Product
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power

factorChainDelta :
  (g : R.ℝ → R.ℝ) (point h : R.ℝ) → R.ℝ
factorChainDelta g point h =
  R._-_ (g (R._+_ point h)) (g point)

factorChainDeltaConvergesZero :
  ∀ {g point dg} →
  Factor.BishopFactorDerivativeAt g point dg →
  ∀ {perturbation : Nat → R.ℝ} →
  Seq._ConvergesTo_ perturbation R.0ℝ →
  Seq._ConvergesTo_
    (λ index → factorChainDelta g point (perturbation index))
    R.0ℝ
factorChainDeltaConvergesZero
    {g} {point} {dg} G {perturbation} perturbationConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ+yₙ→x₀+y₀
      (g point ,
        Product.factorDerivativeSequentialContinuity
          G perturbationConverges)
      (R.-_ (g point) ,
        Seq.xₙ≃c⇒xₙ→c
          (λ {(suc _) → RP.≃-refl})))
    (RP.+-inverseʳ (g point))

factorDerivativeChain :
  ∀ {f g point df dg} →
  Factor.BishopFactorDerivativeAt f (g point) df →
  Factor.BishopFactorDerivativeAt g point dg →
  Factor.BishopFactorDerivativeAt
    (λ x → f (g x))
    point
    (R._*_ df dg)
factorDerivativeChain {f} {g} {point} {df} {dg} F G =
  record
  { Factor.quotient = λ h →
      R._*_
        (Factor.quotient G h)
        (Factor.quotient F (factorChainDelta g point h))
  ; Factor.incrementFactorisation = λ h →
      let
        delta = factorChainDelta g point h
        qf = Factor.quotient F delta
        qg = Factor.quotient G h
        open RP.ℝ-Solver
      in
      RP.≃-trans
        (RP.≃-trans
          (RP.+-cong
            (RP.≃-refl)
            (RP.≃-refl))
          (Factor.incrementFactorisation F delta))
        (RP.≃-trans
          (RP.*-cong
            (Factor.incrementFactorisation G h)
            RP.≃-refl)
          (solve 3
            (λ h′ qg′ qf′ →
              (h′ ⊗ qg′) ⊗ qf′
              ⊜ h′ ⊗ (qg′ ⊗ qf′))
            RP.≃-refl h qg qf))
  ; Factor.quotientConvergesOnNullSequences = λ
      {perturbation} perturbationConverges →
      let
        deltaConvergesZero =
          factorChainDeltaConvergesZero
            G perturbationConverges
        productConverges :
          Seq._ConvergesTo_
            (λ index →
              R._*_
                (Factor.quotient G (perturbation index))
                (Factor.quotient F
                  (factorChainDelta g point (perturbation index))))
            (R._*_ dg df)
        productConverges =
          Seq.xₙyₙ→x₀y₀
            (dg ,
              Factor.quotientConvergesOnNullSequences
                G perturbationConverges)
            (df ,
              Factor.quotientConvergesOnNullSequences
                F deltaConvergesZero)
      in
      Seq.xₙ→x∧x≃y⇒xₙ→y
        productConverges
        (RP.*-comm dg df)
  }
