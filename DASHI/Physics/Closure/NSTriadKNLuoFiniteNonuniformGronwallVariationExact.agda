module DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallVariationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Thomas Hakon Gronwall.
-- Result: finite nonuniform variation-of-constants Gronwall formula.
-- DOI: not assigned; this is a repository-specialised finite identity.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Expand the recursive nonuniform envelope exactly.  For step factors
-- b_i=1+a_i and forcings f_i,
--
--   envelope(E,steps)
--     = E product_i b_i
--       + sum_i f_i product_{j>i} b_j.
--
-- This is the finite variation-of-constants formula underlying the continuum
-- integral Gronwall expression.  It is proved by induction and ring
-- normalization, not supplied as a final bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallExact as Gronwall
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallProductExact as Product

forcingConvolution : List Gronwall.GronwallStep → ℚ
forcingConvolution [] = 0ℚ
forcingConvolution (stepValue ∷ steps) =
  Product.growthProduct steps * Gronwall.forcing stepValue
  + forcingConvolution steps

explicitEnvelope : ℚ → List Gronwall.GronwallStep → ℚ
explicitEnvelope initial steps =
  Product.growthProduct steps * initial + forcingConvolution steps

envelopeVariationIdentity :
  (initial : ℚ) →
  (steps : List Gronwall.GronwallStep) →
  Gronwall.envelope initial steps ≡ explicitEnvelope initial steps
envelopeVariationIdentity initial [] =
  solve (initial ∷ [])
envelopeVariationIdentity initial (stepValue ∷ steps)
  rewrite envelopeVariationIdentity
    ((1ℚ + Gronwall.growth stepValue) * initial
      + Gronwall.forcing stepValue)
    steps =
  solve
    ( initial
    ∷ Gronwall.growth stepValue
    ∷ Gronwall.forcing stepValue
    ∷ Product.growthProduct steps
    ∷ forcingConvolution steps
    ∷ []
    )

finiteNonuniformVariationGronwall :
  ∀ {initial terminal steps bound} →
  Gronwall.GronwallPath initial steps terminal →
  initial ≤ bound →
  terminal ≤ explicitEnvelope bound steps
finiteNonuniformVariationGronwall
  {steps = steps} {bound = bound}
  path initialBound =
  subst
    (λ upper → terminalOf path ≤ upper)
    (envelopeVariationIdentity bound steps)
    (Gronwall.finiteNonuniformGronwall path initialBound)
  where
  terminalOf :
    ∀ {initial steps terminal} →
    Gronwall.GronwallPath initial steps terminal → ℚ
  terminalOf {terminal = terminal} path = terminal

finiteVariationIdentityClosed : Bool
finiteVariationIdentityClosed = true

finiteVariationGronwallClosed : Bool
finiteVariationGronwallClosed = true

finiteVariationIdentityClosedIsTrue :
  finiteVariationIdentityClosed ≡ true
finiteVariationIdentityClosedIsTrue = refl

finiteVariationGronwallClosedIsTrue :
  finiteVariationGronwallClosed ≡ true
finiteVariationGronwallClosedIsTrue = refl
