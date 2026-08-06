module DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallProductExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Thomas Hakon Gronwall.
-- Result: product form of the finite nonuniform discrete Gronwall estimate.
-- DOI: not assigned; this is a repository-specialised finite induction.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Identify the recursive nonuniform Gronwall envelope with the explicit
-- product when every forcing term vanishes:
--
--   envelope(E,[a_0,...,a_{n-1}])
--     = E product_i (1+a_i).
--
-- Combining this equality with the proof-relevant path theorem gives the
-- terminal product estimate directly from the one-step recurrence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallExact as Gronwall

data ZeroForcing : List Gronwall.GronwallStep → Set where
  empty : ZeroForcing []
  prepend :
    ∀ {stepValue steps} →
    Gronwall.forcing stepValue ≡ 0ℚ →
    ZeroForcing steps →
    ZeroForcing (stepValue ∷ steps)

growthProduct : List Gronwall.GronwallStep → ℚ
growthProduct [] = 1ℚ
growthProduct (stepValue ∷ steps) =
  (1ℚ + Gronwall.growth stepValue) * growthProduct steps

zeroForcingEnvelopeProduct :
  (initial : ℚ) →
  (steps : List Gronwall.GronwallStep) →
  ZeroForcing steps →
  Gronwall.envelope initial steps ≡ growthProduct steps * initial
zeroForcingEnvelopeProduct initial [] empty =
  solve (initial ∷ [])
zeroForcingEnvelopeProduct initial (stepValue ∷ steps)
  (prepend forcingZero restZero)
  rewrite forcingZero
        | zeroForcingEnvelopeProduct
            ((1ℚ + Gronwall.growth stepValue) * initial + 0ℚ)
            steps
            restZero =
  solve
    ( initial
    ∷ Gronwall.growth stepValue
    ∷ growthProduct steps
    ∷ []
    )

finiteNonuniformGronwallProduct :
  ∀ {initial terminal steps bound} →
  Gronwall.GronwallPath initial steps terminal →
  initial ≤ bound →
  ZeroForcing steps →
  terminal ≤ growthProduct steps * bound
finiteNonuniformGronwallProduct
  {steps = steps} {bound = bound}
  path initialBound zeroForcing =
  subst
    (λ upper → terminalOf path ≤ upper)
    (zeroForcingEnvelopeProduct bound steps zeroForcing)
    (Gronwall.finiteNonuniformGronwall path initialBound)
  where
  terminalOf :
    ∀ {initial steps terminal} →
    Gronwall.GronwallPath initial steps terminal → ℚ
  terminalOf {terminal = terminal} path = terminal

finiteNonuniformProductIdentityClosed : Bool
finiteNonuniformProductIdentityClosed = true

finiteNonuniformProductGronwallClosed : Bool
finiteNonuniformProductGronwallClosed = true

finiteNonuniformProductIdentityClosedIsTrue :
  finiteNonuniformProductIdentityClosed ≡ true
finiteNonuniformProductIdentityClosedIsTrue = refl

finiteNonuniformProductGronwallClosedIsTrue :
  finiteNonuniformProductGronwallClosed ≡ true
finiteNonuniformProductGronwallClosedIsTrue = refl
