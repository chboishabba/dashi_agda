module DASHI.Physics.Closure.NSTriadKNLuoFiniteDiscreteGronwallExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Mathematical ingredient: the finite discrete Gronwall inequality.  This is
-- a classical induction theorem; no DOI is assigned to the repository proof.
--
-- PURPOSE
-- Replace the finite Gronwall step by a checked rational induction theorem.
-- For a nonnegative growth factor lambda, an initial upper bound and the
-- one-step inequality
--
--   E_{n+1} <= lambda E_n + F_n
--
-- imply domination by the recursively unrolled Duhamel/Gronwall envelope at
-- every finite time.  The homogeneous envelope is also identified exactly
-- with lambda^n E_0.
--
-- This does not claim the real exponential theorem or the continuum
-- absolutely-continuous Gronwall lemma; those are the remaining limit layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

gronwallEnvelope :
  ℚ →
  (Nat → ℚ) →
  ℚ →
  Nat →
  ℚ
gronwallEnvelope growth forcing initial zero = initial
gronwallEnvelope growth forcing initial (suc step) =
  growth * gronwallEnvelope growth forcing initial step
  + forcing step

record FiniteDiscreteGronwallData : Set₁ where
  field
    energy forcing : Nat → ℚ
    growth initialBound : ℚ

    growthNonnegative : 0ℚ ≤ growth
    initialEnergyBound : energy zero ≤ initialBound

    oneStepBound :
      (step : Nat) →
      energy (suc step)
      ≤ growth * energy step + forcing step

open FiniteDiscreteGronwallData public

finiteDiscreteGronwall :
  (data : FiniteDiscreteGronwallData) →
  (step : Nat) →
  energy data step
  ≤ gronwallEnvelope
      (growth data)
      (forcing data)
      (initialBound data)
      step
finiteDiscreteGronwall data zero = initialEnergyBound data
finiteDiscreteGronwall data (suc step) =
  let
    instance growthNN = nonNegative (growthNonnegative data)

    scaledInduction :
      growth data * energy data step
      ≤ growth data
        * gronwallEnvelope
            (growth data)
            (forcing data)
            (initialBound data)
            step
    scaledInduction =
      ℚₚ.*-monoˡ-≤-nonNeg
        (growth data)
        (finiteDiscreteGronwall data step)

    affineInduction :
      growth data * energy data step + forcing data step
      ≤ growth data
          * gronwallEnvelope
              (growth data)
              (forcing data)
              (initialBound data)
              step
        + forcing data step
    affineInduction =
      ℚₚ.+-mono-≤ scaledInduction ℚₚ.≤-refl
  in
  ℚₚ.≤-trans
    (oneStepBound data step)
    affineInduction

zeroForcing : Nat → ℚ
zeroForcing step = 0ℚ

homogeneousEnvelopeMeaning :
  (growth initial : ℚ) →
  (step : Nat) →
  gronwallEnvelope growth zeroForcing initial step
  ≡ Geo.pow growth step * initial
homogeneousEnvelopeMeaning growth initial zero =
  solve (initial ∷ [])
homogeneousEnvelopeMeaning growth initial (suc step)
  rewrite homogeneousEnvelopeMeaning growth initial step =
  solve (growth ∷ Geo.pow growth step ∷ initial ∷ [])

record FiniteHomogeneousGronwallData : Set₁ where
  field
    energy : Nat → ℚ
    growth initialBound : ℚ

    growthNonnegative : 0ℚ ≤ growth
    initialEnergyBound : energy zero ≤ initialBound

    homogeneousStepBound :
      (step : Nat) →
      energy (suc step) ≤ growth * energy step

open FiniteHomogeneousGronwallData public

homogeneousAsInhomogeneous :
  FiniteHomogeneousGronwallData →
  FiniteDiscreteGronwallData
homogeneousAsInhomogeneous data = record
  { energy = energy data
  ; forcing = zeroForcing
  ; growth = growth data
  ; initialBound = initialBound data
  ; growthNonnegative = growthNonnegative data
  ; initialEnergyBound = initialEnergyBound data
  ; oneStepBound = λ step →
      ℚₚ.≤-trans
        (homogeneousStepBound data step)
        (subst
          (λ upper →
            growth data * energy data step ≤ upper)
          (sym (ℚₚ.+-identityʳ (growth data * energy data step)))
          ℚₚ.≤-refl)
  }

finiteHomogeneousGronwall :
  (data : FiniteHomogeneousGronwallData) →
  (step : Nat) →
  energy data step
  ≤ Geo.pow (growth data) step * initialBound data
finiteHomogeneousGronwall data step =
  subst
    (λ upper → energy data step ≤ upper)
    (homogeneousEnvelopeMeaning
      (growth data)
      (initialBound data)
      step)
    (finiteDiscreteGronwall (homogeneousAsInhomogeneous data) step)

finiteDiscreteGronwallClosed : Bool
finiteDiscreteGronwallClosed = true

finiteHomogeneousGronwallClosed : Bool
finiteHomogeneousGronwallClosed = true

finiteDiscreteGronwallClosedIsTrue :
  finiteDiscreteGronwallClosed ≡ true
finiteDiscreteGronwallClosedIsTrue = refl

finiteHomogeneousGronwallClosedIsTrue :
  finiteHomogeneousGronwallClosed ≡ true
finiteHomogeneousGronwallClosedIsTrue = refl
