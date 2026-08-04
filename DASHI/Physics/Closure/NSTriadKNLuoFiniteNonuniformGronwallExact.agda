module DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Thomas Hakon Gronwall.
-- Result: finite nonuniform discrete Gronwall propagation.
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
-- Prove the nonuniform finite recurrence needed for weighted time partitions.
-- Each step may have its own growth and forcing:
--
--   E_{i+1} <= (1+a_i) E_i + f_i,   0 <= a_i.
--
-- A proof-relevant path stores every one-step inequality.  Induction proves
-- that the terminal energy is below the recursively constructed envelope.
-- The theorem does not assume a constant time step or a prepackaged final
-- Gronwall estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = toWitness {a? = 0ℚ ≤? 1ℚ} _

record GronwallStep : Set where
  constructor gronwall-step
  field
    growth forcing : ℚ
    growthNonnegative : 0ℚ ≤ growth

open GronwallStep public

onePlusGrowthNonnegative :
  (step : GronwallStep) →
  0ℚ ≤ 1ℚ + growth step
onePlusGrowthNonnegative step =
  L2.addNonnegative oneNonnegative (growthNonnegative step)

envelope : ℚ → List GronwallStep → ℚ
envelope initial [] = initial
envelope initial (step ∷ steps) =
  envelope
    ((1ℚ + growth step) * initial + forcing step)
    steps

data GronwallPath : ℚ → List GronwallStep → ℚ → Set where
  finished :
    (energy : ℚ) →
    GronwallPath energy [] energy

  advance :
    ∀ {current next terminal steps} →
    (step : GronwallStep) →
    next ≤ (1ℚ + growth step) * current + forcing step →
    GronwallPath next steps terminal →
    GronwallPath current (step ∷ steps) terminal

oneStepEnvelopeMonotone :
  (step : GronwallStep) →
  ∀ {current bound} →
  current ≤ bound →
  (1ℚ + growth step) * current + forcing step
  ≤ (1ℚ + growth step) * bound + forcing step
oneStepEnvelopeMonotone step current≤bound =
  ℚₚ.+-mono-≤
    (let instance factorIsNonnegative =
       nonNegative (onePlusGrowthNonnegative step)
     in
     ℚₚ.*-monoˡ-≤-nonNeg
       (1ℚ + growth step)
       current≤bound)
    ℚₚ.≤-refl

finiteNonuniformGronwall :
  ∀ {initial terminal steps bound} →
  GronwallPath initial steps terminal →
  initial ≤ bound →
  terminal ≤ envelope bound steps
finiteNonuniformGronwall (finished energy) initial≤bound = initial≤bound
finiteNonuniformGronwall
  (advance step nextBound restPath) initial≤bound =
  finiteNonuniformGronwall
    restPath
    (ℚₚ.≤-trans
      nextBound
      (oneStepEnvelopeMonotone step initial≤bound))

record NonnegativeGronwallStep : Set where
  constructor nonnegative-gronwall-step
  field
    step : GronwallStep
    forcingNonnegative : 0ℚ ≤ forcing step

open NonnegativeGronwallStep public

nonnegativeEnvelope :
  (initial : ℚ) →
  0ℚ ≤ initial →
  (steps : List NonnegativeGronwallStep) →
  0ℚ ≤ envelope initial (mapSteps steps)
  where
  mapSteps : List NonnegativeGronwallStep → List GronwallStep
  mapSteps [] = []
  mapSteps (wrapped ∷ rest) = step wrapped ∷ mapSteps rest
nonnegativeEnvelope initial initialNonnegative [] = initialNonnegative
nonnegativeEnvelope initial initialNonnegative (wrapped ∷ rest) =
  nonnegativeEnvelope
    ((1ℚ + growth (step wrapped)) * initial + forcing (step wrapped))
    (L2.addNonnegative
      (let
        factorNonnegative = onePlusGrowthNonnegative (step wrapped)
       in
       let
        instance
          factorIsNonnegative = nonNegative factorNonnegative
          initialIsNonnegative = nonNegative initialNonnegative
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (1ℚ + growth (step wrapped)) initial
       in
       ℚₚ.nonNegative⁻¹
         ((1ℚ + growth (step wrapped)) * initial))
      (forcingNonnegative wrapped))
    rest

finiteNonuniformGronwallClosed : Bool
finiteNonuniformGronwallClosed = true

nonnegativeEnvelopeClosed : Bool
nonnegativeEnvelopeClosed = true

finiteNonuniformGronwallClosedIsTrue :
  finiteNonuniformGronwallClosed ≡ true
finiteNonuniformGronwallClosedIsTrue = refl

nonnegativeEnvelopeClosedIsTrue :
  nonnegativeEnvelopeClosed ≡ true
nonnegativeEnvelopeClosedIsTrue = refl
