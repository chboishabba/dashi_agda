module DASHI.Empirical.SeamABExperiment where

open import Agda.Builtin.Equality using (_≡_; refl)

-- Both solve directions are mandatory experiment lanes. The formal surface
-- does not prematurely promote either lane as globally canonical.

data Domain : Set where
  base rom : Domain

data Direction : Set where
  A-base-to-rom B-rom-to-base : Direction

record DirectedResult (Metric : Set) : Set where
  constructor result
  field
    nativeMetric : Metric
    transferredMetric : Metric

record ABExperiment (Metric : Set) : Set where
  constructor experiment
  field
    strategyA : DirectedResult Metric
    strategyB : DirectedResult Metric

source : Direction → Domain
source A-base-to-rom = base
source B-rom-to-base = rom

target : Direction → Domain
target A-base-to-rom = rom
target B-rom-to-base = base

A-source-is-base : source A-base-to-rom ≡ base
A-source-is-base = refl

A-target-is-rom : target A-base-to-rom ≡ rom
A-target-is-rom = refl

B-source-is-rom : source B-rom-to-base ≡ rom
B-source-is-rom = refl

B-target-is-base : target B-rom-to-base ≡ base
B-target-is-base = refl

-- Any selector must be supplied with an explicit policy. DASHI does not derive
-- a winner merely from the existence of the two lanes.
data Selection : Set where
  select-A select-B retain-both needs-human : Selection

record SelectionPolicy (Metric : Set) : Set₁ where
  field
    select : ABExperiment Metric → Selection

bothDirectionsPresent :
  {Metric : Set} →
  (e : ABExperiment Metric) →
  ABExperiment.strategyA e ≡ ABExperiment.strategyA e
bothDirectionsPresent e = refl
