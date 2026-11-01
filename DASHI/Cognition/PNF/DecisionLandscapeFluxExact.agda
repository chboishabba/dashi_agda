module DASHI.Cognition.PNF.DecisionLandscapeFluxExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- LANDSCAPE != NONEQUILIBRIUM FLOW
--
-- Literature calibration:
-- John J. Hopfield,
-- "Neural networks and physical systems with emergent collective
-- computational abilities", DOI 10.1073/pnas.79.8.2554.
--
-- Takamitsu Watanabe; Satoshi Hirose; Hiroyuki Wada; Yoshio Imai; Toru
-- Machida; Ichiro Shirouzu; Seiki Konishi; Yasushi Miyashita; Naoki Masuda,
-- "Energy landscapes of resting-state brain networks",
-- DOI 10.3389/fninf.2014.00012.
--
-- Han Yan; Lei Zhao; Liang Hu; Xidi Wang; Erkang Wang; Jin Wang,
-- "Nonequilibrium landscape theory of neural networks",
-- DOI 10.1073/pnas.1310692110.
--
-- The exact finite object below separates a scalar basin landscape from a
-- circulation/flux coordinate.  It is not a quantitative fit of any cited
-- neural dataset and does not identify cognition with gradient flow.
------------------------------------------------------------------------

data LandscapeState : Set where leftMinimum saddle rightMinimum : LandscapeState

data FluxRegime : Set where noFlux clockwiseFlux counterclockwiseFlux : FluxRegime

potential : LandscapeState → Nat
potential leftMinimum = 0
potential saddle = 3
potential rightMinimum = 0

next : FluxRegime → LandscapeState → LandscapeState
next noFlux x = x
next clockwiseFlux leftMinimum = saddle
next clockwiseFlux saddle = rightMinimum
next clockwiseFlux rightMinimum = leftMinimum
next counterclockwiseFlux leftMinimum = rightMinimum
next counterclockwiseFlux rightMinimum = saddle
next counterclockwiseFlux saddle = leftMinimum

sameEnergyDistinctMinima :
  potential leftMinimum ≡ potential rightMinimum
  × (leftMinimum ≡ rightMinimum → ⊥)
sameEnergyDistinctMinima = refl , (λ ())

sameLandscapePointDifferentFluxCanChangeSuccessor :
  next clockwiseFlux leftMinimum
  ≡ next counterclockwiseFlux leftMinimum → ⊥
sameLandscapePointDifferentFluxCanChangeSuccessor ()

clockwiseCirculationReturnsAfterThreeSteps :
  next clockwiseFlux
    (next clockwiseFlux (next clockwiseFlux leftMinimum))
  ≡ leftMinimum
clockwiseCirculationReturnsAfterThreeSteps = refl

counterclockwiseCirculationReturnsAfterThreeSteps :
  next counterclockwiseFlux
    (next counterclockwiseFlux (next counterclockwiseFlux leftMinimum))
  ≡ leftMinimum
counterclockwiseCirculationReturnsAfterThreeSteps = refl

flowOutcome : LandscapeState → LandscapeState
flowOutcome = next clockwiseFlux

potentialCannotDetermineFlowOutcome :
  NF.FactorsThrough potential flowOutcome → ⊥
potentialCannotDetermineFlowOutcome =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      leftMinimum rightMinimum refl (λ ()))

record LandscapeFluxState : Set where
  constructor landscapeFluxState
  field
    landscapeState : LandscapeState
    fluxRegime : FluxRegime

open LandscapeFluxState public

samePotentialDifferentFluxState :
  potential (landscapeState (landscapeFluxState leftMinimum clockwiseFlux))
  ≡ potential (landscapeState (landscapeFluxState leftMinimum counterclockwiseFlux))
  × (fluxRegime (landscapeFluxState leftMinimum clockwiseFlux)
      ≡ fluxRegime (landscapeFluxState leftMinimum counterclockwiseFlux) → ⊥)
samePotentialDifferentFluxState = refl , (λ ())

record DecisionLandscapeFluxBoundary : Set where
  constructor decisionLandscapeFluxBoundary
  field
    scalarPotentialDeterminesFlow : Bool
    equalPotentialImpliesSameFineState : Bool
    circulationCanExistWithReturnedPotential : Bool
    landscapeAndFluxSeparatelyTyped : Bool

canonicalDecisionLandscapeFluxBoundary : DecisionLandscapeFluxBoundary
canonicalDecisionLandscapeFluxBoundary =
  decisionLandscapeFluxBoundary false false true true
