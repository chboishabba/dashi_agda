module DASHI.Physics.Optics.FourierPixelGradientPoissonSquareExact where

-- Glauser, Vonk, Seda et al., Nature 655, 87-92 (2026),
-- DOI 10.1038/s41586-026-10681-7, Methods Eqs (30)-(31).
--
-- Original article: reconstruct phase gradients by solving a discrete
-- Poisson equation with zero Fourier mode fixed (global phase gauge).
-- DASHI mathematical reconstruction: reuse two canonical commuting-square
-- and consumer-descent theorem owners. The discrete 4x4 torus Gaussian-
-- rational check lives in scripts/check_fourier_pixel_phase_poisson_exact.py.
--
-- CONSTRAINT: This abstract record does not prove its own Fourier spectral
-- inverse or claim that a measured phase step is an exact unwrapped gradient.
-- Those properties must be supplied for the SAME discrete grid operator.

open import Agda.Primitive using (Set; Set₁)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

import DASHI.Physics.Limits.PhysicsLimitCommutingSquare as Sq
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

record PhasePoissonModel (Phase Edges Source : Set) : Set₁ where
  field
    gradient : Phase → Edges
    divergence : Edges → Source
    solvePoisson : Source → Phase
    gaugeFix : Phase → Phase

    -- This exact inverse is restricted to exact gradient data.
    solveGradient : (phase : Phase) →
      solvePoisson (divergence (gradient phase)) ≡ gaugeFix phase

    -- Gauge fixing changes only the unobserved constant mode.
    gradientGaugeInvariant : (phase : Phase) →
      gradient (gaugeFix phase) ≡ gradient phase

open PhasePoissonModel public

phasePoissonSquare :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  Sq.CommutingSquare Phase Edges Phase Phase
phasePoissonSquare model = record
  { top = gradient model
  ; left = gaugeFix model
  ; right = λ measured → solvePoisson model (divergence model measured)
  ; bottom = λ phase → phase
  }

phasePoissonSquareExact :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  Sq.ExactCommutation (phasePoissonSquare model)
phasePoissonSquareExact model =
  record { pathsAgree = solveGradient model }

-- The unobserved constant phase is explicitly a fibre of the gradient.
record GaugeCollision
    {Phase Edges Source : Set}
    (model : PhasePoissonModel Phase Edges Source) : Set where
  field
    first second : Phase
    sameGradient : gradient model first ≡ gradient model second
    distinctAbsolutePhase : first ≡ second → ⊥

open GaugeCollision public

gaugeCollisionDefect :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  GaugeCollision model →
  Core.ConsumerDescentDefect (gradient model) (λ phase → phase)
gaugeCollisionDefect model collision =
  Core.consumerDescentDefect
    (first collision) (second collision)
    (sameGradient collision) (distinctAbsolutePhase collision)

noUniversalAbsolutePhaseRecovery :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  GaugeCollision model →
  Core.ConsumerDescent (gradient model) (λ phase → phase) → ⊥
noUniversalAbsolutePhaseRecovery model collision claimed =
  Core.consumerDescentDefectContradictsDescent
    claimed (gaugeCollisionDefect model collision)

-- An actual measured edge map may contain loop curl. The proof of exact
-- recovery MUST contain an exact-gradient certificate for that same map.
record ExactEdgeField
    {Phase Edges Source : Set}
    (model : PhasePoissonModel Phase Edges Source)
    (measurement : Edges) : Set where
  field
    sourcePhase : Phase
    isGradient : gradient model sourcePhase ≡ measurement

open ExactEdgeField public

exactEdgesRecovered :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  (measurement : Edges) →
  (witness : ExactEdgeField model measurement) →
  gradient model
    (solvePoisson model (divergence model measurement)) ≡ measurement
exactEdgesRecovered model measurement witness =
  trans
    (cong
      (λ edges → gradient model
        (solvePoisson model (divergence model edges)))
      (sym (isGradient witness)))
    (trans
      (cong (gradient model) (solveGradient model (sourcePhase witness)))
      (trans
        (gradientGaugeInvariant model (sourcePhase witness))
        (isGradient witness)))

-- A curl/cycle obstruction is stronger than the absence of a chosen decoder:
-- it proves that no phase potential explains the measured edge field at all.
record IncompatibleEdges
    {Phase Edges Source : Set}
    (model : PhasePoissonModel Phase Edges Source) : Set where
  field
    measurements : Edges
    noPotential : (phase : Phase) →
      gradient model phase ≡ measurements → ⊥

open IncompatibleEdges public

incompatibleEdgesDoNotCommute :
  {Phase Edges Source : Set} →
  (model : PhasePoissonModel Phase Edges Source) →
  (obstruction : IncompatibleEdges model) →
  gradient model
    (solvePoisson model (divergence model (measurements obstruction)))
    ≡ measurements obstruction → ⊥
incompatibleEdgesDoNotCommute model obstruction attempted =
  noPotential obstruction
    (solvePoisson model (divergence model (measurements obstruction)))
    attempted

-- Physical proof frontier: calibrated geometry, boundary conditions,
-- wrapped-phase handling, interpolation, finite photons, read noise, ADC,
-- uncertainty over gradient maps, and numerical error propagation.
