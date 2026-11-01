module DASHI.Physics.Closure.NSAncientLiouvilleContradictionCompilerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- PURPOSE
-- This is only the downstream contradiction calculus.  It deliberately does
-- not postulate or mark closed either frontier theorem.  A physical blow-up
-- theorem must supply a bounded ancient limit carrying a genuine spatial
-- oscillation witness; an independent Liouville theorem must force every
-- bounded ancient limit in that class to be spatially constant.  Those two
-- inputs are contradictory, hence blow-up is impossible.
------------------------------------------------------------------------

open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.Closure.NSAncientBlowupOscillationNormalizationExact
  using (SpatiallyConstant; SpatialOscillationWitness;
         oscillationRulesOutSpatialConstancy)

noBlowupFromOscillatoryAncientExtractionAndLiouville :
  {Blowup X V : Set} →
  (BoundedAncientMild : (X → V) → Set) →
  (extract : Blowup → X → V) →
  ((b : Blowup) → BoundedAncientMild (extract b)) →
  ((u : X → V) → BoundedAncientMild u → SpatiallyConstant u) →
  ((b : Blowup) → SpatialOscillationWitness (extract b)) →
  ¬ Blowup
noBlowupFromOscillatoryAncientExtractionAndLiouville
  BoundedAncientMild extract extractedBounded liouville extractedOscillation blowup =
  oscillationRulesOutSpatialConstancy
    (extractedOscillation blowup)
    (liouville (extract blowup) (extractedBounded blowup))

-- Consequently the research cutset is exact:
--
-- R1. PeriodicSingularityProducesBoundedAncientOscillationWitness
--     (not merely |U(0,0)| = 1).
--
-- R2. BoundedAncientMildNavierStokesLiouville3D
--     for the exact extracted whole-space class.
--
-- Everything in this file after those inputs is constructive contradiction,
-- not another regularity estimate.
