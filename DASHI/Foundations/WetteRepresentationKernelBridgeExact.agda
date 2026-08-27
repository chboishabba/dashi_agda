module DASHI.Foundations.WetteRepresentationKernelBridgeExact where

------------------------------------------------------------------------
-- WETTE / REPRESENTATION-KERNEL CROSS-POLLINATION
--
-- The Wette reconstruction already carries a one-step simulation square.
-- Rather than maintain a parallel trajectory theory, this module packages a
-- fixed generator as the repository's existing canonical
-- RepresentationKernelCompatibility owner. All n-step, observable,
-- fixed-point, and finite-reachability transport then come from that owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Physics.Closure.RepresentationKernelCompatibility as R

fixedGeneratorCompatibility :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (g : W.Generator machine) →
  R.RepresentationKernelCompatibility
fixedGeneratorCompatibility {machine} simulation g =
  record
    { FineState = W.Syntax simulation
    ; CoarseState = W.State machine
    ; Observable = W.State machine
    ; fineStep = W.syntaxStep simulation g
    ; coarseStep = W.step machine g
    ; project = W.encode simulation
    ; fineAdmissible =
        λ term → W.admissible machine (W.encode simulation term) ≡ true
    ; coarseAdmissible =
        λ state → W.admissible machine state ≡ true
    ; fineObserve = W.encode simulation
    ; coarseObserve = λ state → state
    ; fineAdmissibleStep = fineStepPreservesAdmissibility
    ; coarseAdmissibleStep =
        λ {x} admissible → W.preservesAdmissible machine g x admissible
    ; projectPreservesAdmissibility = λ admissible → admissible
    ; projectPreservesObservable = λ _ → refl
    ; kernelCommutesWithProjection =
        λ {x} _ → W.stepCommutes simulation g x
    }
  where
  fineStepPreservesAdmissibility :
    {term : W.Syntax simulation} →
    W.admissible machine (W.encode simulation term) ≡ true →
    W.admissible machine
      (W.encode simulation (W.syntaxStep simulation g term)) ≡ true
  fineStepPreservesAdmissibility {term} admissible
    rewrite W.stepCommutes simulation g term =
      W.preservesAdmissible machine g (W.encode simulation term) admissible

------------------------------------------------------------------------
-- Canonical consequences imported from RepresentationKernelCompatibility.
------------------------------------------------------------------------

canonicalTrajectoryCommutes :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (g : W.Generator machine) →
  {term : W.Syntax simulation} →
  W.admissible machine (W.encode simulation term) ≡ true →
  ∀ n →
  W.encode simulation
    (R.iterate (W.syntaxStep simulation g) n term)
  ≡
  R.iterate (W.step machine g) n (W.encode simulation term)
canonicalTrajectoryCommutes simulation g admissible =
  R.trajectoryCommutes (fixedGeneratorCompatibility simulation g) admissible

canonicalProjectedFixedPoint :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (g : W.Generator machine) →
  {term : W.Syntax simulation} →
  W.admissible machine (W.encode simulation term) ≡ true →
  R.FixedPoint (W.syntaxStep simulation g) term →
  R.FixedPoint (W.step machine g) (W.encode simulation term)
canonicalProjectedFixedPoint simulation g admissible =
  R.projectedFixedPoint (fixedGeneratorCompatibility simulation g) admissible

canonicalProjectedEventuallyReaches :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (g : W.Generator machine) →
  {term target : W.Syntax simulation} →
  W.admissible machine (W.encode simulation term) ≡ true →
  R.EventuallyReaches (W.syntaxStep simulation g) term target →
  R.EventuallyReaches
    (W.step machine g)
    (W.encode simulation term)
    (W.encode simulation target)
canonicalProjectedEventuallyReaches simulation g admissible =
  R.projectedEventuallyReaches
    (fixedGeneratorCompatibility simulation g)
    admissible

------------------------------------------------------------------------
-- Interpretation boundary.
--
-- This proves a general theorem: IF source syntax and machine semantics satisfy
-- WetteDeductionSimulation, then the canonical DASHI representation-kernel
-- theorem stack applies. It does not assert that Wette's historical syntax or
-- generator family has already been recovered.
------------------------------------------------------------------------
