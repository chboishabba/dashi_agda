{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP122ROperationReflectionSupportCutExact where

------------------------------------------------------------------------
-- CMP122 R-OPERATION / OS SUPPORT CUT
--
-- Equation (1.100) is already indexed by one source polymer X.  When that
-- Polymer parameter is instantiated by the repository's literal periodic
-- block-polymer carrier, the same X can be classified relative to the selected
-- OS time cut without changing the source norm or its exponential-decay bound.
--
-- This file therefore separates two orthogonal facts:
--   * support geometry: positive-only / negative-only / crossing;
--   * CMP122 source control: |R^(k)(X)| <= exp(-p0) exp(-kappa d_k(X)).
--
-- Decay does not imply reflection positivity.  Crossing R-polymers still need
-- an actual cross-plane kernel theorem (or counterexample).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as Source
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Geometry

ROperationPositiveOnly :
  ∀ {n Scale Boundary} → Nat → Periodic.PeriodicPolymer n → Set
ROperationPositiveOnly cut polymer =
  Geometry.polymerPositiveOnly cut polymer

ROperationNegativeOnly :
  ∀ {n Scale Boundary} → Nat → Periodic.PeriodicPolymer n → Set
ROperationNegativeOnly cut polymer =
  Geometry.polymerNegativeOnly cut polymer

ROperationCrossing :
  ∀ {n Scale Boundary} → Nat → Periodic.PeriodicPolymer n → Set
ROperationCrossing cut polymer =
  Geometry.polymerCrossesReflectionCut cut polymer

/--
The imported CMP122 Eq. (1.100) bound survives unchanged on a crossing
polymer.  The support proof is deliberately unused in the arithmetic: it
records which source terms need a later RP audit, not a stronger decay claim.
-/
rOperationCrossingEquation1100 :
  ∀ {n Scale Boundary}
    (source : Source.CMP122Equation1100Pointwise
      Scale (Periodic.PeriodicPolymer n) Boundary)
    cut scale polymer boundary →
  ROperationCrossing {Scale = Scale} {Boundary = Boundary} cut polymer →
  Source.rNorm source scale polymer boundary
  ≤ Source.p0Suppression source scale *
      Source.diameterDecay source scale polymer
rOperationCrossingEquation1100 source cut scale polymer boundary crossing =
  Source.equation1100 source scale polymer boundary

rOperationReflectionSupportCutCompilerLevel : ProofLevel
rOperationReflectionSupportCutCompilerLevel = machineChecked

-- The exact CMP122 source Polymer still has to be identified with this literal
-- periodic carrier at the selected cutoff.
cmp122ROperationPublishedPolymerToPeriodicCarrierLevel : ProofLevel
cmp122ROperationPublishedPolymerToPeriodicCarrierLevel = conditional

-- One-sided source activities must still be shown to transform into each other
-- under the selected OS reflection.
cmp122ROperationOneSidedActivityReflectionLevel : ProofLevel
cmp122ROperationOneSidedActivityReflectionLevel = conditional

-- Crossing source activities require an independently PSD kernel or an explicit
-- obstruction.  Eq. (1.100) alone does not supply positivity.
cmp122ROperationCrossingKernelRPLevel : ProofLevel
cmp122ROperationCrossingKernelRPLevel = conditional
