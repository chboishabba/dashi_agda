module DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact where

------------------------------------------------------------------------
-- CLAY E1: original changing-cutoff four-torus Wilson family, not a
-- sequence of measures on a fictitious cutoff-independent link carrier.
-- This module actually SELECTS the original SUN Wilson/Gibbs measure
-- and its genuine normalized Haar expectation at EVERY finite cutoff.
-- The analytic existence of a common limiting cylinder functional is
-- NOT deduced from these finite identities.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Wilson
import DASHI.Physics.YangMills.YMClayOriginalWilsonFiniteTwoSourceJetExact as Original
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YMClayE1VariableCutoffCylinderLimitExact as E1

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  ActualLinks : Nat → Set
  ActualLinks n = Wilson.SUNPeriodicLinks theory n

  -- This is the FULL algebra of cutoff-dependent sections, used ONLY
  -- to identify the original finite-measure source. Not every such
  -- section converges: e.g. arbitrary n-parity-dependent constants.
  -- A true E1 continuum state must restrict to a physically admissible
  -- local cylinder selection with gauge/embedding compatibility.
  -- Each selected section is represented on ALL original finite
  -- lattices; its domain genuinely changes with n.
  Cylinder : Set
  Cylinder = (n : Nat) → ActualLinks n → ℝ

  zeroCylinder : Cylinder
  zeroCylinder n links = 0ℝ

  oneCylinder : Cylinder
  oneCylinder n links = 1ℝ

  addCylinder : Cylinder → Cylinder → Cylinder
  addCylinder left right n links =
    left n links +ℝ right n links

  scaleCylinder : ℝ → Cylinder → Cylinder
  scaleCylinder scalar observable n links =
    scalar *ℝ observable n links

  originalDependentCylinderRealization :
    E1.CylinderRealization ActualLinks Cylinder ℝ
  originalDependentCylinderRealization = record
    { E1.CylinderRealization.realization =
        λ n cylinder → cylinder n
    ; E1.CylinderRealization.zeroObservable = zeroCylinder
    ; E1.CylinderRealization.oneObservable = oneCylinder
    ; E1.CylinderRealization.addObservable = addCylinder
    ; E1.CylinderRealization.scalarObservable = scaleCylinder
    }

  actualOriginalWilsonMeasureAt :
    (n : Nat) →
    Physical.PhysicalFiniteYMMeasure (ActualLinks n) ℝ
  actualOriginalWilsonMeasureAt n =
    Original.originalWilsonMeasure
      theory traceData exponential beta oneLink bilateral divide n

  actualOriginalWilsonCylinderExpectation :
    (n : Nat) → Cylinder → ℝ
  actualOriginalWilsonCylinderExpectation n cylinder =
    Physical.normalizedExpectation
      (actualOriginalWilsonMeasureAt n) (cylinder n)

  -- Definitional, every cutoff; not a new measure, fake common lattice
  -- or independently selected functional.
  nativeSUNSelectedFiniteExpectationIsLiteralWilson :
    ∀ n cylinder →
    actualOriginalWilsonCylinderExpectation n cylinder
      ≡ Physical.normalizedExpectation
          (actualOriginalWilsonMeasureAt n)
          (E1.realization originalDependentCylinderRealization n cylinder)
  nativeSUNSelectedFiniteExpectationIsLiteralWilson n cylinder = refl

  -- Target remains SOURCE convergence of this exact varying-carrier
  -- sequence for its gauge-invariant cylinder algebra; those witnesses
  -- are deliberately NOT manufactured by the finite identity above.
