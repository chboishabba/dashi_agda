module DASHI.Physics.YangMills.YMClayE1ConcreteCylinderStateOS2Exact where

------------------------------------------------------------------------
-- CLAY E1: construct a single concrete continuum cylinder state from
-- an actual finite expectation sequence and selected scalar convergence.
-- Its normalization, linearity, positivity, and whole-Gram OS2 are
-- THEOREMS, not fresh Set-valued outcome fields.
--
-- The required original Wilson source convergence and finite positive-time
-- RP are genuine inputs of the existing convergence/OS theorems.
-- This proves an E1 subresult; it DOES NOT construct a 4D YM continuum,
-- OS0/OS1/OS3/OS5, local operators or nontriviality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2

module _
    {Observable : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (cylinder :
      Cylinder.ScalarCylinderExpectationLimitData Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws))
    (observableAlgebra : OS2.CylinderOSAlgebra Observable)
    (inputs : OS2.CylinderLimitOSInputs
      limitLaws cylinder observableAlgebra)
  where

  -- One selected continuum state, definitionally the limit of the
  -- finite original cylinder expectations, not a free Schwinger field.
  continuumCylinderState : Observable → ℝ
  continuumCylinderState = Cylinder.limitExpectation cylinder

  continuumCylinderZero :
    continuumCylinderState (Cylinder.zeroObservable cylinder)
      ≡ Cylinder.zero (RealLimit.canonicalCylinderAlgebra limitLaws)
  continuumCylinderZero = Cylinder.limitZero cylinder

  continuumCylinderNormalized :
    continuumCylinderState (Cylinder.oneObservable cylinder)
      ≡ Cylinder.one (RealLimit.canonicalCylinderAlgebra limitLaws)
  continuumCylinderNormalized = Cylinder.limitOne cylinder

  continuumCylinderAdditive :
    ∀ left right →
    continuumCylinderState (Cylinder.addObservable cylinder left right)
      ≡
    _+ℝ_ (continuumCylinderState left) (continuumCylinderState right)
  continuumCylinderAdditive = Cylinder.limitAdd cylinder

  continuumCylinderHomogeneous :
    ∀ scalar observable →
    continuumCylinderState
      (Cylinder.scaleObservable cylinder scalar observable)
      ≡ scalar *ℝ continuumCylinderState observable
  continuumCylinderHomogeneous = Cylinder.limitScale cylinder

  continuumCylinderPositive :
    ∀ observable →
    Cylinder.Nonnegative cylinder observable →
    0ℝ ≤ℝ continuumCylinderState observable
  continuumCylinderPositive = Cylinder.limitPositive cylinder

  -- Complete finite-word family: all complex coefficients are outside
  -- this selected real-cylinder sector. The real full-Gram positivity
  -- is transported by its actual finite-double-sum convergence theorem.
  continuumCylinderFullRealOS2 :
    OS.GramReflectionPositive
      (OS2.asOSGramLimitData inputs)
      continuumCylinderState
  continuumCylinderFullRealOS2 =
    OS2.continuumReflectionPositive inputs

  -- Selected individual cylinder expectations converge to THIS state;
  -- no independent continuum source may be smuggled into the conclusion.
  originalCylinderConvergesToConstructedState :
    ∀ observable →
    RealLimit.Converges sequenceLimit
      (λ cutoff → Cylinder.finiteExpectation cylinder cutoff observable)
      (continuumCylinderState observable)
  originalCylinderConvergesToConstructedState =
    Cylinder.selectedConverges cylinder
