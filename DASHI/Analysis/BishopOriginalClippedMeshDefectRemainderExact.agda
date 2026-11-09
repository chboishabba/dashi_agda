module DASHI.Analysis.BishopOriginalClippedMeshDefectRemainderExact where

------------------------------------------------------------------------
-- P0.06: ORIGINAL CLIPPED EQUAL-MESH QUOTIENT REMAINDER EVALUATION.
--
-- Let the original clipped mesh have m=n+1 equal nonzero steps
-- h_n=x/(n+1), then zero steps. At the endpoint exactly x:
--
-- sum(j<m) h_j * B_N(R,h_j) = x * B_N(R,h_n).
--
-- This identity reuses the pinned finite sum and Nat reciprocal
-- cancellation. The source h_n converges to 0 by the ORIGINAL
-- Basel reciprocalSequenceConvergesZero, and B_N(R,h_n)->0 by
-- the previously proved original quotient modulus.
--
-- Therefore the entire finite-mesh remainder converges to 0.
-- No abstract mesh refinement/FTC field or synthetic real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopOriginalClippedEqualMeshExact as Clip
import DASHI.Analysis.BishopOriginalFiniteNormalizedEndpointQuadratureRemainderExact as Quad
import DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact as Defect
import DASHI.Analysis.BishopOriginalFiniteLogExpUniformDefectNullModulusExact as Null
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Scale
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as ScaleBridge
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel

originalClippedFiniteSumShift :
  (term : R.ℝ → R.ℝ) (step : R.ℝ) (cells j : Nat) →
  R._≃_
    (Walk.sumFinite
      (λ k → term (Clip.sourceClippedConstantSteps (suc cells) step k))
      (suc j))
    (R._+_
      (term step)
      (Walk.sumFinite
        (λ k → term (Clip.sourceClippedConstantSteps cells step k))
        j))
originalClippedFiniteSumShift term step cells zero =
  let open RP.ℝ-Solver in
  solve 1
    (λ hh → Κ 0ℚᵘ ⊕ hh ⊜ hh ⊕ Κ 0ℚᵘ)
    RP.≃-refl (term step)
originalClippedFiniteSumShift term step cells (suc j) =
  let
    first = term step
    rest = Walk.sumFinite
      (λ k → term (Clip.sourceClippedConstantSteps cells step k))
      j
    next = term (Clip.sourceClippedConstantSteps cells step j)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (originalClippedFiniteSumShift term step cells j)
      RP.≃-refl)
    (solve 3
      (λ ff rr nn →
        (ff ⊕ rr) ⊕ nn
        ⊜ ff ⊕ (rr ⊕ nn))
      RP.≃-refl first rest next)

originalClippedFiniteSumIsNatScale :
  (term : R.ℝ → R.ℝ) (step : R.ℝ) (cells : Nat) →
  R._≃_
    (Walk.sumFinite
      (λ j → term (Clip.sourceClippedConstantSteps cells step j))
      cells)
    (Scale.natScale cells (term step))
originalClippedFiniteSumIsNatScale term step zero = RP.≃-refl
originalClippedFiniteSumIsNatScale term step (suc cells) =
  RP.≃-trans
    (originalClippedFiniteSumShift term step cells cells)
    (RP.≃-trans
      (RP.+-cong RP.≃-refl
        (originalClippedFiniteSumIsNatScale term step cells))
      (RP.+-comm (term step) (Scale.natScale cells (term step))))

originalEqualClippedMeshDefectRemainderEqualsBudget :
  (stage : Nat) (radius x : R.ℝ) (n : Nat) →
  let
    h = Clip.sourceEqualStep x n
    b = Defect.sourceOriginalUniformErrorBudget stage radius h
    steps = Clip.sourceClippedEqualSteps x n
  in
  R._≃_
    (Walk.sumFinite
      (Quad.sourceDefectQuadratureCell stage radius steps)
      (suc n))
    (R._*_ x b)
originalEqualClippedMeshDefectRemainderEqualsBudget
    stage radius x n =
  let
    h = Clip.sourceEqualStep x n
    b = Defect.sourceOriginalUniformErrorBudget stage radius h
    t = λ step →
      R._*_ step
        (Defect.sourceOriginalUniformErrorBudget
          stage radius step)
    count = NatReal.natReal (suc n)
    recip = R._⋆ (Recip.reciprocalNatRational n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (originalClippedFiniteSumIsNatScale t h (suc n))
    (RP.≃-trans
      (ScaleBridge.recursiveScaleIsEmbeddedNaturalMultiply
        (suc n) (R._*_ h b))
      (RP.≃-trans
        (solve 4
          (λ cc xx rr bb →
            cc ⊗ ((xx ⊗ rr) ⊗ bb)
            ⊜ (xx ⊗ (rr ⊗ cc)) ⊗ bb)
          RP.≃-refl count x recip b)
        (RP.≃-trans
          (RP.*-cong
            (RP.*-cong RP.≃-refl
              (Recip.embeddedReciprocalNatCancels n))
            RP.≃-refl)
          (solve 2
            (λ xx bb →
              (xx ⊗ Κ 1ℚᵘ) ⊗ bb
              ⊜ xx ⊗ bb)
            RP.≃-refl x b))))

originalEqualStepConvergesToZero :
  (x : R.ℝ) →
  Seq._ConvergesTo_
    (λ n → Clip.sourceEqualStep x n)
    R.0ℝ
originalEqualStepConvergesToZero x =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙyₙ→x₀y₀
      (x , Power.constantConverges x)
      (R.0ℝ , Basel.reciprocalSequenceConvergesZero))
    (let open RP.ℝ-Solver in
     solve 1
       (λ xx → xx ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl x)

originalEqualClippedMeshDefectBudgetConvergesZero :
  (stage : Nat) (radius x : R.ℝ) →
  Seq._ConvergesTo_
    (λ n →
      R._*_ x
        (Defect.sourceOriginalUniformErrorBudget
          stage radius (Clip.sourceEqualStep x n)))
    R.0ℝ
originalEqualClippedMeshDefectBudgetConvergesZero
    stage radius x =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙyₙ→x₀y₀
      (x , Power.constantConverges x)
      (R.0ℝ ,
        Null.originalFiniteLogStagewiseUniformBudgetConvergesZero
          stage radius (originalEqualStepConvergesToZero x)))
    (let open RP.ℝ-Solver in
     solve 1
       (λ xx → xx ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl x)
