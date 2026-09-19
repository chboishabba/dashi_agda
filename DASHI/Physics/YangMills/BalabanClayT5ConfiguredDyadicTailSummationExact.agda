module DASHI.Physics.YangMills.BalabanClayT5ConfiguredDyadicTailSummationExact where

------------------------------------------------------------------------
-- CONFIGURED ONE-STEP DYADIC DEFECT -> UNIFORM FINITE TAIL
--
-- The live T5 continuum instance already fixes the physical one-step envelope
--
--     d_k <= (1/4) (1/2)^k.
--
-- What was still being carried separately in
-- BalabanClayT5ConfiguredPhysicalTailMomentInstanceExact was a finite
-- telescoping-tail control premise.  That quantitative summation is not an
-- independent Yang--Mills estimate: it is the geometric-series theorem already
-- proved in the T2 Ursell lane.
--
-- This module identifies the two dyadic carriers definitionally and reuses the
-- machine-checked T2 tail theorem.  Consequently any pointwise defect sequence
-- below the configured rooted-shell tail has, for every finite interval,
--
--   sum_{j=0}^{N-1} d_{k+j} <= (1/2) (1/2)^k.
--
-- The remaining physical input is the literal one-step localization/defect
-- estimate and the exact telescoping identity tying those defects to the
-- selected expectation difference.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredPhysicalTailMomentInstanceExact as Configured
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

------------------------------------------------------------------------
-- The configured T5 and earlier T2 lanes use the same numerical dyadic
-- sequence.  Pin that sameness explicitly so the old analytic theorem can be
-- consumed without a parallel majorant.
------------------------------------------------------------------------

powHalfAgreement : ∀ depth →
  Tail.powHalf depth ≡ Geo.halfPower depth
powHalfAgreement zero = refl
powHalfAgreement (suc depth) =
  cong (Geo.half *_) (powHalfAgreement depth)

rootedShellTailAgreement : ∀ depth →
  Tail.rootedShellTail depth
  ≡ Ursell.quarter * Geo.halfPower depth
rootedShellTailAgreement depth =
  cong (Ursell.quarter *_) (powHalfAgreement depth)

finiteDyadicTailAgreement : ∀ start count →
  Configured.finiteDyadicTail start count
  ≡ Ursell.geometricTailPartial start count
finiteDyadicTailAgreement start zero = refl
finiteDyadicTailAgreement start (suc count) =
  cong₂ _+_
    (rootedShellTailAgreement start)
    (finiteDyadicTailAgreement (suc start) count)

configuredInfiniteTailAgreement : ∀ start →
  Configured.configuredInfiniteTailMajorant start
  ≡ Geo.half * Geo.halfPower start
configuredInfiniteTailAgreement start =
  cong (Geo.half *_) (powHalfAgreement start)

configuredFiniteDyadicTailBelowInfiniteMajorant : ∀ start count →
  Configured.finiteDyadicTail start count
  ≤ Configured.configuredInfiniteTailMajorant start
configuredFiniteDyadicTailBelowInfiniteMajorant start count =
  subst
    (λ left →
      left ≤ Configured.configuredInfiniteTailMajorant start)
    (sym (finiteDyadicTailAgreement start count))
    (subst
      (λ right →
        Ursell.geometricTailPartial start count ≤ right)
      (sym (configuredInfiniteTailAgreement start))
      (Ursell.geometricTailBelow start count))

------------------------------------------------------------------------
-- Generic defect summation.  No positivity assumption on d_k is needed for an
-- upper bound: pointwise monotonicity and the exact finite dyadic envelope are
-- enough.
------------------------------------------------------------------------

defectPartial : (Nat → ℚ) → Nat → Nat → ℚ
defectPartial defect start zero = 0ℚ
defectPartial defect start (suc count) =
  defect start + defectPartial defect (suc start) count

pointwiseDefectBelowFiniteDyadicTail :
  (defect : Nat → ℚ) →
  (∀ depth → defect depth ≤ Tail.rootedShellTail depth) →
  ∀ start count →
  defectPartial defect start count
  ≤ Configured.finiteDyadicTail start count
pointwiseDefectBelowFiniteDyadicTail defect pointwise start zero =
  Ursell.rationalReflexive 0ℚ
pointwiseDefectBelowFiniteDyadicTail defect pointwise start (suc count) =
  ℚP.+-mono-≤
    (pointwise start)
    (pointwiseDefectBelowFiniteDyadicTail
      defect pointwise (suc start) count)

pointwiseRootedShellBoundToUniformFiniteTail :
  (defect : Nat → ℚ) →
  (∀ depth → defect depth ≤ Tail.rootedShellTail depth) →
  ∀ start count →
  defectPartial defect start count
  ≤ Configured.configuredInfiniteTailMajorant start
pointwiseRootedShellBoundToUniformFiniteTail defect pointwise start count =
  trans
    (pointwiseDefectBelowFiniteDyadicTail
      defect pointwise start count)
    (configuredFiniteDyadicTailBelowInfiniteMajorant start count)

configuredDyadicFiniteSummationLevel : ProofLevel
configuredDyadicFiniteSummationLevel = machineChecked

configuredDefectFiniteTailCompilerLevel : ProofLevel
configuredDefectFiniteTailCompilerLevel = machineChecked

-- Still physical: identify the literal RG expectation difference with the
-- finite sum of the one-step defects and prove each literal defect is below the
-- rooted-shell bound.
literalOneStepDefectEstimateLevel : ProofLevel
literalOneStepDefectEstimateLevel = conditional

literalTelescopingIdentityLevel : ProofLevel
literalTelescopingIdentityLevel = conditional
