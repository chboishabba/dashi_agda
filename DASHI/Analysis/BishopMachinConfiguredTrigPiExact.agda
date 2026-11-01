module DASHI.Analysis.BishopMachinConfiguredTrigPiExact where

------------------------------------------------------------------------
-- K05: ACTUAL ROUND11 BISHOP TRIGONOMETRIC CONFIGURATION AND MACHIN
-- QUARTER-ANGLE SEMANTIC CONNECTION, WITHOUT CROSS-PROVER PROMOTION.
--
-- John Machin (1706), Bishop & Bridges (1985),
-- DOI 10.1007/978-3-642-61667-9;
-- Zachary Murray (2022), arXiv:2205.08354.
-- Existing original owners:
--  BishopMachinArctanConstructionExact (actual Bishop Machin real);
--  BishopMachinQuarterAngleBranchExact (quarter-angle rational window);
--  BishopRound11MachinSetoidComplexInstanceExact (actual trig dataSet);
--  BishopSetoidComplexExact (actual configured complex exp/sine/cosine).
--
-- This proves source identity of the configured pi and trigonometric
-- carrier. It does NOT establish that the independently characterized
-- true trigonometric/geometric pi agrees with the configured choice.
-- The remaining sine/cosine addition, tangent and branch uniqueness
-- are analytic K05 lemmas; no external Lean proof is silently imported.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as Bishop

import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- The actual Round11 trig dataSet names the SAME Bishop Pi constructed
-- by the genuine convergent Machin series, not a number chosen afresh.
configuredMachinPiIsOriginal :
  (inputs : Round11.Round11BishopCutset) →
  Complex.pi (Route.round11MachinTranscendentals inputs)
    ≡ Machin.bishopMachinPi
configuredMachinPiIsOriginal inputs = refl

-- Native Bishop setoid equality for the canonical quarter angle.
configuredFourTimesQuarterIsPi :
  (inputs : Round11.Round11BishopCutset) →
  Bishop._≃_
    (Bishop._*_ (Bishop._⋆ (+ 4 / 1)) Quarter.machinQuarterAngle)
    (Complex.pi (Route.round11MachinTranscendentals inputs))
configuredFourTimesQuarterIsPi inputs =
  Quarter.fourTimesQuarterIsMachinPi

-- The geometric source of piC is this exact configured real at 0i.
configuredPiComplexReal :
  (inputs : Round11.Round11BishopCutset) →
  Complex.re (Complex.piC (Route.round11MachinTranscendentals inputs))
    ≡ Machin.bishopMachinPi
configuredPiComplexReal inputs = refl

configuredPiComplexImaginaryZero :
  (inputs : Round11.Round11BishopCutset) →
  Complex.im (Complex.piC (Route.round11MachinTranscendentals inputs))
    ≡ Bishop.0ℝ
configuredPiComplexImaginaryZero inputs = refl

-- True constructed sine/cosine consumers, already supplied as concrete
-- Round11 signed-factorial power series. No assumption of sine(pi)=0.
configuredSinAtMachinPi :
  (inputs : Round11.Round11BishopCutset) →
  Bishop.ℝ
configuredSinAtMachinPi inputs =
  Elementary.bishopSin
    (Complex.dataSet (Route.round11MachinTranscendentals inputs))
    Machin.bishopMachinPi

configuredCosAtMachinPi :
  (inputs : Round11.Round11BishopCutset) →
  Bishop.ℝ
configuredCosAtMachinPi inputs =
  Elementary.bishopCos
    (Complex.dataSet (Route.round11MachinTranscendentals inputs))
    Machin.bishopMachinPi

-- K05 terminal mathematical acceptance (NOT proved here):
--   configuredSinAtMachinPi inputs ≃ 0ℝ
--   configuredCosAtMachinPi inputs ≃ (- 1ℝ)
-- together with the appropriate constructive branch/period uniqueness
-- linking to an independent classical trigonometric pi.
-- The existing Lean source-written Machin semantic result is not an
-- Agda kernel witness or substitute for these actual sine/cosine laws.
