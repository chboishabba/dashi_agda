module DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact where

------------------------------------------------------------------------
-- K05: TRUE BISHOP RING-ALGEBRA QUADRUPLICATION AT MACHIN QUARTER.
--
-- For x=cos_B(theta), y=sin_B(theta), assume x~y and
-- x*x+y*y~1, on the *same* Round11 Bishop trig dataSet.
-- The standard double-angle POLYNOMIALS then satisfy
--   sin(4theta)-POLYNOMIAL ~ 0, cos(4theta)-POLYNOMIAL ~ -1.
--
-- This is NOT a claim that sin_B(4theta) equals the polynomial:
-- the sine/cosine addition identities for the actual Bishop series
-- must still be proved and connected to the original rational
-- tangent/algebraic arctangent source (K05 terminal).
--
-- Historical source: classical trigonometry / Machin 1706;
-- Bishop & Bridges 1985, DOI 10.1007/978-3-642-61667-9;
-- Murray 2022 arXiv:2205.08354, pinned viktorcsimma/bishop.
-- DASHI proof uses original real setoid and checked polynomial solver.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Q
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

two : R.ℝ
two = R._⋆ (+ 2 / 1)

sinDoublePolynomial cosDoublePolynomial : R.ℝ → R.ℝ → R.ℝ
sinDoublePolynomial x y =
  R._*_ (R._*_ two x) y
cosDoublePolynomial x y =
  R._-_ (R._*_ x x) (R._*_ y y)

sinFourfoldPolynomial cosFourfoldPolynomial : R.ℝ → R.ℝ → R.ℝ
sinFourfoldPolynomial x y =
  R._*_ (R._*_ two (sinDoublePolynomial x y))
    (cosDoublePolynomial x y)
cosFourfoldPolynomial x y =
  R._-_
    (R._*_ (cosDoublePolynomial x y) (cosDoublePolynomial x y))
    (R._*_ (sinDoublePolynomial x y) (sinDoublePolynomial x y))

sinDoubleAsCrossSum :
  ∀ x y →
  R._≃_
    (sinDoublePolynomial x y)
    (R._+_ (R._*_ x y) (R._*_ y x))
sinDoubleAsCrossSum x y =
  let open RP.ℝ-Solver
  in solve 2
    (λ x y →
      ((Κ (+ 2 / 1) ⊗ x) ⊗ y)
      ⊜ ((x ⊗ y) ⊕ (y ⊗ x)))
    RP.≃-refl x y

sinDoubleIsOneAtEqualUnitPhase :
  ∀ x y →
  R._≃_ x y →
  R._≃_
    (R._+_ (R._*_ x x) (R._*_ y y))
    R.1ℝ →
  R._≃_ (sinDoublePolynomial x y) R.1ℝ
sinDoubleIsOneAtEqualUnitPhase x y equal unit =
  RP.≃-trans
    (sinDoubleAsCrossSum x y)
    (RP.≃-trans
      (RP.+-cong
        (RP.*-cong RP.≃-refl (RP.≃-symm equal))
        (RP.*-cong RP.≃-refl equal))
      unit)

cosDoubleIsZeroAtEqualPhase :
  ∀ x y →
  R._≃_ x y →
  R._≃_ (cosDoublePolynomial x y) R.0ℝ
cosDoubleIsZeroAtEqualPhase x y equal =
  RP.≃-trans
    (RP.+-cong
      (RP.*-cong equal equal)
      RP.≃-refl)
    (let open RP.ℝ-Solver
     in solve 1
       (λ y → (y ⊗ y) ⊖ (y ⊗ y) ⊜ Κ 0ℚᵘ)
       RP.≃-refl y)

sinFourfoldIsZeroAtEqualUnitPhase :
  ∀ x y →
  R._≃_ x y →
  R._≃_ (sinFourfoldPolynomial x y) R.0ℝ
sinFourfoldIsZeroAtEqualUnitPhase x y equal =
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl
      (cosDoubleIsZeroAtEqualPhase x y equal))
    (let open RP.ℝ-Solver
     in solve 1
       (λ s → (Κ (+ 2 / 1) ⊗ s) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       RP.≃-refl
       (sinDoublePolynomial x y))

cosFourfoldIsMinusOneAtEqualUnitPhase :
  ∀ x y →
  R._≃_ x y →
  R._≃_
    (R._+_ (R._*_ x x) (R._*_ y y))
    R.1ℝ →
  R._≃_
    (cosFourfoldPolynomial x y)
    (R.-_ R.1ℝ)
cosFourfoldIsMinusOneAtEqualUnitPhase x y equal unit =
  RP.≃-trans
    (RP.+-cong
      (RP.*-cong
        (cosDoubleIsZeroAtEqualPhase x y equal)
        (cosDoubleIsZeroAtEqualPhase x y equal))
      (RP.-‿cong
        (RP.*-cong
          (sinDoubleIsOneAtEqualUnitPhase x y equal unit)
          (sinDoubleIsOneAtEqualUnitPhase x y equal unit))))
    (let open RP.ℝ-Solver
     in solve 0
       (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊖ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)
        ⊜ ⊝ (Κ 1ℚᵘ))
       RP.≃-refl)

-- ACTUAL round11 trigonometric power-series functions and actual
-- original Bishop Machin quarter-angle are the consumers.
quarterSin quarterCos :
  Round11.Round11BishopCutset → R.ℝ
quarterSin inputs =
  E.bishopSin
    (Complex.dataSet (Route.round11MachinTranscendentals inputs))
    Q.machinQuarterAngle
quarterCos inputs =
  E.bishopCos
    (Complex.dataSet (Route.round11MachinTranscendentals inputs))
    Q.machinQuarterAngle

-- Constructive K05 reduction with no new postulate:
-- exact algebraic fourfold endpoint from the two *explicit*
-- original analytic proof obligations.
quarterUnitPhaseGivesFourfoldEndpoint :
  ∀ inputs →
  R._≃_ (quarterCos inputs) (quarterSin inputs) →
  R._≃_
    (R._+_
      (R._*_ (quarterCos inputs) (quarterCos inputs))
      (R._*_ (quarterSin inputs) (quarterSin inputs)))
    R.1ℝ →
  (R._≃_
    (sinFourfoldPolynomial (quarterCos inputs) (quarterSin inputs))
    R.0ℝ)
  ×
  (R._≃_
    (cosFourfoldPolynomial (quarterCos inputs) (quarterSin inputs))
    (R.-_ R.1ℝ))
quarterUnitPhaseGivesFourfoldEndpoint inputs equal unit =
  sinFourfoldIsZeroAtEqualUnitPhase
    (quarterCos inputs) (quarterSin inputs) equal
  ,
  cosFourfoldIsMinusOneAtEqualUnitPhase
    (quarterCos inputs) (quarterSin inputs) equal unit

------------------------------------------------------------------------
-- K05 actual endpoint bridge. The only additional premises are the
-- genuine, independently owed same-object sine/cosine quadruplication
-- identities and true quarter-angle predicates. The proof itself
-- invokes original Round11 term identification and original
-- fourTimesQuarterIsMachinPi; no Lean result is imported to Agda.
------------------------------------------------------------------------

fourTimesQuarter : R.ℝ
fourTimesQuarter =
  R._*_ (R._⋆ (+ 4 / 1)) Q.machinQuarterAngle

round11Sine round11Cos :
  Round11.Round11BishopCutset → R.ℝ → R.ℝ
round11Sine inputs =
  E.bishopSin (Round11.elementarySeries inputs)
round11Cos inputs =
  E.bishopCos (Round11.elementarySeries inputs)

-- The true analytic addition theorem must establish these two identities
-- independently; they are not exported as a postulate or smuggled into the
-- original core. All other proof transport below is algebra/setoid.
quarterSemanticBridgeToActualMachinPi :
  (inputs : Round11.Round11BishopCutset) →
  R._≃_ (quarterCos inputs) (quarterSin inputs) →
  R._≃_
    (R._+_
      (R._*_ (quarterCos inputs) (quarterCos inputs))
      (R._*_ (quarterSin inputs) (quarterSin inputs)))
    R.1ℝ →
  R._≃_
    (round11Sine inputs fourTimesQuarter)
    (sinFourfoldPolynomial (quarterCos inputs) (quarterSin inputs)) →
  R._≃_
    (round11Cos inputs fourTimesQuarter)
    (cosFourfoldPolynomial (quarterCos inputs) (quarterSin inputs)) →
  (R._≃_ (round11Sine inputs Machin.bishopMachinPi) R.0ℝ)
  ×
  (R._≃_ (round11Cos inputs Machin.bishopMachinPi) (R.-_ R.1ℝ))
quarterSemanticBridgeToActualMachinPi
  inputs quarterEqual pythag sineQuad cosineQuad =
  let
    endpoint =
      quarterUnitPhaseGivesFourfoldEndpoint
        inputs quarterEqual pythag
    actualSinTransport :
      R._≃_
        (round11Sine inputs Machin.bishopMachinPi)
        (round11Sine inputs fourTimesQuarter)
    actualSinTransport =
      RP.≃-symm
        (TrigCong.bishopSinCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          Q.fourTimesQuarterIsMachinPi)
    actualCosTransport :
      R._≃_
        (round11Cos inputs Machin.bishopMachinPi)
        (round11Cos inputs fourTimesQuarter)
    actualCosTransport =
      RP.≃-symm
        (TrigCong.bishopCosCongruent
          (Round11.round11ConcreteTermIdentification inputs)
          Q.fourTimesQuarterIsMachinPi)
  in
  RP.≃-trans actualSinTransport
    (RP.≃-trans sineQuad (proj₁ endpoint))
  ,
  RP.≃-trans actualCosTransport
    (RP.≃-trans cosineQuad (proj₂ endpoint))
