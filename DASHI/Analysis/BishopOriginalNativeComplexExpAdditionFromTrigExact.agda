module DASHI.Analysis.BishopOriginalNativeComplexExpAdditionFromTrigExact where

------------------------------------------------------------------------
-- P2 ORIGINAL BISHOP expC ADDITION: REAL-EXP ADD + TWO TRIG LEAVES.
--
-- Provenance:
--   Errett Bishop and Douglas Bridges, Constructive Analysis (1985).
--   Zachary Murray, Constructive Analysis in the Agda Proof Assistant
--   (2022), arXiv:2205.08354, DOI 10.48550/arXiv.2205.08354.
--   DASHI original source owners: BishopExponentialCauchyProductExact
--   (REAL exp add), BishopSetoidComplexExact (actual expC),
--   BishopRiemannAnalyticSetoidExpReuseExact (literal carrier weld),
--   BishopOriginalEtaDyadicSourceLawReductionExact (selected P2).
--
-- The real exponential addition law is ALREADY CONSTRUCTED in DASHI.
-- We derive original complex exp addition algebraically using that law
-- and precisely TWO UNINHABITED source-specific trig identities:
--   cos(y+b) ≃ cos(y)cos(b) - sin(y)sin(b);
--   sin(y+b) ≃ sin(y)cos(b) + cos(y)sin(b).
--
-- Unlike an abstract ComplexExponentialHomomorphism, this has the
-- original vendor Bishop ℝ setoid, exact expC and source Riemann pair.
-- No postulate, synthetic exponential, quotient, or arbitrary oracle
-- for expC is introduced. The two trig laws remain mathematical gates;
-- this is NOT a completed expC-add theorem or RH theorem.
-- Pinned Agda 2.9 kernel acceptance of the new source remains OPEN.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as RealExp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as Bridge
import DASHI.Analysis.BishopOriginalEtaDyadicSourceLawReductionExact as Dyadic

-- The actual sine/cosine source data, not an unrelated trigonometric
-- package with functions allowed to diverge from the selected expC.
OriginalCosineAddition :
  C.BishopSetoidComplexTranscendentals → Set
OriginalCosineAddition T =
  (y b : R.ℝ) →
  R._≃_
    (Elementary.bishopCos (C.dataSet T) (R._+_ y b))
    (R._-_
      (R._*_
        (Elementary.bishopCos (C.dataSet T) y)
        (Elementary.bishopCos (C.dataSet T) b))
      (R._*_
        (Elementary.bishopSin (C.dataSet T) y)
        (Elementary.bishopSin (C.dataSet T) b)))

OriginalSineAddition :
  C.BishopSetoidComplexTranscendentals → Set
OriginalSineAddition T =
  (y b : R.ℝ) →
  R._≃_
    (Elementary.bishopSin (C.dataSet T) (R._+_ y b))
    (R._+_
      (R._*_
        (Elementary.bishopSin (C.dataSet T) y)
        (Elementary.bishopCos (C.dataSet T) b))
      (R._*_
        (Elementary.bishopCos (C.dataSet T) y)
        (Elementary.bishopSin (C.dataSet T) b)))

originalBishopExpCAddFromNativeRealExpAndTrig :
  (T : C.BishopSetoidComplexTranscendentals) →
  OriginalCosineAddition T →
  OriginalSineAddition T →
  (z w : C.BishopComplex) →
  C._≈C_
    (C.expC T (C._+C_ z w))
    (C._*C_ (C.expC T z) (C.expC T w))
originalBishopExpCAddFromNativeRealExpAndTrig
  T cosAdd sinAdd (C.complex x y) (C.complex a b) =
  let
    ex = Exp.bishopExp x
    ea = Exp.bishopExp a
    cy = Elementary.bishopCos (C.dataSet T) y
    cb = Elementary.bishopCos (C.dataSet T) b
    sy = Elementary.bishopSin (C.dataSet T) y
    sb = Elementary.bishopSin (C.dataSet T) b

    realRing :
      R._≃_
        (R._*_
          (R._*_ ex ea)
          (R._-_ (R._*_ cy cb) (R._*_ sy sb)))
        (R._-_
          (R._*_ (R._*_ ex cy) (R._*_ ea cb))
          (R._*_ (R._*_ ex sy) (R._*_ ea sb)))
    realRing =
      let open RP.ℝ-Solver in
      solve 6
        (λ e₁ e₂ c₁ c₂ s₁ s₂ →
          (e₁ ⊗ e₂) ⊗ ((c₁ ⊗ c₂) ⊖ (s₁ ⊗ s₂))
          ⊜
          ((e₁ ⊗ c₁) ⊗ (e₂ ⊗ c₂))
          ⊖ ((e₁ ⊗ s₁) ⊗ (e₂ ⊗ s₂)))
        RP.≃-refl ex ea cy cb sy sb

    imagRing :
      R._≃_
        (R._*_
          (R._*_ ex ea)
          (R._+_ (R._*_ sy cb) (R._*_ cy sb)))
        (R._+_
          (R._*_ (R._*_ ex cy) (R._*_ ea sb))
          (R._*_ (R._*_ ex sy) (R._*_ ea cb)))
    imagRing =
      let open RP.ℝ-Solver in
      solve 6
        (λ e₁ e₂ c₁ c₂ s₁ s₂ →
          (e₁ ⊗ e₂) ⊗ ((s₁ ⊗ c₂) ⊕ (c₁ ⊗ s₂))
          ⊜
          ((e₁ ⊗ c₁) ⊗ (e₂ ⊗ s₂))
          ⊕ ((e₁ ⊗ s₁) ⊗ (e₂ ⊗ c₂)))
        RP.≃-refl ex ea cy cb sy sb
  in
  C.complex-equivalent
    (RP.≃-trans
      (RP.*-cong (RealExp.bishopExpAdd x a) (cosAdd y b))
      realRing)
    (RP.≃-trans
      (RP.*-cong (RealExp.bishopExpAdd x a) (sinAdd y b))
      imagRing)

-- EXACT P2 source-consumer type: the source-selected Bishop complex
-- exponential in the original Riemann carrier, not merely an analogous
-- Cartesian exponential. The conversion is definitionally literal on pairs.
originalBishopAnalyticExpAddFromNativeRealExpAndTrig :
  (T : C.BishopSetoidComplexTranscendentals) →
  OriginalCosineAddition T →
  OriginalSineAddition T →
  Dyadic.OriginalBishopAnalyticExpAddLaw T
originalBishopAnalyticExpAddFromNativeRealExpAndTrig
  T cosAdd sinAdd
  (A.bishop-complex x y) (A.bishop-complex a b) =
  let
    equality =
      originalBishopExpCAddFromNativeRealExpAndTrig
        T cosAdd sinAdd
        (C.complex x y) (C.complex a b)
  in
  C.reEquivalent equality , C.imEquivalent equality
