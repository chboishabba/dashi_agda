module DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact where

-- SOURCE-WRITTEN, UNCOMPILED. Evaluate the already-proved literal
-- square and cleared jet at the ORIGINAL selected real CM coordinate.
-- Explicit remaining inputs are series/majorant witnesses and actual
-- same-object coordinate bindings, not square or derivative identities.
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_)
import Real as R
open R using (ℝ; _≃_; _*_; _⋆)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as W
import DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact as A
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as Euler
import DASHI.Foundations.BishopChudnovskyNativeHyperODEExact as Hyper
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as End
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalHyperClearedODEExact as Proof
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as EV
import DASHI.Moonshine.JInvariantBishopFiniteCompositionExchangeExact as EX
import DASHI.Moonshine.JInvariantBishopCompositionLimitExact as CL
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as Literal
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as Period
import DASHI.Foundations.BishopChudnovskyNativeRealExact as Native
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
open U using (Series; _⊗s_; scale)

q : ℝ
q = R.- CM.radius

weightedCong : (f g : Series) → (∀ n → f n ≃ g n) →
  ∀ n → EV.weighted q f n ≃ EV.weighted q g n
weightedCong f g h n = P.*-congˡ (h n)

Eval : Series → ℝ → Set
Eval f x = S._ConvergesTo_ (S.SeriesOf (EV.weighted q f)) x

Abs : Series → Set
Abs f = S.SeriesOf_ConvergesAbsolutely (EV.weighted q f)

scaleWeighted : (a : ℝ) (f : Series) (n : Nat) →
  EV.weighted q (scale a f) n ≃ a * EV.weighted q f n
scaleWeighted a f n = let open P.ℝ-Solver in
  solve 3 (λ r a f → r ⊗ (a ⊗ f) ⊜ a ⊗ (r ⊗ f))
    P.≃-refl (R.pow q n) a (f n)

scaleEval : (a : ℝ) (f : Series) (x : ℝ) → Eval f x → Eval (scale a f) (a * x)
scaleEval a f x hx =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → P.≃-trans (EX.scaleSum a (EV.weighted q f) n)
      (Ext.seriesPartialSumsCongruent (λ k → P.≃-symm (scaleWeighted a f k)) n))
    (a * x , S.xₙyₙ→x₀y₀ (a , S.xₙ≃c⇒xₙ→c (λ n → P.≃-refl)) (x , hx))

sameEval : (f g : Series) (x y : ℝ) →
  (∀ n → f n ≃ g n) → Eval f x → Eval g y → x ≃ y
sameEval f g x y h =
  Ext.termwiseEquivalentSeriesHaveEquivalentLimits (weightedCong f g h)

module AtOriginalZ
  (zAbs : Abs H.Zcoord)
  (zEval : Eval H.Zcoord Hyper.z) where

  module HA = CL.At q H.hyperCoeff H.Zcoord H.zCoordZero zAbs
  module JA = CL.At q H.hyperJetCoeff H.Zcoord H.zCoordZero zAbs
  module HS = HA.Signed Hyper.z zEval
  module JS = JA.Signed Hyper.z zEval

  -- The two outer readouts are the SAME signed factorial histories
  -- used by the original Chudnovsky native period.
  originalH : S._ConvergesTo_ (S.SeriesOf HS.l) Euler.H
  originalH = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → Ext.seriesPartialSumsCongruent (λ k → P.≃-symm (H.hyperCoeffAtCM k)) n)
    (Euler.H , Euler.hConverges)

  originalJ : S._ConvergesTo_ (S.SeriesOf JS.l) Euler.J₁
  originalJ = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → Ext.seriesPartialSumsCongruent (λ k → P.≃-symm (H.hyperJetCoeffAtCM k)) n)
    (Euler.J₁ , Euler.jConverges)

  module WithMajorants
    (hm : S._isConvergent (S.SeriesOf HA.m))
    (jm : S._isConvergent (S.SeriesOf JA.m)) where

    hAbs : Abs H.hyperCandidate
    hAbs = HA.compositionAbsolute hm

    jAbs : Abs H.hyperJetCandidate
    jAbs = JA.compositionAbsolute jm

    hEval : Eval H.hyperCandidate Euler.H
    hEval = HS.compositionLimit hm Euler.H originalH

    jEval : Eval H.hyperJetCandidate Euler.J₁
    jEval = JS.compositionLimit jm Euler.J₁ originalJ

    actualSquare : F.RamanujanX → F.RamanujanY → F.RamanujanE →
      Eval U.X End.X → End.HyperSquare
    actualSquare hx hy he xEval =
      sameEval (H.hyperCandidate ⊗s H.hyperCandidate) U.X
        (Euler.H * Euler.H) End.X (Proof.hyperSquare hx hy he)
        (EV.weightedProductLimit q H.hyperCandidate H.hyperCandidate
          Euler.H Euler.H hAbs hAbs hEval hEval) xEval

    -- Use the literal 3DX stream at the endpoint, whose evaluation
    -- must be bound to the existing original E4 jet End.U.
    uSeries : Series
    uSeries = scale ((+ 3 / 1) ⋆) (U.D 1 U.X)

    actualClearedJet : F.RamanujanX → F.RamanujanY → F.RamanujanE →
      Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U →
      End.ClearedHyperJet
    actualClearedJet hx hy he xa ya ua xv yv uv =
      let
        hyAbs = EV.weightedProductAbsolute q H.hyperCandidate U.Y hAbs ya
        hyEval = EV.weightedProductLimit q H.hyperCandidate U.Y
          Euler.H End.Y hAbs ya hEval yv
        hyjEval = EV.weightedProductLimit q (H.hyperCandidate ⊗s U.Y) H.hyperJetCandidate
          (Euler.H * End.Y) Euler.J₁ hyAbs jAbs hyEval jEval
        left = scale ((+ 6 / 1) ⋆) (H.hyperCandidate ⊗s U.Y ⊗s H.hyperJetCandidate)
        right = U.X ⊗s uSeries
        eq = λ n → P.≃-trans (Proof.hyperClearedJet hx hy he n)
          (P.≃-symm (W.rowScaleRight ((+ 3 / 1) ⋆) U.X (U.D 1 U.X) n))
        h = sameEval left right
          (((+ 6 / 1) ⋆) * ((Euler.H * End.Y) * Euler.J₁)) (End.X * End.U)
          eq (scaleEval ((+ 6 / 1) ⋆) (H.hyperCandidate ⊗s U.Y ⊗s H.hyperJetCandidate)
            ((Euler.H * End.Y) * Euler.J₁) hyjEval)
          (EV.weightedProductLimit q U.X uSeries End.X End.U xa ua xv uv)
      in P.≃-trans (let open P.ℝ-Solver in
        solve 3 (λ h y j → Κ (+ 6 / 1) ⊗ h ⊗ y ⊗ j ⊜ Κ (+ 6 / 1) ⊗ ((h ⊗ y) ⊗ j))
          P.≃-refl Euler.H End.Y Euler.J₁) h

    -- The existing terminal owner is used without a new period theorem.
    actualRaw : F.RamanujanX → F.RamanujanY → F.RamanujanE →
      Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U →
      End.CMRoot → End.SignedJet → (k : Nat) → Raw.RawCross k
    actualRaw hx hy he xa ya ua xv yv uv root jet =
      End.rawFromThree root (actualSquare hx hy he xv)
        (actualClearedJet hx hy he xa ya ua xv yv uv) jet

    -- The original all-index Ramanujan producers already exist. Discharge
    -- those arguments here, not via a new external coefficient receipt.
    -- Remaining inputs are actual weighted evaluation and signed CM geometry.
    originalSquare : Eval U.X End.X → End.HyperSquare
    originalSquare = actualSquare Literal.ramanujanX Literal.ramanujanY Literal.ramanujanE

    originalClearedJet : Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U → End.ClearedHyperJet
    originalClearedJet = actualClearedJet Literal.ramanujanX Literal.ramanujanY Literal.ramanujanE

    originalPeriod : Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U →
      End.CMRoot → End.SignedJet → Period.NativePeriod
    originalPeriod xa ya ua xv yv uv root jet =
      End.periodFromThree root (originalSquare xv)
        (originalClearedJet xa ya ua xv yv uv) jet

    originalSameReal : Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U →
      End.CMRoot → End.SignedJet → Native.chudnovskyReal ≃ Machin.bishopMachinPi
    originalSameReal xa ya ua xv yv uv root jet =
      Period.periodToSameReal (originalPeriod xa ya ua xv yv uv root jet)

    originalRaw : Abs U.X → Abs U.Y → Abs uSeries →
      Eval U.X End.X → Eval U.Y End.Y → Eval uSeries End.U →
      End.CMRoot → End.SignedJet → (k : Nat) → Raw.RawCross k
    originalRaw = actualRaw Literal.ramanujanX Literal.ramanujanY Literal.ramanujanE
