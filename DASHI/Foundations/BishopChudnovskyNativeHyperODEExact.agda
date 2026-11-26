module DASHI.Foundations.BishopChudnovskyNativeHyperODEExact where

-- SOURCE-WRITTEN, UNCOMPILED. Literal signed CM factorial recurrence
-- and all Euler orders on the existing Bishop carrier. Classical
-- hypergeometric ODE, reused from Paper9HypergeometricSeriesODE.lean;
-- no claim of the composed E4 identity yet.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_,_; proj₂)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Relation.Binary.PropositionalEquality using (sym; cong; trans)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _⋆)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as Raw
import DASHI.Foundations.BishopChudnovskyFactorialSourceExact as F
import DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact as A
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as E
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Norm
import DASHI.Foundations.BishopChudnovskyWidthSourceExact as Width
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopNatEmbeddingPowerExact as NPow
import DASHI.Moonshine.JInvariantBishopPolynomialGeometricRatioExact as NAdd
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as Maj
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Analysis.BishopMachinSignedFiniteHistoryExact as Scale

zQ : Q.ℚᵘ
zQ = (Z.-_ (+ 1728)) / 262537412640768000

z : ℝ
z = zQ ⋆

-- The original factorial stream already has the signed leaf ratio.
termStep : (n : Nat) → F.factorialTerm (suc n) Q.≃
  (F.factorialTerm n Q.* Raw.leafRatio (suc n))
termStep n = QP.≃-trans (QP.≃-sym (F.productFactorial (suc n)))
  (QP.≃-trans (Raw.rawProductStep (suc n))
    (QP.*-cong (F.productFactorial n) QP.≃-refl))

-- Exact denominator clearing on unnormalised rationals, including
-- zero or negative numerator. No field inversion of a signed value.
clearFraction : (a : Z.ℤ) (d : Nat) (nd : Nat.NonZero d) →
  ((+ d / 1) Q.* Raw.frac a d nd) Q.≃ (a / 1)
clearFraction a d nd =
  QP.≃-trans
    (QP.≃-sym (Raw.fracMulEdge (+ d) a 1 d Nat.nonZero nd))
    (QP.≃-trans sameDen
      (QP.*-cancelˡ-/ d {q = a} {r = 1}
        {{Nat.nonZero}} {{Raw.prodNZ d 1 nd Nat.nonZero}}))
  where
  sameDen :
    Raw.frac (Z._*_ (+ d) a) (Nat._*_ 1 d)
      (Raw.prodNZ 1 d Nat.nonZero nd) Q.≃
    Raw.frac (Z._*_ (+ d) a) (Nat._*_ d 1)
      (Raw.prodNZ d 1 nd Nat.nonZero)
  sameDen rewrite NP.*-identityˡ d | NP.*-identityʳ d = QP.≃-refl

leafCleared : (n : Nat) →
  (NR.natReal (G.qNat (suc n)) * (Raw.leafRatio (suc n) ⋆)) ≃
    ((CH.sourceP (suc n) / 1) ⋆)
leafCleared n =
  P.≃-trans (P.≃-symm (P.⋆-distrib-* (+ (G.qNat (suc n)) / 1)
    (Raw.leafRatio (suc n))))
    (P.⋆-cong (clearFraction (CH.sourceP (suc n))
      (G.qNat (suc n)) (G.qNatNonZero (suc n))))

sourceEdge : (n : Nat) →
  (NR.natReal (G.qNat (suc n)) * A.hTerm (suc n)) ≃
    (((CH.sourceP (suc n) / 1) ⋆) * A.hTerm n)
sourceEdge n =
  P.≃-trans
    (P.*-congˡ (P.≃-trans (P.⋆-cong (termStep n))
      (P.⋆-distrib-* (F.factorialTerm n) (Raw.leafRatio (suc n)))))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3 (λ q h l →
        q ⊗ (h ⊗ l) ⊜ (q ⊗ l) ⊗ h)
        P.≃-refl (NR.natReal (G.qNat (suc n))) (A.hTerm n)
        (Raw.leafRatio (suc n) ⋆))
      (P.*-congʳ (leafCleared n)))

-- Polynomial source shape, using the original Nat embedding owner.
lin : (a b n : Nat) →
  NR.natReal (Nat._+_ (Nat._*_ a n) b) ≃
    (NR.natReal a * NR.natReal n + NR.natReal b)
lin a b n = P.≃-trans (NAdd.natRealAdd (Nat._*_ a n) b)
  (P.+-cong (NR.natRealMul a n) P.≃-refl)

leafMagnitudeShape : (n : Nat) →
  NR.natReal (G.leafMagnitude n) ≃
    (((+ 24 / 1) ⋆) * (((+ 2 / 1) ⋆) * NR.natReal n + R.1ℝ) *
      (((+ 6 / 1) ⋆) * NR.natReal n + R.1ℝ) *
      (((+ 6 / 1) ⋆) * NR.natReal n + ((+ 5 / 1) ⋆)))
leafMagnitudeShape n =
  P.≃-trans (NR.natRealMul _ _)
    (P.*-cong
      (P.≃-trans (NR.natRealMul _ _)
        (P.*-cong
          (P.≃-trans (NR.natRealMul 24 _) (P.*-congˡ (lin 2 1 n)))
          (lin 6 1 n)))
      (lin 6 5 n))

negativeEmbedding : (n : Nat) →
  ((Z.-_ (+ n) / 1) ⋆) ≃ R.- (NR.natReal n)
negativeEmbedding n = P.⋆-distrib-neg (+ n / 1)

sourcePShape : (n : Nat) →
  ((CH.sourceP (suc n) / 1) ⋆) ≃
  R.- (((+ 24 / 1) ⋆) *
    (((+ 2 / 1) ⋆) * NR.natReal n + R.1ℝ) *
    (((+ 6 / 1) ⋆) * NR.natReal n + R.1ℝ) *
    (((+ 6 / 1) ⋆) * NR.natReal n + ((+ 5 / 1) ⋆)))
sourcePShape n = P.≃-trans (negativeEmbedding (G.leafMagnitude n))
  (P.-‿cong (leafMagnitudeShape n))

-- All d, including the zero mode 0^0=1. Order zero and one
-- are identified with the already-owned H and J₁ below.
jetTerm : Nat → Nat → ℝ
jetTerm d n = R.pow (NR.natReal n) d * A.hTerm n

jetZero : (n : Nat) → jetTerm zero n ≃ A.hTerm n
jetZero n = P.*-identityˡ (A.hTerm n)

jetOne : (n : Nat) → jetTerm 1 n ≃ A.jTerm n
jetOne n = P.≃-trans
  (P.*-congʳ (P.*-identityˡ (NR.natReal n)))
  (P.≃-symm (P.⋆-distrib-* (+ n / 1) (F.factorialTerm n)))

-- Build the degree-three jet from the actual source, not from
-- numerical estimates or a new normalization.
powThree : (n : Nat) → NR.natReal (n Nat.^ 3) ≃ R.pow (NR.natReal n) 3
powThree n = NPow.natRealPowNat n 3

qShape : (n : Nat) → NR.natReal (G.qNat (suc n)) ≃
  (((+ 262537412640768000 / 1) ⋆) * R.pow (NR.natReal (suc n)) 3)
qShape n = P.≃-trans (NR.natRealMul CH.C (suc n Nat.^ 3))
  (P.*-congˡ (powThree (suc n)))

-- The selected z=-1728/C retains its sign. Clearing C first
-- produces the hypergeometric recurrence directly from the leaf.
coefficientODE : (n : Nat) →
  jetTerm 3 (suc n) ≃
    (z * (jetTerm 3 n + ((+ 3 / 2) ⋆) * jetTerm 2 n +
      ((+ 23 / 36) ⋆) * jetTerm 1 n + ((+ 5 / 72) ⋆) * jetTerm zero n))
coefficientODE n =
  let
    x = NR.natReal n
    u = R.pow (NR.natReal (suc n)) 3
    h = A.hTerm n
    h′ = A.hTerm (suc n)
    c = (+ 262537412640768000 / 1) ⋆
    ci = (+ 1 / 262537412640768000) ⋆
    f = ((+ 24 / 1) ⋆) * (((+ 2 / 1) ⋆) * x + R.1ℝ) *
      (((+ 6 / 1) ⋆) * x + R.1ℝ) * (((+ 6 / 1) ⋆) * x + ((+ 5 / 1) ⋆))
    open P.ℝ-Solver
    eq : ((c * u) * h′) ≃ (R.- f * h)
    eq = P.≃-trans (P.*-congʳ (P.≃-symm (qShape n)))
      (P.≃-trans (sourceEdge n) (P.*-congʳ (sourcePShape n)))
  in P.≃-trans
    (solve 2 (λ u h′ → u ⊗ h′ ⊜
      Κ (+ 1 / 262537412640768000) ⊗
        ((Κ (+ 262537412640768000 / 1) ⊗ u) ⊗ h′))
      P.≃-refl u h′)
    (P.≃-trans (P.*-congˡ eq)
      (solve 2 (λ x h →
        Κ (+ 1 / 262537412640768000) ⊗
          ((⊝ (Κ (+ 24 / 1) ⊗ (Κ (+ 2 / 1) ⊗ x ⊕ Κ Q.1ℚᵘ) ⊗
            (Κ (+ 6 / 1) ⊗ x ⊕ Κ Q.1ℚᵘ) ⊗ (Κ (+ 6 / 1) ⊗ x ⊕ Κ (+ 5 / 1)))) ⊗ h)
        ⊜ Κ zQ ⊗
          (((((Κ Q.1ℚᵘ ⊗ x) ⊗ x) ⊗ x) ⊗ h) ⊕
            Κ (+ 3 / 2) ⊗ (((Κ Q.1ℚᵘ ⊗ x) ⊗ x) ⊗ h) ⊕
            Κ (+ 23 / 36) ⊗ ((Κ Q.1ℚᵘ ⊗ x) ⊗ h) ⊕
            Κ (+ 5 / 72) ⊗ (Κ Q.1ℚᵘ ⊗ h)))
        P.≃-refl x h))

ratioNN : R._≤_ R.0ℝ E.ratio
ratioNN = P.p≤q⇒p⋆≤q⋆ Q.0ℚᵘ E.ratioQ (QP.nonNegative⁻¹ E.ratioQ)

ratioSmall : R._<_ E.ratio R.1ℝ
ratioSmall = P.p<q⇒p⋆<q⋆ E.ratioQ Q.1ℚᵘ
  (Q.*<* (Z.+<+ (from-yes (2 NP.≤? Width.M))))

-- The same already-owned factorial absolute bound pays every fixed
-- Euler order: n^d (1/M)^n is summable by the generic Poly owner.
jetBound : (d n : Nat) → R._≤_ (R.∣ jetTerm d n ∣)
  (Poly.polynomialGeometricTerm E.ratio d n)
jetBound d n =
  P.≤-respʳ-≃ (P.*-congˡ (P.*-identityˡ (R.pow E.ratio n)))
    (Maj.scaledComponentAbsoluteBound
      (S.nonNegx⇒nonNegxⁿ d (Poly.natRealNonnegative n))
      (Poly.polynomialGeometricTermNonnegative ratioNN zero n)
      P.≤-refl (E.hBound n))

jetAbsolute : (d : Nat) → S.SeriesOf_ConvergesAbsolutely (jetTerm d)
jetAbsolute d = Maj.absoluteSeriesFromMajorant (jetTerm d)
  (Poly.polynomialGeometricTerm E.ratio d)
  (Poly.polynomialGeometricSeriesAbsolutelyConvergent E.ratio d ratioNN ratioSmall)
  (jetBound d)

jetCauchy : (d : Nat) → S._isConvergent (S.SeriesOf (jetTerm d))
jetCauchy d = S.absolute⇒isConvergent (jetAbsolute d)

J : Nat → ℝ
J d = S.lim (jetCauchy d)

jetConverges : (d : Nat) → S._ConvergesTo_ (S.SeriesOf (jetTerm d)) (J d)
jetConverges d = proj₂ (jetCauchy d)

J0 : J zero ≃ E.H
J0 = Ext.termwiseEquivalentSeriesHaveEquivalentLimits jetZero
  (jetConverges zero) E.hConverges

J1 : J 1 ≃ E.J₁
J1 = Ext.termwiseEquivalentSeriesHaveEquivalentLimits jetOne
  (jetConverges 1) E.jConverges

-- Remove only the true zero term of the positive-order jet.
thirdZero : jetTerm 3 zero ≃ R.0ℝ
thirdZero = let open P.ℝ-Solver in solve 1 (λ h →
  (((Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊗ Κ Q.0ℚᵘ) ⊗ Κ Q.0ℚᵘ) ⊗ h
    ⊜ Κ Q.0ℚᵘ) P.≃-refl (A.hTerm zero)

shiftPartial : (n : Nat) →
  S.SeriesOf (λ i → jetTerm 3 (suc i)) n ≃ S.SeriesOf (jetTerm 3) (suc n)
shiftPartial zero = P.≃-symm (P.≃-trans
  (P.+-cong P.≃-refl thirdZero) (P.+-identityʳ R.0ℝ))
shiftPartial (suc n) = P.+-cong (shiftPartial n) P.≃-refl

shiftConverges : S._ConvergesTo_ (S.SeriesOf (λ i → jetTerm 3 (suc i))) (J 3)
shiftConverges =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n → P.≃-symm (shiftPartial n))
    (J 3 , S.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
      (S.shift-is-subsequence (S.SeriesOf (jetTerm 3)) 1) (J 3 , jetConverges 3))

-- Finite sum additivity and limit transport, using the same
-- pinned Bishop product/sum convergence used by factorial attachment.
addPartial : (f g : Nat → ℝ) (n : Nat) →
  S.SeriesOf (λ i → f i + g i) n ≃ (S.SeriesOf f n + S.SeriesOf g n)
addPartial f g zero = P.≃-symm (P.+-identityʳ R.0ℝ)
addPartial f g (suc n) = P.≃-trans
  (P.+-cong (addPartial f g n) P.≃-refl)
  (let open P.ℝ-Solver in solve 4 (λ a b c d →
    (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
    P.≃-refl (S.SeriesOf f n) (S.SeriesOf g n) (f n) (g n))

addConverges : (f g : Nat → ℝ) (a b : ℝ) →
  S._ConvergesTo_ (S.SeriesOf f) a →
  S._ConvergesTo_ (S.SeriesOf g) b →
  S._ConvergesTo_ (S.SeriesOf (λ n → f n + g n)) (a + b)
addConverges f g a b hf hg =
  S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ n → P.≃-symm (addPartial f g n))
    (a + b , S.xₙ+yₙ→x₀+y₀ (a , hf) (b , hg))

rhsTerm : Nat → ℝ
rhsTerm n = jetTerm 3 n + ((+ 3 / 2) ⋆) * jetTerm 2 n +
  ((+ 23 / 36) ⋆) * jetTerm 1 n + ((+ 5 / 72) ⋆) * jetTerm zero n

rhsLimit : ℝ
rhsLimit = J 3 + ((+ 3 / 2) ⋆) * J 2 + ((+ 23 / 36) ⋆) * J 1 + ((+ 5 / 72) ⋆) * J zero

rhsConverges : S._ConvergesTo_ (S.SeriesOf rhsTerm) rhsLimit
rhsConverges = addConverges _ _ _ _
  (addConverges _ _ _ _
    (addConverges _ _ _ _ (jetConverges 3)
      (Scale.leftScaledSeriesConverges ((+ 3 / 2) ⋆) (jetTerm 2) (J 2) (jetConverges 2)))
    (Scale.leftScaledSeriesConverges ((+ 23 / 36) ⋆) (jetTerm 1) (J 1) (jetConverges 1)))
  (Scale.leftScaledSeriesConverges ((+ 5 / 72) ⋆) (jetTerm zero) (J zero) (jetConverges zero))

actualHyperODE : J 3 ≃ (z * rhsLimit)
actualHyperODE = Ext.termwiseEquivalentSeriesHaveEquivalentLimits coefficientODE
  shiftConverges (Scale.leftScaledSeriesConverges z rhsTerm rhsLimit rhsConverges)

-- This is the actual factorial-series ODE at the selected rational z.
-- HyperSquare still needs the original E4 coefficient/germ producer;
-- the ODE alone is not that identity.
