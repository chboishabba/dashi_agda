module DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact where

-- Source-written, kernel pending. Original Machin pi and literal
-- positive-Nat reciprocal sums. No opaque zeta authority.
-- RH donor: exact unsigned/even pair regrouping on literal prefixes.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Nat.Base using (z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRec
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryTermsExact as H
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryClosureExact as Close
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryFourierExact as F
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; powC)
open Comp using (complexTrans; complexSym)
open Completion using (realConverges)

r : Nat → ℝ
r k = Basel.embed (NatRec.reciprocalNatRational k)

double : Nat → Nat
double zero = zero
double (suc k) = suc (suc (double k))

doubleRead : ∀ k → N.natReal (double k) ≃ D.two * N.natReal k
doubleRead zero = let open P.ℝ-Solver in
  solve 0 (Κ 0ℚᵘ ⊜ Κ (+ 2 / 1) ⊗ Κ 0ℚᵘ) P.≃-refl
doubleRead (suc k) =
  P.≃-trans (N.natRealSuccessor (suc (double k)))
    (P.≃-trans (P.+-cong (N.natRealSuccessor (double k)) P.≃-refl)
      (P.≃-trans (P.+-cong (P.+-cong (doubleRead k) P.≃-refl) P.≃-refl)
        (P.≃-trans
          (let open P.ℝ-Solver in solve 1
            (λ k → (Κ (+ 2 / 1) ⊗ k ⊕ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ
              ⊜ Κ (+ 2 / 1) ⊗ (k ⊕ Κ 1ℚᵘ)) P.≃-refl (N.natReal k))
          (P.*-congˡ (P.≃-symm (N.natRealSuccessor k))))))

inverseUnique : ∀ a b d → (a * d) ≃ R.1ℝ → (b * d) ≃ R.1ℝ → a ≃ b
inverseUnique a b d ha hb =
  P.≃-trans (P.≃-symm (P.*-identityʳ a))
    (P.≃-trans (P.*-congˡ (P.≃-symm hb))
      (P.≃-trans
        (let open P.ℝ-Solver in solve 3
          (λ a b d → a ⊗ (b ⊗ d) ⊜ b ⊗ (a ⊗ d)) P.≃-refl a b d)
        (P.≃-trans (P.*-congˡ ha) (P.*-identityʳ b))))

evenRecip : ∀ k → r (suc (double k)) ≃ D.half * r k
evenRecip k = inverseUnique _ _ (N.natReal (double (suc k)))
  (NatRec.embeddedReciprocalNatCancels (suc (double k)))
  (P.≃-trans (P.*-congˡ (doubleRead (suc k)))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 2
        (λ r j → (Κ (+ 1 / 2) ⊗ r) ⊗ (Κ (+ 2 / 1) ⊗ j) ⊜ r ⊗ j)
        P.≃-refl (r k) (N.natReal (suc k)))
      (NatRec.embeddedReciprocalNatCancels k)))

oddMag : ∀ k → N.natReal (suc (double k)) ≃ D.two * H.mag k
oddMag k = P.≃-trans (N.natRealSuccessor (double k))
  (P.≃-trans (P.+-cong (doubleRead k) P.≃-refl)
    (let open P.ℝ-Solver in solve 1
      (λ k → Κ (+ 2 / 1) ⊗ k ⊕ Κ 1ℚᵘ ⊜ Κ (+ 2 / 1) ⊗ (k ⊕ Κ (+ 1 / 2)))
      P.≃-refl (N.natReal k)))

oddCancel : ∀ k → (H.mag k * (D.two * r (double k))) ≃ R.1ℝ
oddCancel k = P.≃-trans
  (let open P.ℝ-Solver in solve 2
    (λ a r → a ⊗ (Κ (+ 2 / 1) ⊗ r) ⊜ r ⊗ (Κ (+ 2 / 1) ⊗ a))
    P.≃-refl (H.mag k) (r (double k)))
  (P.≃-trans (P.*-congˡ (P.≃-symm (oddMag k))) (NatRec.embeddedReciprocalNatCancels (double k)))

realC : ℝ → BishopComplex
realC a = C.complex a R.0ℝ

realMul : ∀ a b → (realC a *C realC b) ≈C realC (a * b)
realMul a b =
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊗ b ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ a ⊗ b) P.≃-refl a b) ,
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ b ⊜ Κ 0ℚᵘ) P.≃-refl a b)

realCong : ∀ {a b} → a ≃ b → realC a ≈C realC b
realCong h = h , P.≃-refl

axisPlus : ∀ k → H.w H.plus k R.0ℝ ≈C realC (D.two * r (double k))
axisPlus k = G.reciprocalUnique _ _ _ (complexTrans (realMul _ _) (realCong (oddCancel k)))

axisMinus : ∀ k → H.w H.minus k R.0ℝ ≈C realC (R.- (D.two * r (double k)))
axisMinus k = G.reciprocalUnique _ _ _ (complexTrans (realMul _ _)
  (realCong (P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ a r → (⊝ a) ⊗ (⊝ r) ⊜ a ⊗ r) P.≃-refl (H.mag k) (D.two * r (double k)))
    (oddCancel k))))

realPow : ∀ a n → powC (realC a) n ≈C realC (R.pow a n)
realPow a zero = C.≈C-refl _
realPow a (suc n) = complexTrans (A.mulCCongruent (C.≈C-refl _) (realPow a n))
  (complexTrans (realMul a (R.pow a n)) (realCong (P.*-comm a (R.pow a n))))

powCong : ∀ {a b} → a ≃ b → ∀ n → R.pow a n ≃ R.pow b n
powCong h zero = P.≃-refl
powCong h (suc n) = P.*-cong (powCong h n) h

powProd : ∀ a b n → R.pow (a * b) n ≃ (R.pow a n * R.pow b n)
powProd a b zero = P.≃-symm (P.*-identityʳ R.1ℝ)
powProd a b (suc n) = P.≃-trans (P.*-congʳ (powProd a b n))
  (let open P.ℝ-Solver in solve 4
    (λ x y a b → (x ⊗ y) ⊗ (a ⊗ b) ⊜ (x ⊗ a) ⊗ (y ⊗ b)) P.≃-refl (R.pow a n) (R.pow b n) a b)

term : Nat → Nat → ℝ
term w k = R.pow (r k) w

positive : ∀ w k → R.NonNegative (term w k)
positive w k = Seq.nonNegx⇒nonNegxⁿ w (NatRec.reciprocalNonnegative k)

squareRead : ∀ k → term 2 k ≃ Basel.baselTerm k
squareRead k =
  P.≃-trans
    (let open P.ℝ-Solver in solve 1
      (λ r → (Κ 1ℚᵘ ⊗ r) ⊗ r ⊜ r ⊗ r) P.≃-refl (r k))
    (P.≃-trans (P.≃-symm (P.⋆-distrib-* (NatRec.reciprocalNatRational k) (NatRec.reciprocalNatRational k)))
      (P.⋆-cong (NatRec.reciprocalNatSquareIsBaselRational k)))

zetaConvergent : ∀ extra → Seq._isConvergent (Seq.SeriesOf (term (suc (suc extra))))
zetaConvergent extra = Seq.proposition-3-5 Basel.baselSeriesConvergent
  (0 , λ k _ → P.≤-respˡ-≃ (P.nonNegx⇒∣x∣≃x (positive (suc (suc extra)) k))
    (P.≤-respʳ-≃ (squareRead k) (NatRec.reciprocalExtraPowersBelowSquare k extra)))

zeta : Nat → ℝ
zeta extra = Seq.lim (zetaConvergent extra)

prefixScale : ∀ c f n → Seq.SeriesOf (λ k → c * f k) n ≃ c * Seq.SeriesOf f n
prefixScale c f zero = P.≃-symm (let open P.ℝ-Solver in solve 1 (λ c → c ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl c)
prefixScale c f (suc n) = P.≃-trans (P.+-cong (prefixScale c f n) P.≃-refl)
  (let open P.ℝ-Solver in solve 3 (λ c a b → c ⊗ a ⊕ c ⊗ b ⊜ c ⊗ (a ⊕ b))
    P.≃-refl c (Seq.SeriesOf f n) (f n))

prefixCong : ∀ f g → (∀ k → f k ≃ g k) → ∀ n → Seq.SeriesOf f n ≃ Seq.SeriesOf g n
prefixCong f g h zero = P.≃-refl
prefixCong f g h (suc n) = P.+-cong (prefixCong f g h n) (h n)

oddPrefix : Nat → Nat → ℝ
oddPrefix w = Seq.SeriesOf (λ k → term w (double k))

evenPrefix : Nat → Nat → ℝ
evenPrefix w = Seq.SeriesOf (λ k → term w (suc (double k)))

-- Same finite pairing discipline as the original RH eta/zeta source.
pairRead : ∀ w n → Seq.SeriesOf (term w) (double n) ≃ (oddPrefix w n + evenPrefix w n)
pairRead w zero = P.≃-symm (P.+-identityʳ R.0ℝ)
pairRead w (suc n) =
  P.≃-trans (P.+-cong (P.+-cong (pairRead w n) P.≃-refl) P.≃-refl)
    (let open P.ℝ-Solver in solve 4
      (λ a b c d → (a ⊕ b) ⊕ c ⊕ d ⊜ (a ⊕ c) ⊕ (b ⊕ d)) P.≃-refl
      (oddPrefix w n) (evenPrefix w n) (term w (double n)) (term w (suc (double n))))

evenRead : ∀ w n → evenPrefix w n ≃ R.pow D.half w * Seq.SeriesOf (term w) n
evenRead w n = P.≃-trans
  (prefixCong _ _ (λ k → P.≃-trans (powCong (evenRecip k) w) (powProd D.half (r k) w)) n)
  (prefixScale (R.pow D.half w) (term w) n)

evenSubsequence : ∀ extra → Seq._ConvergesTo_ (λ n → Seq.SeriesOf (term (suc (suc extra))) (double n)) (zeta extra)
evenSubsequence extra = Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
  (Seq.subseq* (double , (λ n → P.≃-refl) , (λ n → NatP.<-trans (NatP.n<1+n (double n)) (NatP.n<1+n (suc (double n))))))
  (zetaConvergent extra)

oddRead : ∀ w n → oddPrefix w n ≃
  (Seq.SeriesOf (term w) (double n) - R.pow D.half w * Seq.SeriesOf (term w) n)
oddRead w n =
  P.≃-symm (P.≃-trans
    (P.+-cong (pairRead w n) (P.-‿cong (P.≃-symm (evenRead w n))))
    (let open P.ℝ-Solver in solve 2 (λ a b → (a ⊕ b) ⊖ b ⊜ a) P.≃-refl (oddPrefix w n) (evenPrefix w n)))

oddConv : ∀ extra → Seq._ConvergesTo_ (oddPrefix (suc (suc extra)))
  (zeta extra - R.pow D.half (suc (suc extra)) * zeta extra)
oddConv extra = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-symm (oddRead (suc (suc extra)) (suc n))})
  (_ , Inv.subR (evenSubsequence extra)
    (Inv.mulR (Power.constantConverges (R.pow D.half (suc (suc extra)))) (proj₂ (zetaConvergent extra))))

axis4Read : ∀ j → C.re (Close.axis 4 j) ≃ ((+ 32 / 1) ⋆) * term 4 (double j)
axis4Read j =
  P.≃-trans (proj₁ (A.addCCongruent
    (complexTrans (A.powCCongruent (axisPlus j) 4) (realPow _ 4))
    (complexTrans (A.powCCongruent (axisMinus j) 4) (realPow _ 4))))
    (let open P.ℝ-Solver in solve 1
      (λ r → ((((Κ 1ℚᵘ ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊕ ((((Κ 1ℚᵘ ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r)))
        ⊜ Κ (+ 32 / 1) ⊗ ((((Κ 1ℚᵘ ⊗ r) ⊗ r) ⊗ r) ⊗ r)) P.≃-refl (r (double j)))

axis4Prefix : ∀ n → C.re (Close.partial (Close.axis 4) n) ≃ ((+ 32 / 1) ⋆) * oddPrefix 4 n
axis4Prefix n = P.≃-trans (prefixCong _ _ axis4Read n)
  (prefixScale ((+ 32 / 1) ⋆) (λ k → term 4 (double k)) n)

axis6Read : ∀ j → C.re (Close.axis 6 j) ≃ ((+ 128 / 1) ⋆) * term 6 (double j)
axis6Read j =
  P.≃-trans (proj₁ (A.addCCongruent
    (complexTrans (A.powCCongruent (axisPlus j) 6) (realPow _ 6))
    (complexTrans (A.powCCongruent (axisMinus j) 6) (realPow _ 6))))
    (let open P.ℝ-Solver in solve 1
      (λ r → ((((((Κ 1ℚᵘ ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊗ (Κ (+ 2 / 1) ⊗ r)) ⊕ ((((((Κ 1ℚᵘ ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r))) ⊗ (⊝ (Κ (+ 2 / 1) ⊗ r)))
        ⊜ Κ (+ 128 / 1) ⊗ ((((((Κ 1ℚᵘ ⊗ r) ⊗ r) ⊗ r) ⊗ r) ⊗ r) ⊗ r)) P.≃-refl (r (double j)))

axis6Prefix : ∀ n → C.re (Close.partial (Close.axis 6) n) ≃ ((+ 128 / 1) ⋆) * oddPrefix 6 n
axis6Prefix n = P.≃-trans (prefixCong _ _ axis6Read n)
  (prefixScale ((+ 128 / 1) ⋆) (λ k → term 6 (double k)) n)

module At (inputs : Round11.BishopCutset) where
  module Hf = Close.At inputs

  axisLimit4 : Seq._ConvergesTo_ (λ n → ((+ 32 / 1) ⋆) * oddPrefix 4 n) (C.re Hf.target4)
  axisLimit4 = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → axis4Prefix (suc n)}) (_ , realConverges Hf.actualAxis4)

  targetRead4 : C.re Hf.target4 ≃ ((+ 30 / 90) ⋆) * R.pow D.pi 4
  targetRead4 =
    let open P.ℝ-Solver in solve 1
      (λ p → ((Κ (+ 1 / 6) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))))) ⊗ ((⊝ Κ (+ 1 / 4)) ⊕ (Κ (+ 6 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ (⊝ Κ (+ 1 / 4)) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 1 / 6) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))))) ⊗ (Κ 0ℚᵘ ⊕ (Κ (+ 6 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ (⊝ Κ (+ 1 / 4)))))) ⊜ Κ (+ 30 / 90) ⊗ ((((Κ 1ℚᵘ ⊗ p) ⊗ p) ⊗ p) ⊗ p)) P.≃-refl D.pi

  zetaFactor4 : ((+ 30 / 1) ⋆) * zeta 2 ≃ C.re Hf.target4
  zetaFactor4 =
    P.≃-trans
      (let open P.ℝ-Solver in solve 1
        (λ z → Κ (+ 30 / 1) ⊗ z ⊜ Κ (+ 32 / 1) ⊗ (z ⊖ ((((Κ 1ℚᵘ ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ z))
        P.≃-refl (zeta 2))
      (Seq.uniqueness-of-limits (Inv.mulR (Power.constantConverges ((+ 32 / 1) ⋆)) (oddConv 2)) axisLimit4)

  zeta4 : zeta 2 ≃ ((+ 1 / 90) ⋆) * R.pow D.pi 4
  zeta4 =
    let law = P.≃-trans zetaFactor4 targetRead4
    in P.≃-trans
      (let open P.ℝ-Solver in solve 1 (λ z → z ⊜ Κ (+ 1 / 30) ⊗ (Κ (+ 30 / 1) ⊗ z)) P.≃-refl (zeta 2))
      (P.≃-trans (P.*-congˡ law)
        (let open P.ℝ-Solver in solve 1
          (λ p → Κ (+ 1 / 30) ⊗ (Κ (+ 30 / 90) ⊗ p) ⊜ Κ (+ 1 / 90) ⊗ p)
          P.≃-refl (R.pow D.pi 4)))

  axisLimit6 : Seq._ConvergesTo_ (λ n → ((+ 128 / 1) ⋆) * oddPrefix 6 n) (C.re Hf.target6)
  axisLimit6 = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → axis6Prefix (suc n)}) (_ , realConverges Hf.actualAxis6)

  targetRead6 : C.re Hf.target6 ≃ ((+ 126 / 945) ⋆) * R.pow D.pi 6
  targetRead6 =
    let open P.ℝ-Solver in solve 1
      (λ p → ((Κ (+ 1 / 120) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))))))) ⊗ (((⊝ Κ (+ 1 / 4)) ⊕ (Κ (+ 30 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ (⊝ Κ (+ 1 / 4)) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))) ⊕ (Κ (+ 120 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ (⊝ Κ (+ 1 / 4)) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ) ⊖ Κ 0ℚᵘ ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ (⊝ Κ (+ 1 / 4)))))) ⊖ (Κ (+ 1 / 120) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)))) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ)) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ))) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ)) ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 1ℚᵘ) ⊕ (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ 0ℚᵘ ⊗ Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ))))))) ⊗ ((Κ 0ℚᵘ ⊕ (Κ (+ 30 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ (⊝ Κ (+ 1 / 4))))) ⊕ (Κ (+ 120 / 1) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ (⊝ Κ (+ 1 / 4))) ⊕ Κ 0ℚᵘ ⊗ ((⊝ Κ (+ 1 / 4)) ⊗ (⊝ Κ (+ 1 / 4)) ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))))) ⊜ Κ (+ 126 / 945) ⊗ ((((((Κ 1ℚᵘ ⊗ p) ⊗ p) ⊗ p) ⊗ p) ⊗ p) ⊗ p)) P.≃-refl D.pi

  zetaFactor6 : ((+ 126 / 1) ⋆) * zeta 4 ≃ C.re Hf.target6
  zetaFactor6 =
    P.≃-trans
      (let open P.ℝ-Solver in solve 1
        (λ z → Κ (+ 126 / 1) ⊗ z ⊜ Κ (+ 128 / 1) ⊗ (z ⊖ ((((((Κ 1ℚᵘ ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ Κ (+ 1 / 2)) ⊗ z))
        P.≃-refl (zeta 4))
      (Seq.uniqueness-of-limits (Inv.mulR (Power.constantConverges ((+ 128 / 1) ⋆)) (oddConv 4)) axisLimit6)

  zeta6 : zeta 4 ≃ ((+ 1 / 945) ⋆) * R.pow D.pi 6
  zeta6 =
    let law = P.≃-trans zetaFactor6 targetRead6
    in P.≃-trans
      (let open P.ℝ-Solver in solve 1 (λ z → z ⊜ Κ (+ 1 / 126) ⊗ (Κ (+ 126 / 1) ⊗ z)) P.≃-refl (zeta 4))
      (P.≃-trans (P.*-congˡ law)
        (let open P.ℝ-Solver in solve 1
          (λ p → Κ (+ 1 / 126) ⊗ (Κ (+ 126 / 945) ⊗ p) ⊜ Κ (+ 1 / 945) ⊗ p)
          P.≃-refl (R.pow D.pi 6)))
