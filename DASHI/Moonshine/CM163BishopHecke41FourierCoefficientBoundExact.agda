module DASHI.Moonshine.CM163BishopHecke41FourierCoefficientBoundExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Exact finite Laurent projection + arbitrary-precision common tail
-- on a single actual height circle gives the weighted coefficient bound.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41DyadicFourierProjectionExact as Fourier
import DASHI.Moonshine.CM163BishopHecke41DyadicCircleBoundsExact as Circle
import DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact as Uniform
import DASHI.Moonshine.CM163BishopHecke41CuspContractionExact as Contract
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open Comp using (complexTrans; complexSym)
open Fourier using (Point; mean; meanCong)
open Uniform using (complexPrefix)
open Contract using (Box; boxCong; two)

approxBound : ∀ a b M e → ∣ a ∣ ≤ M → ∣ a - b ∣ ≤ e → ∣ b ∣ ≤ (M + e)
approxBound a b M e ha he =
  let eq = let open P.ℝ-Solver in solve 2
        (λ a b → a ⊕ (⊝ (a ⊖ b)) ⊜ b) P.≃-refl a b
  in P.≤-respˡ-≃ (P.∣-∣-cong eq)
    (P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ a (R.- (a - b)))
      (P.+-mono-≤ ha (P.≤-respˡ-≃ (P.≃-symm P.∣-x∣≃∣x∣) he)))

module At (inputs : Round11.BishopCutset) where
  module H = Circle.At inputs
  module F = H.F
  open H using (q; nz)

  other : ∀ f n j → (j ≡ n → ⊥) → F.selected f n j ≈C A.zeroC
  other f n j h with j NP.≟ n
  ... | yes e = ⊥-elim (h e)
  ... | no _ = C.≈C-refl _

  self : ∀ f n → F.selected f n n ≈C f n
  self f n with n NP.≟ n
  ... | yes _ = C.≈C-refl _
  ... | no h = ⊥-elim (h refl)

  before : ∀ f n m → m ≤ n → complexPrefix (F.selected f n) m ≈C A.zeroC
  before f n zero h = C.≈C-refl _
  before f n (suc m) h =
    complexTrans (A.addCCongruent (before f n m (NP.≤-trans (NP.n≤1+n m) h))
      (other f n m (λ { refl → NP.<-irrefl refl h })))
      (L.complexAddLeftIdentity _)

  atIndex : ∀ f n → complexPrefix (F.selected f n) (suc n) ≈C f n
  atIndex f n = complexTrans
    (A.addCCongruent (before f n n NP.≤-refl) (self f n))
    (L.complexAddLeftIdentity _)

  extra : ∀ f n d → complexPrefix (F.selected f n) (d + suc n) ≈C f n
  extra f n zero = atIndex f n
  extra f n (suc d) =
    complexTrans (A.addCCongruent (extra f n d)
      (other f n (d + suc n) (λ { refl → NP.<-irrefl refl (NP.m≤n+m (suc n) d) })))
      (L.complexAddRightIdentity _)

  module For (p0 : Point) (f : N.SeriesC) (ev : ∀ p → Eval.Eval (q p) f) where
    r = q p0
    module U = Uniform.Disk r (nz p0) f (ev p0)

    prefix : Nat → Fourier.Func
    prefix m p = complexPrefix (N.twist (q p) f) m

    weighted : Nat → Nat → Fourier.Func
    weighted n m p = H.weight p0 n p *C prefix m p

    termRead : ∀ n j p →
      (H.weight p0 n p *C N.twist (q p) f j) ≈C
      (N.twist r (λ _ → f j) n *C F.mono j n p)
    termRead n j p =
      let a = powC r n
          b = powC (F.iq p) n
          c = f j
          d = powC (q p) j
      in complexTrans (A.mulCCongruent (Gen.powProduct r (F.iq p) n) (C.≈C-refl _))
        (complexTrans (Gen.shuffle a b c d)
          (A.mulCCongruent (L.complexMultiplyCommutative a c) (L.complexMultiplyCommutative b d)))

    weightedRead : ∀ n m p → weighted n m p ≈C
      complexPrefix (λ j → (f j *C powC r n) *C F.mono j n p) m
    weightedRead n m p =
      complexTrans (complexSym (D.prefixMul (H.weight p0 n p) (N.twist (q p) f) m))
        (D.prefixCong _ _ (λ j → termRead n j p) m)

    extract : ∀ n d →
      let m = d + suc n
          k = m + n
      in mean k (weighted n m) (Circle.root k p0) ≈C N.twist r f n
    extract n d =
      let m = d + suc n
          k = m + n
          g j = f j *C powC r n
          root = Circle.root k p0
      in complexTrans (meanCong k (weightedRead n m) root)
        (complexTrans (F.prefixProjection k g n m (NP.m≤n+m n m)
          (NP.≤-step (NP.m≤m+n m n)) root) (extra g n d))

    -- Increase the cutoff past the selected mode BEFORE choosing depth.
    -- Every leaf gets the same modulus, not a point-dependent cutoff.
    approximate : ∀ M → (∀ p → Box M (Eval.value (ev p))) →
      ∀ n e → Box (two * (M + Basel.reciprocalSequence e)) (N.twist r f n)
    approximate M hb n e =
      let kprec = suc e
          d = U.B.cutoff kprec
          m = d + suc n
          k = m + n
          past = NP.m≤m+n d (suc n)
          eps = Basel.reciprocalSequence e
          leaf : ∀ v → Circle.height v ≃ Circle.height p0 →
            Box (two * (M + eps)) (weighted n m v)
          leaf v h =
            let inside = P.≤-reflexive (H.normHeight v p0 h)
                re = U.B.limitErrorAfter (C.realTerms (N.twist (q v) f)) _
                  (λ i → proj₁ (U.D.termBound (q v) inside i))
                  (C.realConverges (Eval.converges (ev v))) kprec m past
                im = U.B.limitErrorAfter (C.imagTerms (N.twist (q v) f)) _
                  (λ i → proj₂ (U.D.termBound (q v) inside i))
                  (C.imagConverges (Eval.converges (ev v))) kprec m past
                b = approxBound _ _ M eps (proj₁ (hb v)) re ,
                    approxBound _ _ M eps (proj₂ (hb v)) im
            in H.weightedBox p0 v n (M + eps) (prefix m) h b
          leaves = Circle.mapLeaves k (Circle.root k p0) leaf (Circle.circleLeaves k p0)
      in boxCong (extract n d) (Circle.meanBox k (Circle.root k p0)
        (two * (M + eps)) (weighted n m) leaves)

    coefficientBound : ∀ M → (∀ p → Box M (Eval.value (ev p))) →
      ∀ n → Box (two * M) (N.twist r f n)
    coefficientBound M hb n =
      let cv = Seq.xₙ→x∧x≃y⇒xₙ→y
            (Conv.mulR (Const.constantConverges two)
              (Conv.addR (Const.constantConverges M) Basel.reciprocalSequenceConvergesZero))
            (P.*-congˡ (P.+-identityʳ M))
          z = N.twist r f n
      in Seq.xₙ≤yₙ⇒x₀≤y₀ (Const.constantConverges ∣ C.re z ∣) cv
          (λ e → proj₁ (approximate M hb n e)) ,
         Seq.xₙ≤yₙ⇒x₀≤y₀ (Const.constantConverges ∣ C.im z ∣) cv
          (λ e → proj₂ (approximate M hb n e))
