module DASHI.Moonshine.JInvariantBishopCofinalSquareSandwichExact where

-- Consume the actual unique finite-list sandwich of SquareExhaustion.
-- No extra summation operator, no absolute-value-of-total substitution.
-- Every exhaustion between two cofinal squares has the original limit.
-- Source-written; rectangle/degree-list instantiations are separate.
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base as N using (_⊔_) renaming (_≤_ to _≤N_)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L

module Cofinal
  (f : K.NonzeroLatticePoint → ℝ) (respect : Re.PointRespect f)
  (v a : ℝ)
  (shell : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellComponent k f)) v)
  (absolute : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellAbsolute k f)) a)
  (items : Nat → List L.LatticePoint) (outer : Nat → Nat)
  (unique : ∀ n → Unique (items n))
  (inner : ∀ n {p} → p ∈ S.squarePoints n → p ∈ items n)
  (outside : ∀ n {p} → p ∈ items n → p ∈ S.squarePoints (outer n))
  (radius : ∀ n → n ≤N outer n)
  where

  signedConv = Ex.prefixConverges f respect v shell
  absConv = Ex.absPrefixConverges f respect a absolute

  selected : Nat → ℝ
  selected n = Re.sum (Ex.raw f) (items n)

  absPrefix : Nat → ℝ
  absPrefix n = Re.sum (λ p → ∣ Ex.raw f p ∣) (S.squarePoints n)

  remainder : ∀ n → ∣ selected n - Ex.prefix f n ∣ ≤ absPrefix (outer n) - absPrefix n
  remainder n = Ex.sandwich (Ex.raw f)
    (S.squarePointsUnique n) (unique n) (S.squarePointsUnique (outer n))
    (inner n) (outside n)

  converges : Seq._ConvergesTo_ selected v
  converges = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        delta = ((+ 1 / 4) ⋆) * eps
        dp = P.posx,y⇒posx*y (Eps.reciprocalNatPositive 3) (Eps.reciprocalNatPositive k)
        head = Seq.fast-ε-from-convergence (v , signedConv) delta dp
        tail = Seq.fast-ε-from-convergence (a , absConv) delta dp
        cut = proj₁ head ⊔ proj₁ tail
    in cut , λ n past →
      let after = NP.≤-trans (NP.n≤1+n cut) past
          hn = NP.≤-trans (NP.m≤m⊔n (proj₁ head) (proj₁ tail)) after
          tn = NP.≤-trans (NP.m≤n⊔m (proj₁ head) (proj₁ tail)) after
          to = NP.≤-trans tn (radius n)
          h = P.<⇒≤ (proj₂ head n hn)
          t1 = P.<⇒≤ (proj₂ tail (outer n) to)
          t2 = P.<⇒≤ (proj₂ tail n tn)
          diff = P.≤-respˡ-≃
            (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
              (λ x y z → x ⊖ y ⊜ (x ⊖ z) ⊖ (y ⊖ z))
              P.≃-refl (absPrefix (outer n)) (absPrefix n) a))
            (Bounds.boundSub t1 t2)
          t = P.≤-trans (remainder n) (P.≤-trans P.x≤∣x∣ diff)
          total = P.≤-respˡ-≃
            (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
              (λ x y z → x ⊖ z ⊜ (x ⊖ y) ⊕ (y ⊖ z))
              P.≃-refl (selected n) (Ex.prefix f n) v))
            (Bounds.boundAdd t h)
          budget = P.≤-respˡ-≃
            (let open P.ℝ-Solver in solve 1
              (λ e → ((Κ (+ 1 / 4) ⊗ e) ⊕ (Κ (+ 1 / 4) ⊗ e)) ⊕ (Κ (+ 1 / 4) ⊗ e)
                ⊜ Κ (+ 3 / 4) ⊗ e) P.≃-refl eps)
            (P.≤-respʳ-≃ (P.*-identityˡ eps)
              (P.*-monoʳ-≤-nonNeg
                (P.p≤q⇒p⋆≤q⋆ (+ 3 / 4) (+ 1 / 1)
                  (toWitness {a? = QP._≤?_ (+ 3 / 4) (+ 1 / 1)} _))
                (P.pos⇒nonNeg (Eps.reciprocalNatPositive k))))
      in P.≤-trans total budget }
