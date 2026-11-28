module DASHI.Moonshine.JInvariantBishopLambertCofinalRegroupExact where

-- SOURCE-WRITTEN, kernel pending. Generic degree triangle / row rectangle
-- limit interchange by a positive degree majorant. Reuses original finite
-- list subset decomposition and real epsilon arithmetic. No equality of
-- signed totals substitutes for absolute control.
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base as N using (_⊔_) renaming (_≤_ to _≤N_)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopLambertDegreeChartExact as D
import DASHI.Moonshine.JInvariantBishopRectangleRowFoldExact as Fold
import DASHI.Moonshine.JInvariantBishopRectangleRowLimitAttachmentExact as Limit
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as H
open Re using (sum)

sumMono : ∀ {X : Set} (f b : X → ℝ) → (∀ x → f x ≤ b x) →
  ∀ xs → sum f xs ≤ sum b xs
sumMono f b h [] = P.≤-refl
sumMono f b h (x ∷ xs) = P.+-mono-≤ (h x) (sumMono f b h xs)

majorizedDifference : ∀ {X : Set} (f b : X → ℝ) →
  (∀ x → ∣ f x ∣ ≤ b x) →
  {ps qs : List X} → Unique ps → Unique qs →
  (∀ {x} → x ∈ ps → x ∈ qs) →
  ∣ sum f qs - sum f ps ∣ ≤ sum b qs - sum b ps
majorizedDifference f b h up uq incl with Ex.subsetDecomp up uq incl
... | rs , perm =
  P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (Ex.differenceRead f perm)))
    (P.≤-respʳ-≃ (P.≃-symm (Ex.differenceRead b perm))
      (P.≤-trans (Ex.sumTriangle f rs) (sumMono (λ x → ∣ f x ∣) b h rs)))

majorizedSandwich : ∀ {X : Set} (f b : X → ℝ) →
  (∀ x → ∣ f x ∣ ≤ b x) → (∀ x → R.NonNegative (b x)) →
  {ps qs rs : List X} → Unique ps → Unique qs → Unique rs →
  (∀ {x} → x ∈ ps → x ∈ qs) → (∀ {x} → x ∈ qs → x ∈ rs) →
  ∣ sum f qs - sum f ps ∣ ≤ sum b rs - sum b ps
majorizedSandwich f b h nn {ps} up uq ur pq qr =
  P.≤-trans (majorizedDifference f b h up uq pq)
    (P.+-monoˡ-≤ (R.- (sum b ps)) (Ex.subsetMono b nn uq ur qr))

-- Generic cofinal limit, with the actual degree prefix and its positive
-- majorant supplied by the finite degree fibre theorem.
module At
  (f b : D.Key → ℝ) (v B : ℝ)
  (bound : ∀ x → ∣ f x ∣ ≤ b x) (nonnegative : ∀ x → R.NonNegative (b x))
  (signed : Seq._ConvergesTo_ (λ n → sum f (D.triangle n)) v)
  (majorant : Seq._ConvergesTo_ (λ n → sum b (D.triangle n)) B)
  where

  rect : Nat → Nat → ℝ
  rect n m = sum f (D.rectangle n (n ⊔ m))
  prefix : (D.Key → ℝ) → Nat → ℝ
  prefix h n = sum h (D.triangle n)

  remainder : ∀ n m → ∣ rect n m - prefix f n ∣ ≤
    prefix b (n * (n ⊔ m)) - prefix b n
  remainder n m = majorizedSandwich f b bound nonnegative
    (D.triangleUnique n) (D.rectUnique n (n ⊔ m)) (D.triangleUnique (n * (n ⊔ m)))
    (D.inner n m) (D.outer n m)

  cofinal : ∀ height → Seq._ConvergesTo_ (λ n → rect n (height n)) v
  cofinal height = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        delta = ((+ 1 / 4) ⋆) * eps
        dp = P.posx,y⇒posx*y (Eps.reciprocalNatPositive 3) (Eps.reciprocalNatPositive k)
        head = Seq.fast-ε-from-convergence (v , signed) delta dp
        tail = Seq.fast-ε-from-convergence (B , majorant) delta dp
        cut = proj₁ head ⊔ proj₁ tail
    in cut , λ n past →
      let after = NP.≤-trans (NP.n≤1+n cut) past
          hn = NP.≤-trans (NP.m≤m⊔n (proj₁ head) (proj₁ tail)) after
          tn = NP.≤-trans (NP.m≤n⊔m (proj₁ head) (proj₁ tail)) after
          o = n * (n ⊔ height n)
          to = NP.≤-trans tn (D.outerRadius n (height n))
          h = P.<⇒≤ (proj₂ head n hn)
          t1 = P.<⇒≤ (proj₂ tail o to)
          t2 = P.<⇒≤ (proj₂ tail n tn)
          diff = P.≤-respˡ-≃
            (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
              (λ x y z → x ⊖ y ⊜ (x ⊖ z) ⊖ (y ⊖ z)) P.≃-refl (prefix b o) (prefix b n) B))
            (Bounds.boundSub t1 t2)
          t = P.≤-trans (remainder n (height n)) (P.≤-trans P.x≤∣x∣ diff)
          total = P.≤-respˡ-≃
            (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
              (λ x y z → x ⊖ z ⊜ (x ⊖ y) ⊕ (y ⊖ z)) P.≃-refl (rect n (height n)) (prefix f n) v))
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

  iterated : (rows : Nat → ℝ) →
    (∀ n → Seq._ConvergesTo_ (rect n) (rows n)) → Seq._ConvergesTo_ rows v
  iterated rows cv = Seq.con* λ { (suc k) →
    let eps = (+ 1 / suc k) ⋆
        delta = ((+ 1 / 4) ⋆) * eps
        dp = P.posx,y⇒posx*y (Eps.reciprocalNatPositive 3) (Eps.reciprocalNatPositive k)
        moduli = λ n → Seq.fast-ε-from-convergence (rows n , cv n) delta dp
        height = λ n → proj₁ (moduli n)
        both = Seq.fast-ε-from-convergence (v , cofinal height) delta dp
    in proj₁ both , λ n past →
      let h1 = P.<⇒≤ (proj₂ (moduli n) (height n) NP.≤-refl)
          h2 = P.<⇒≤ (proj₂ both n (NP.≤-trans (NP.n≤1+n (proj₁ both)) past))
          signed1 = P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ (rows n) (rect n (height n))) h1
          total = P.≤-respˡ-≃ (P.∣-∣-cong (let open P.ℝ-Solver in solve 3
            (λ x y z → x ⊖ z ⊜ (x ⊖ y) ⊕ (y ⊖ z)) P.≃-refl (rows n) (rect n (height n)) v))
            (Bounds.boundAdd signed1 h2)
          budget = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
            (λ e → (Κ (+ 1 / 4) ⊗ e) ⊕ (Κ (+ 1 / 4) ⊗ e) ⊜ Κ (+ 1 / 2) ⊗ e)
            P.≃-refl eps)
            (P.≤-respʳ-≃ (P.*-identityˡ eps)
              (P.*-monoʳ-≤-nonNeg
                (P.p≤q⇒p⋆≤q⋆ (+ 1 / 2) (+ 1 / 1)
                  (toWitness {a? = QP._≤?_ (+ 1 / 2) (+ 1 / 1)} _))
                (P.pos⇒nonNeg (Eps.reciprocalNatPositive k))))
      in P.≤-trans total budget }

  rowPrefix : Nat → Nat → ℝ
  rowPrefix m n = sum (λ d → f (m , d)) (H.oneTo n)

  rowSum : (Nat → ℝ) → Nat → ℝ
  rowSum value n = sum value (H.oneTo n)

  rowLimit : ∀ value →
    (∀ m → Seq._ConvergesTo_ (rowPrefix m) (value m)) →
    Seq._ConvergesTo_ (rowSum value) v
  rowLimit value cv = iterated (rowSum value) λ n →
    Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc m) → P.≃-symm (Fold.sumProduct (λ i j → f (i , j))
        (H.oneTo n) (H.oneTo (n ⊔ suc m)))})
      (rowSum value n ,
        Limit.listLimit (λ i m → rowPrefix i (n ⊔ m)) value
          (λ i → Limit.maxLimit n (cv i)) (H.oneTo n))
