module DASHI.Foundations.BishopChudnovskyWidthReflectionExact where

-- Intended all-index proof terms, SOURCE-WRITTEN; not elaborated or checked.
-- Width is independent of analytic overlap. No alternate evaluator.
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Nat.Base using (_≤_; _^_)
import Data.Nat.Properties as N
import Data.Nat.DivMod as ND
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Product.Base using (Σ; _,_)
import Data.Integer.Base as Z
import Data.Integer.Properties as I
open import Data.Integer.Solver renaming (module +-*-Solver to ZSolver)
open ZSolver using () renaming
  (solve to zs; _:+_ to _⊕_; _:*_ to _⊗_; con to zk; _:=_ to _⊜_)
import Data.Rational.Unnormalised as Q
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopChudnovskyWidthSourceExact as W
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskyOverlapBudgetExact as B

K : Nat
K = 426880

-- Algebraic order transport with explicit endpoint equalities.
move : ∀ {a b c d : Nat} → a ≡ b → c ≡ d → b ≤ d → a ≤ c
move refl refl h = h

record View (n : Nat) : Set where
  constructor view
  field
    value : CH.PositiveSum
    computes : CH.positiveView (CH.sourcePrefix (suc n)) ≡ just value
    numEq : E.T (suc n) ≡ Z.+_ (CH.num value)
    denEq : E.Q (suc n) ≡ Z.+_ (CH.den value)
open View

sourceView : (n : Nat) → View n
sourceView n with T.allNonemptyTPositive n | T.prefixQPositive (suc n)
... | T.pos t te | T.pos q qe rewrite te | qe | E.prefixBOne (suc n) =
  view (CH.positiveSum t (q * 1 + 0)) refl refl
    (cong (λ x → Z.+_ (suc x))
      (sym (trans (N.+-identityʳ (q * 1)) (N.*-identityʳ q))))

sourceDen : (n : Nat) (v : View n) →
  CH.den (value v) ≡ G.qProduct (suc n)
sourceDen n v = I.+-injective
  (trans (sym (denEq v)) (G.prefixQNatural (suc n)))

-- Turn the signed lower-plane witness into the actual natural comparison.
lowerPlane : (n : Nat) (v : View n) →
  CH.A * CH.den (value v) ≤ 2 * CH.num (value v)
lowerPlane n v with W.nonemptyLowerPlane n
... | T.pos j eq =
  let
    t = CH.num (value v)
    d = CH.den (value v)
    diff : W.slack (suc n) ≡ Z._-_ (Z.+_ (2 * t)) (Z.+_ (CH.A * d))
    diff rewrite numEq v | denEq v
      | sym (I.neg-distribˡ-* (Z.+_ CH.A) (Z.+_ d)) = refl
    nonnegative : Z._≤_ (Z.+_ 0) (Z._-_ (Z.+_ (2 * t)) (Z.+_ (CH.A * d)))
    nonnegative = subst (Z._≤_ (Z.+_ 0)) (trans (sym eq) diff) (Z.+≤+ N.z≤n)
  in unPlus (I.0≤i-j⇒j≤i nonnegative)
  where
    unPlus : ∀ {a b : Nat} → Z._≤_ (Z.+_ a) (Z.+_ b) → a ≤ b
    unPlus (Z.+≤+ h) = h

-- Signed cross before taking magnitude; sign is not erased in source.
crossSigned : (n : Nat) →
  Z._-_ (Z._*_ (E.T (suc n)) (E.Q n))
         (Z._*_ (E.T n) (E.Q (suc n)))
  ≡ Z._*_ (E.delta n) (E.Q n)
crossSigned n rewrite E.sourceAdjacentCrossIdentity n =
  trans (cong (λ a → Z._+_
      (Z._+_ (Z._*_ (E.T n) (E.Q (suc n))) (Z._*_ (E.delta n) (E.Q n))) a)
      (sym (I.-1*i≡-i (Z._*_ (E.T n) (E.Q (suc n))))))
    (zs 2 (λ a b → (a ⊕ b) ⊕ (zk (Z.-_ (Z.+_ 1)) ⊗ a) ⊜ b)
      refl (Z._*_ (E.T n) (E.Q (suc n))) (Z._*_ (E.delta n) (E.Q n)))

crossMagnitude : (n : Nat) (x : View n) (y : View (suc n)) →
  Z.∣ Z._-_ (Z.+_ (CH.den (value x) * CH.num (value y)))
            (Z.+_ (CH.den (value y) * CH.num (value x))) ∣
  ≡ G.qProduct (suc n) * W.H (suc n)
crossMagnitude n x y =
  let
    source = crossSigned (suc n)
    signedEq : Z._-_ (Z.+_ (CH.den (value x) * CH.num (value y)))
                     (Z.+_ (CH.den (value y) * CH.num (value x)))
      ≡ Z._*_ (E.delta (suc n)) (E.Q (suc n))
    signedEq rewrite N.*-comm (CH.den (value x)) (CH.num (value y))
                   | N.*-comm (CH.den (value y)) (CH.num (value x))
                   | sym (numEq x) | sym (numEq y) | sym (denEq x) | sym (denEq y) = source
  in trans (cong Z.∣_∣ signedEq)
     (trans (I.abs-* (E.delta (suc n)) (E.Q (suc n)))
       (trans (cong (λ a → a * Z.∣ E.Q (suc n) ∣) (W.hIsOriginalDefectMagnitude (suc n)))
        (trans (cong (W.H (suc n) *_) (cong Z.∣_∣ (G.prefixQNatural (suc n))))
          (N.*-comm (W.H (suc n)) (G.qProduct (suc n))))))

-- Ordered cross as a positive additive equality, including touching.
gapFromAbs : (a b j : Nat) → a ≤ b →
  Z.∣ Z._-_ (Z.+_ b) (Z.+_ a) ∣ ≡ j →
  b ≡ a + j
gapFromAbs a b j h eq =
  let
    gap : Z.+_ j ≡ Z._-_ (Z.+_ b) (Z.+_ a)
    gap = trans (cong Z.+_ (sym eq))
      (trans (cong Z.+_ (I.∣i-j∣≡∣j-i∣ (Z.+_ b) (Z.+_ a)))
             (I.∣-∣-≤ (Z.+≤+ h)))
    addBack = zs 2
      (λ x y → x ⊕ (y ⊕ (zk (Z.-_ (Z.+_ 1)) ⊗ x)) ⊜ y)
      refl (Z.+_ a) (Z.+_ b)
  in I.+-injective
    (sym (trans (cong (Z._+_ (Z.+_ a)) gap)
      (trans (cong (λ z → Z._+_ (Z.+_ a) (Z._+_ (Z.+_ b) z))
        (sym (I.-1*i≡-i (Z.+_ a)))) addBack)))

scaleEq : (k : Nat) → CH.rootScale k ≡ 4 * (2 ^ k)
scaleEq k = trans (cong (2 ^_) (N.+-comm k 2)) (N.^-distribˡ-+-* 2 2 k)

schedule : (k : Nat) → 8 * CH.rootScale k ≤ W.M ^ CH.cutoff k
schedule k =
  let
    n = CH.cutoff k
    a = 2 ^ k
    left : 8 * CH.rootScale k ≡ 2 ^ (5 + k)
    left = trans (cong (8 *_) (scaleEq k))
      (trans (solve 1 (λ x → con 8 :* (con 4 :* x) := con 32 :* x) refl a)
             (sym (N.^-distribˡ-+-* 2 5 k)))
    exp : 5 + k ≤ 41 * n
    exp = move (trans (N.+-comm 5 k) (N.+-suc k 4))
               (N.*-comm 41 n) (W.cutoffExponent k)
  in move left (N.^-*-assoc 2 41 n) (N.^-monoʳ-≤ 2 exp)

-- The tail proof is a single positive-product comparison in the raw chart.
tailBudget : (k d0 d1 t0 t1 : Nat) →
  d0 ≡ G.qProduct (CH.cutoff k) →
  d1 ≡ G.qProduct (suc (CH.cutoff k)) →
  CH.A * d0 ≤ 2 * t0 → CH.A * d1 ≤ 2 * t1 →
  K * (CH.rootNumerator k * (d0 * W.H (CH.cutoff k))) ≤ 2 * (t0 * t1)
tailBudget k d0 d1 t0 t1 q0 q1 l0 l1 =
  let
    n = CH.cutoff k
    s = CH.rootScale k
    r = CH.rootNumerator k
    h = W.H n
    p = W.M ^ n
    hBound : (8 * s) * h ≤ CH.A * d1
    hBound = N.≤-trans (N.*-mono-≤ (schedule k) N.≤-refl)
      (move refl (cong (CH.A *_) q1) (W.scaledDefectBound n))
    step1 : 8 * (K * (r * (d0 * h))) ≤ (101 * K * d0) * ((8 * s) * h)
    step1 = move
      (solve 4 (λ r′ d h′ k′ → con 8 :* (k′ :* (r′ :* (d :* h′)))
        := ((con 8 :* k′) :* (d :* h′)) :* r′) refl r d0 h K)
      (solve 4 (λ s′ d h′ k′ → (con 101 :* k′ :* d) :* ((con 8 :* s′) :* h′)
        := ((con 8 :* k′) :* (d :* h′)) :* (con 101 :* s′))
        refl s d0 h K)
      (N.*-mono-≤ N.≤-refl (W.radicalUpper k))
    step2 : (101 * K * d0) * ((8 * s) * h) ≤ (4 * CH.A * d0) * (CH.A * d1)
    step2 = N.*-mono-≤
      (N.*-mono-≤ (N.m≤m+n 43114880 11250756) N.≤-refl) hBound
    step3 : (4 * CH.A * d0) * (CH.A * d1) ≤ 8 * (2 * (t0 * t1))
    step3 = move
      (solve 3 (λ a x y → (con 4 :* a :* x) :* (a :* y)
        := con 4 :* ((a :* x) :* (a :* y))) refl CH.A d0 d1)
      (solve 2 (λ x y → con 8 :* (con 2 :* (x :* y))
        := con 4 :* ((con 2 :* x) :* (con 2 :* y))) refl t0 t1)
      (N.*-mono-≤ N.≤-refl (N.*-mono-≤ l0 l1))
  in N.*-cancelˡ-≤ 8 (N.≤-trans step1 (N.≤-trans step2 step3))

baseBudget : (d t : Nat) → CH.A * d ≤ 2 * t → K * d ≤ t
baseBudget d t h = N.*-cancelˡ-≤ 2
  (N.≤-trans
    (move (sym (N.*-assoc 2 K d)) refl
      (N.*-mono-≤ (N.m≤m+n 853760 12737649) N.≤-refl)) h)

-- Actual rational subtraction numerator: factor the raw denominator
-- product, then use the positive cross equality. No field inverse.
cornerNumerator : (s r dL dH tL tH j : Nat) →
  dL * tH ≡ dH * tL + j →
  Z._+_
    (Z._*_ (Z.+_ (K * suc r * dL)) (Z.+_ (s * tH)))
    (Z._*_ (Z.-_ (Z.+_ (K * r * dH))) (Z.+_ (s * tL)))
  ≡ Z.+_ (s * (K * (dL * tH + r * j)))
cornerNumerator s r dL dH tL tH j g =
  let
    a = Z.+_ (dL * tH)
    b = Z.+_ (dH * tL)
    jz = Z.+_ j
    sz = Z.+_ s
    rz = Z.+_ r
    kz = Z.+_ K
    minus = Z.-_ (Z.+_ 1)
    factor :
      Z._+_
        (Z._*_ (Z.+_ (K * suc r * dL)) (Z.+_ (s * tH)))
        (Z._*_ (Z.-_ (Z.+_ (K * r * dH))) (Z.+_ (s * tL)))
      ≡ Z._*_ sz (Z._*_ kz
         (Z._+_ a (Z._*_ rz (Z._+_ a (Z._*_ minus b)))))
    factor rewrite sym (I.-1*i≡-i (Z.+_ (K * r * dH))) =
      zs 7
        (λ s′ r′ d e t u k′ →
          (k′ ⊗ (zk (Z.+_ 1) ⊕ r′) ⊗ d) ⊗ (s′ ⊗ u)
          ⊕ ((zk minus ⊗ (k′ ⊗ r′ ⊗ e)) ⊗ (s′ ⊗ t))
          ⊜ s′ ⊗ (k′ ⊗ ((d ⊗ u) ⊕
            (r′ ⊗ ((d ⊗ u) ⊕ (zk minus ⊗ (e ⊗ t)))))))
        refl sz rz (Z.+_ dL) (Z.+_ dH) (Z.+_ tL) (Z.+_ tH) kz
    gap : Z._+_ a (Z._*_ minus b) ≡ jz
    gap rewrite g =
      zs 2 (λ x y → (x ⊕ y) ⊕ (zk minus ⊗ x) ⊜ y) refl b jz
  in trans factor (cong (λ v → Z._*_ sz (Z._*_ kz (Z._+_ a (Z._*_ rz v)))) gap)

-- Reflect the actual corners directly into rational order by one
-- denominator-cleared integer comparison.
cornerWidth : (k sPred r j : Nat) (lo hi : CH.PositiveSum) →
  suc sPred ≡ 4 * (2 ^ k) →
  CH.den lo * CH.num hi ≡ CH.den hi * CH.num lo + j →
  K * CH.den lo ≤ CH.num lo →
  K * (r * j) ≤ 2 * (CH.num lo * CH.num hi) →
  (CH.endpoint sPred (suc r) lo Q.- CH.endpoint sPred r hi) Q.≤ B.dyadic k
cornerWidth k sPred r j lo@(CH.positiveSum l dl) hi@(CH.positiveSum h dh)
  scale g b t =
  let
    s = suc sPred
    p = 2 ^ k
    tl = suc l
    th = suc h
    dL = suc dl
    dH = suc dh
    v = K * (dL * th + r * j)
    budget = W.widthNumeratorBudget dL tl th r j b t
    bound : (s * v) * p ≤ (s * tl) * (s * th)
    bound = N.≤-trans
      (N.*-mono-≤ (N.*-mono-≤ N.≤-refl budget) N.≤-refl)
      (move
        (solve 4 (λ s′ l′ h′ p′ → (s′ :* (con 3 :* (l′ :* h′))) :* p′
          := (s′ :* (l′ :* h′)) :* (con 3 :* p′)) refl s tl th p)
        (trans (solve 3 (λ s′ l′ h′ → (s′ :* l′) :* (s′ :* h′)
          := (s′ :* (l′ :* h′)) :* s′) refl s tl th)
          (cong ((s * (tl * th)) *_) scale))
        (N.*-mono-≤ N.≤-refl (N.*-mono-≤ (N.m≤m+n 3 1) N.≤-refl)))
  in Q.*≤*
    (subst (λ z → Z._≤_ (Z._*_ z (Z.+_ p)) (Z.+_ ((s * tl) * (s * th))))
      (sym (cornerNumerator s r dL dH tl th j g)) (Z.+≤+ bound))

-- The evaluator's comparison is exactly the signed cross orientation.
orderedWidth : (k sp : Nat) (x : View ((k + 4) ND./ 41))
  (y : View (CH.cutoff k)) →
  suc sp ≡ CH.rootScale k →
  (CH.upper (CH.orderedInterval sp (CH.rootNumerator k) (value x) (value y))
     Q.- CH.lower (CH.orderedInterval sp (CH.rootNumerator k) (value x) (value y)))
    Q.≤ B.dyadic k
orderedWidth k sp x y se
  with (CH.num (value x) * CH.den (value y)) N.≤?
       (CH.num (value y) * CH.den (value x))
... | yes h =
  cornerWidth k sp (CH.rootNumerator k) j (value x) (value y)
    (trans se (scaleEq k))
    (gapFromAbs (CH.den (value y) * CH.num (value x))
      (CH.den (value x) * CH.num (value y)) j
      (move (N.*-comm (CH.den (value y)) (CH.num (value x)))
        (N.*-comm (CH.den (value x)) (CH.num (value y))) h) mag)
    (baseBudget _ _ lx) tail
  where
    n = (k + 4) ND./ 41
    j = CH.den (value x) * W.H (CH.cutoff k)
    lx = lowerPlane n x
    ly = lowerPlane (CH.cutoff k) y
    mag = trans (crossMagnitude n x y) (cong (_* W.H (CH.cutoff k)) (sym (sourceDen n x)))
    tail = tailBudget k (CH.den (value x)) (CH.den (value y))
      (CH.num (value x)) (CH.num (value y)) (sourceDen n x)
      (sourceDen (CH.cutoff k) y) lx ly
... | no nh =
  cornerWidth k sp (CH.rootNumerator k) j (value y) (value x)
    (trans se (scaleEq k))
    (gapFromAbs (CH.den (value x) * CH.num (value y))
      (CH.den (value y) * CH.num (value x)) j
      (move (N.*-comm (CH.den (value x)) (CH.num (value y)))
        (N.*-comm (CH.den (value y)) (CH.num (value x))) (N.≰⇒≥ nh)) mag)
    (baseBudget _ _ ly) tail
  where
    n = (k + 4) ND./ 41
    j = CH.den (value x) * W.H (CH.cutoff k)
    lx = lowerPlane n x
    ly = lowerPlane (CH.cutoff k) y
    mag = trans (I.∣i-j∣≡∣j-i∣
      (Z.+_ (CH.den (value y) * CH.num (value x)))
      (Z.+_ (CH.den (value x) * CH.num (value y))))
      (trans (crossMagnitude n x y) (cong (_* W.H (CH.cutoff k)) (sym (sourceDen n x))))
    tail = move refl
      (cong (2 *_) (N.*-comm (CH.num (value y)) (CH.num (value x))))
      (tailBudget k (CH.den (value x)) (CH.den (value y))
        (CH.num (value x)) (CH.num (value y)) (sourceDen n x)
        (sourceDen (CH.cutoff k) y) lx ly)

justInjective : ∀ {a b : CH.Interval} → just a ≡ just b → a ≡ b
justInjective refl = refl

-- Use the same computed interval equality; no reliance on equality of
-- independently constructed witness records.
literalWidthBound : (k : Nat) → B.literalWidth k Q.≤ B.dyadic k
literalWidthBound k with T.successorWitness (CH.rootScale k) (N.m^n≢0 2 (CH.rootBits k))
  | sourceView ((k + 4) ND./ 41) | sourceView (CH.cutoff k)
... | (sp , se) | x | y =
  let
    w = CH.orderedInterval sp (CH.rootNumerator k) (value x) (value y)
    actual : CH.intervalAt k ≡ just w
    actual rewrite se | computes x | computes y = refl
    same : w ≡ O.window k
    same = justInjective (trans (sym actual) (O.computed k))
  in subst (λ v → (CH.upper v Q.- CH.lower v) Q.≤ B.dyadic k)
    same (orderedWidth k sp x y (sym se))
