module DASHI.Foundations.BishopChudnovskyWindowNestingExact where

-- SOURCE-WRITTEN, UNCOMPILED. Literal sorted positiveView, literal
-- root and cutoff, literal reciprocal corners. No common-value premise.
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Product.Base using (_×_; _,_)
open import Data.Nat.Base using (_≤_; _≤′_; _^_; ≤′-refl; ≤′-step)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong; subst; cong₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Integer.Base as Z
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as P
import DASHI.Foundations.BishopChudnovskyAdjacentNestingExact as A
import DASHI.Foundations.BishopChudnovskyDyadicRootExact as D
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O

lowerMono′ : ∀ {n m} → n ≤′ m → A.lower n Q.≤ A.lower m
lowerMono′ ≤′-refl = QP.≤-refl
lowerMono′ (≤′-step {n = j} le) with A.nested j
... | l , u = QP.≤-trans (lowerMono′ le) l

upperAnti′ : ∀ {n m} → n ≤′ m → A.upper m Q.≤ A.upper n
upperAnti′ ≤′-refl = QP.≤-refl
upperAnti′ (≤′-step {n = j} le) with A.nested j
... | l , u = QP.≤-trans u (upperAnti′ le)

v : Nat → CH.PositiveSum
v n = W.View.value (W.sourceView n)

vEq : (n : Nat) → A.S (suc n) Q.≃ P.viewFraction (v n)
vEq n = P.literalView n (W.sourceView n)

ViewLe : CH.PositiveSum → CH.PositiveSum → Set
ViewLe x y = CH.num x * CH.den y ≤ CH.num y * CH.den x

viewToOrder : (x y : CH.PositiveSum) →
  ViewLe x y → P.viewFraction x Q.≤ P.viewFraction y
viewToOrder (CH.positiveSum a b) (CH.positiveSum c d) h =
  Q.*≤* (Z.+≤+ h)

orderToView : (x y : CH.PositiveSum) →
  P.viewFraction x Q.≤ P.viewFraction y → ViewLe x y
orderToView (CH.positiveSum a b) (CH.positiveSum c d) (Q.*≤* (Z.+≤+ h)) = h

sourceOrder : (n m : Nat) → ViewLe (v n) (v m) → A.S (suc n) Q.≤ A.S (suc m)
sourceOrder n m h =
  QP.≤-respˡ-≃ (QP.≃-sym (vEq n))
    (QP.≤-respʳ-≃ (QP.≃-sym (vEq m)) (viewToOrder (v n) (v m) h))

lowV highV : Nat → CH.PositiveSum
lowV n with (CH.num (v n) * CH.den (v (suc n))) NP.≤?
              (CH.num (v (suc n)) * CH.den (v n))
... | yes _ = v n
... | no _ = v (suc n)
highV n with (CH.num (v n) * CH.den (v (suc n))) NP.≤?
               (CH.num (v (suc n)) * CH.den (v n))
... | yes _ = v (suc n)
... | no _ = v n

lowEq : (n : Nat) → P.viewFraction (lowV n) Q.≃ A.lower (suc n)
lowEq n with (CH.num (v n) * CH.den (v (suc n))) NP.≤?
               (CH.num (v (suc n)) * CH.den (v n))
... | yes h = QP.≃-trans (QP.≃-sym (vEq n))
  (QP.≃-sym (QP.p≤q⇒p⊓q≃p (sourceOrder n (suc n) h)))
... | no h = QP.≃-trans (QP.≃-sym (vEq (suc n)))
  (QP.≃-sym (QP.p≥q⇒p⊓q≃q (sourceOrder (suc n) n (NP.≰⇒≥ h))))

highEq : (n : Nat) → P.viewFraction (highV n) Q.≃ A.upper (suc n)
highEq n with (CH.num (v n) * CH.den (v (suc n))) NP.≤?
                (CH.num (v (suc n)) * CH.den (v n))
... | yes h = QP.≃-trans (QP.≃-sym (vEq (suc n)))
  (QP.≃-sym (QP.p≤q⇒p⊔q≃q (sourceOrder n (suc n) h)))
... | no h = QP.≃-trans (QP.≃-sym (vEq n))
  (QP.≃-sym (QP.p≥q⇒p⊔q≃p (sourceOrder (suc n) n (NP.≰⇒≥ h))))

lowMono : (n m : Nat) → n ≤ m → ViewLe (lowV n) (lowV m)
lowMono n m h = orderToView (lowV n) (lowV m)
  (QP.≤-respˡ-≃ (QP.≃-sym (lowEq n))
    (QP.≤-respʳ-≃ (QP.≃-sym (lowEq m))
      (lowerMono′ (NP.≤⇒≤′ (N.s≤s h)))))

highAnti : (n m : Nat) → n ≤ m → ViewLe (highV m) (highV n)
highAnti n m h = orderToView (highV m) (highV n)
  (QP.≤-respˡ-≃ (QP.≃-sym (highEq m))
    (QP.≤-respʳ-≃ (QP.≃-sym (highEq n))
      (upperAnti′ (NP.≤⇒≤′ (N.s≤s h)))))

-- A larger root and smaller positive series denominator enlarge a
-- reciprocal corner. Prove it in the raw natural cross chart.
cornerMono : (sp tp r u : Nat) (x y : CH.PositiveSum) →
  r * suc tp ≤ u * suc sp → ViewLe y x →
  CH.endpoint sp r x Q.≤ CH.endpoint tp u y
cornerMono sp tp r u x@(CH.positiveSum a b) y@(CH.positiveSum c d) ru xy =
  Q.*≤* (Z.+≤+
    (W.move
      (solve 5 (λ r s dx ty k →
        (k :* r :* dx) :* (s :* ty) := k :* ((r :* s) :* (ty :* dx)))
        refl r (suc tp) (CH.den x) (CH.num y) 426880)
      (solve 5 (λ u s dy tx k →
        (k :* u :* dy) :* (s :* tx) := k :* ((u :* s) :* (tx :* dy)))
        refl u (suc sp) (CH.den y) (CH.num x) 426880)
      (NP.*-mono-≤ NP.≤-refl (NP.*-mono-≤ ru xy))))

idx : Nat → Nat
idx k = (k + 4) ND./ 41

idxStep : (k : Nat) → idx k ≤ idx (suc k)
idxStep k = ND./-monoˡ-≤ 41 (NP.≤-step NP.≤-refl)

candidate : (k sp : Nat) → CH.Interval
candidate k sp = CH.interval (CH.endpoint sp (CH.rootNumerator k) (highV (idx k)))
  (CH.endpoint sp (suc (CH.rootNumerator k)) (lowV (idx k)))

orderedEq : (k sp : Nat) →
  CH.orderedInterval sp (CH.rootNumerator k) (v (idx k)) (v (suc (idx k)))
    ≡ candidate k sp
orderedEq k sp with
  (CH.num (v (idx k)) * CH.den (v (suc (idx k)))) NP.≤?
  (CH.num (v (suc (idx k))) * CH.den (v (idx k)))
... | yes _ = refl
... | no _ = refl

computedCandidate : (k sp : Nat) → CH.rootScale k ≡ suc sp →
  CH.intervalAt k ≡ just (candidate k sp)
computedCandidate k sp se
  rewrite se | W.View.computes (W.sourceView (idx k))
    | W.View.computes (W.sourceView (suc (idx k))) =
  cong just (orderedEq k sp)

windowEq : (k sp : Nat) → CH.rootScale k ≡ suc sp →
  O.window k ≡ candidate k sp
windowEq k sp se = W.justInjective
  (trans (sym (O.computed k)) (computedCandidate k sp se))

scaleRelation : (k sp tp : Nat) →
  CH.rootScale k ≡ suc sp → CH.rootScale (suc k) ≡ suc tp →
  suc tp ≡ 2 * suc sp
scaleRelation k sp tp se te =
  trans (sym te) (trans (D.scaleStep k) (cong (2 *_) se))

rootCrossLower : (k sp tp : Nat) →
  CH.rootScale k ≡ suc sp → CH.rootScale (suc k) ≡ suc tp →
  CH.rootNumerator k * suc tp ≤ CH.rootNumerator (suc k) * suc sp
rootCrossLower k sp tp se te =
  W.move
    (trans (cong (CH.rootNumerator k *_) (scaleRelation k sp tp se te))
      (solve 2 (λ r s → r :* (con 2 :* s) := (con 2 :* r) :* s)
        refl (CH.rootNumerator k) (suc sp)))
    refl (NP.*-mono-≤ (D.rootLowerRefines k) NP.≤-refl)

rootCrossUpper : (k sp tp : Nat) →
  CH.rootScale k ≡ suc sp → CH.rootScale (suc k) ≡ suc tp →
  suc (CH.rootNumerator (suc k)) * suc sp ≤ suc (CH.rootNumerator k) * suc tp
rootCrossUpper k sp tp se te =
  W.move refl
    (trans (cong (suc (CH.rootNumerator k) *_) (scaleRelation k sp tp se te))
      (solve 2 (λ r s → r :* (con 2 :* s) := (con 2 :* r) :* s)
        refl (suc (CH.rootNumerator k)) (suc sp)))
    (NP.*-mono-≤ (D.rootUpperRefines k) NP.≤-refl)

candidateNests : (k sp tp : Nat) →
  CH.rootScale k ≡ suc sp → CH.rootScale (suc k) ≡ suc tp →
  (CH.lower (candidate k sp) Q.≤ CH.lower (candidate (suc k) tp)) ×
  (CH.upper (candidate (suc k) tp) Q.≤ CH.upper (candidate k sp))
candidateNests k sp tp se te =
  cornerMono sp tp (CH.rootNumerator k) (CH.rootNumerator (suc k))
    (highV (idx k)) (highV (idx (suc k)))
    (rootCrossLower k sp tp se te) (highAnti (idx k) (idx (suc k)) (idxStep k)) ,
  cornerMono tp sp (suc (CH.rootNumerator (suc k))) (suc (CH.rootNumerator k))
    (lowV (idx (suc k))) (lowV (idx k))
    (rootCrossUpper k sp tp se te) (lowMono (idx k) (idx (suc k)) (idxStep k))

-- Actual original window nesting, not the fast alternative evaluator.
windowNests : (k : Nat) →
  (CH.lower (O.window k) Q.≤ CH.lower (O.window (suc k))) ×
  (CH.upper (O.window (suc k)) Q.≤ CH.upper (O.window k))
windowNests k
  with T.successorWitness (CH.rootScale k) (NP.m^n≢0 2 (CH.rootBits k))
     | T.successorWitness (CH.rootScale (suc k)) (NP.m^n≢0 2 (CH.rootBits (suc k)))
... | sp , se | tp , te
  rewrite windowEq k sp se | windowEq (suc k) tp te =
  candidateNests k sp tp se te

windowLowerMono : ∀ {k j} → k ≤′ j →
  CH.lower (O.window k) Q.≤ CH.lower (O.window j)
windowLowerMono ≤′-refl = QP.≤-refl
windowLowerMono (≤′-step {n = j} le) with windowNests j
... | l , u = QP.≤-trans (windowLowerMono le) l

windowUpperAnti : ∀ {k j} → k ≤′ j →
  CH.upper (O.window j) Q.≤ CH.upper (O.window k)
windowUpperAnti ≤′-refl = QP.≤-refl
windowUpperAnti (≤′-step {n = j} le) with windowNests j
... | l , u = QP.≤-trans u (windowUpperAnti le)
