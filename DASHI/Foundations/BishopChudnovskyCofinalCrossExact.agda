module DASHI.Foundations.BishopChudnovskyCofinalCrossExact where

-- SOURCE-WRITTEN, UNCOMPILED. Cofinal overlap and native decidability
-- on the ORIGINAL window. Neither decidability nor a finite pass is
-- the all-index proof. The nesting hypotheses below must be paid.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QS
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Stage
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as X
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W

L U m e a b : Nat → Q.ℚᵘ
L k = CH.lower (O.window k)
U k = CH.upper (O.window k)
m = Stage.qMachinStage
e = O.machinRadius
a k = m k Q.- e k
b k = m k Q.+ e k

CrossAt : Nat → Set
CrossAt k = O.Cross (O.window k) (m k) (e k)

crossDec : (k : Nat) → Dec (CrossAt k)
crossDec k with L k QP.≤? b k | m k QP.≤? (U k Q.+ e k)
... | yes l | yes u = yes (O.cross l u)
... | no nl | _ = no (λ c → nl (O.Cross.lowerCross c))
... | yes _ | no nu = no (λ c → nu (O.Cross.upperCross c))

-- Constructive local elimination of a negative comparison. This is
-- the exact negative-witness formulation of the still unpaid theorem.
allFromNoCounterexample : ¬ (Σ Nat (λ k → ¬ CrossAt k)) →
  (k : Nat) → CrossAt k
allFromNoCounterexample h k with crossDec k
... | yes c = c
... | no n = ⊥-elim (h (k , n))

noCounterexampleFromAll : ((k : Nat) → CrossAt k) →
  ¬ (Σ Nat (λ k → ¬ CrossAt k))
noCounterexampleFromAll h (k , n) = n (h k)

minusRight : (p q r : Q.ℚᵘ) →
  p Q.≤ (q Q.+ r) → (p Q.- r) Q.≤ q
minusRight p q r h =
  QP.≤-respʳ-≃
    (let open QS in solve 2 (λ x y → (x ⊕ y) ⊖ y ⊜ x)
      QP.≃-refl q r)
    (QP.+-monoˡ-≤ (Q.-_ r) h)

plusRight : (p q r : Q.ℚᵘ) →
  (p Q.- r) Q.≤ q → p Q.≤ (q Q.+ r)
plusRight p q r h =
  QP.≤-respˡ-≃
    (let open QS in solve 2 (λ x y → (x ⊖ y) ⊕ y ⊜ x)
      QP.≃-refl p r)
    (QP.+-monoˡ-≤ r h)

-- Exact geometric restriction along a refinement of both intervals.
restrictCross : (k j : Nat) →
  L k Q.≤ L j → U j Q.≤ U k →
  a k Q.≤ a j → b j Q.≤ b k →
  CrossAt j → CrossAt k
restrictCross k j lk uk ak bk c =
  O.cross
    (QP.≤-trans lk (QP.≤-trans (O.Cross.lowerCross c) bk))
    (plusRight (m k) (U k) (e k)
      (QP.≤-trans ak
        (QP.≤-trans
          (minusRight (m j) (U j) (e j) (O.Cross.upperCross c)) uk)))

-- Stage zero is special: its radius 22/7 is not part of the
-- geometric Machin nesting. Compute its original root by uniqueness,
-- not by the large reference scan.
rootZero : CH.rootNumerator zero ≡ 400
rootZero = sym (Floor.floorSquareRootUnique 160080 400
  (from-yes (160000 NP.≤? 160080))
  (from-yes (160081 NP.≤? 160801)))

w0 : CH.Interval
w0 = CH.orderedInterval 3 400
  (CH.positiveSum 13591408 0)
  (CH.positiveSum 3568253353002380914326839 262537412640767999)

computedZero : CH.intervalAt zero ≡ just w0
computedZero rewrite rootZero = refl

windowZero : O.window zero ≡ w0
windowZero = W.justInjective (trans (sym (O.computed zero)) computedZero)

crossZero : CrossAt zero
crossZero rewrite windowZero = O.cross
  (from-yes (CH.lower w0 QP.≤? (m zero Q.+ e zero)))
  (from-yes (m zero QP.≤? (CH.upper w0 Q.+ e zero)))

-- Only positive stages are used in the cofinal family.
allFromCofinal :
  ((k j : Nat) → suc k ≤ suc j → L (suc k) Q.≤ L (suc j)) →
  ((k j : Nat) → suc k ≤ suc j → U (suc j) Q.≤ U (suc k)) →
  ((k j : Nat) → suc k ≤ suc j → a (suc k) Q.≤ a (suc j)) →
  ((k j : Nat) → suc k ≤ suc j → b (suc j) Q.≤ b (suc k)) →
  ((k : Nat) → Σ Nat (λ j → (suc k ≤ suc j) × CrossAt (suc j))) →
  (k : Nat) → X.ExpandedCross k
allFromCofinal ll uu aa bb hit zero =
  X.crossToExpanded zero (X.fromCross zero crossZero)
allFromCofinal ll uu aa bb hit (suc k) with hit k
... | j , le , c = X.crossToExpanded (suc k)
  (X.fromCross (suc k)
    (restrictCross (suc k) (suc j) (ll k j le) (uu k j le)
      (aa k j le) (bb k j le) c))
