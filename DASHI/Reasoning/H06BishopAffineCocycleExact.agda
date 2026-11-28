module DASHI.Reasoning.H06BishopAffineCocycleExact where

-- Native coefficient cocycle on the ORIGINAL six-mark affine atlas.
-- Both source and transported apartness witnesses are retained.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as B
import RealProperties as BP
import DASHI.Reasoning.H06BishopAffineFrameExact as H
import DASHI.Reasoning.H06BishopAffineRechartExact as A

Pair : Set
Pair = B.ℝ × B.ℝ

PairEq : Pair → Pair → Set
PairEq (u , v) (x , y) = B._≃_ u x × B._≃_ v y

pairRefl : (p : Pair) → PairEq p p
pairRefl (u , v) = BP.≃-refl , BP.≃-refl

pairSym : {a b : Pair} → PairEq a b → PairEq b a
pairSym {(_ , _)} {(_ , _)} (u , v) = BP.≃-symm u , BP.≃-symm v

pairTrans : {a b c : Pair} → PairEq a b → PairEq b c → PairEq a c
pairTrans {(_ , _)} {(_ , _)} {(_ , _)} (u , v) (x , y) =
  BP.≃-trans u x , BP.≃-trans v y

forward backward : (p : A.Plane4) → A.Admissible p → Pair → Pair
forward p q (u , v) = A.forward0 p q u v , A.forward1 p q u v
backward p q (u , v) = A.backward0 p q u v , A.backward1 p q u v

evalPair : A.Row → Pair → B.ℝ
evalPair r (u , v) = A.eval r u v

evalCong : (r : A.Row) {a b : Pair} → PairEq a b →
  B._≃_ (evalPair r a) (evalPair r b)
evalCong (A.row o r s) {(_ , _)} {(_ , _)} (u , v) =
  BP.+-cong BP.≃-refl
    (BP.+-cong (BP.*-congˡ u) (BP.*-congˡ v))

forwardCong : (p : A.Plane4) (q : A.Admissible p) {a b : Pair} →
  PairEq a b → PairEq (forward p q a) (forward p q b)
forwardCong p q {(_ , _)} {(_ , _)} eq =
  evalCong (A.at p (A.first (A.mark q))) eq ,
  evalCong (A.at p (A.second (A.mark q))) eq

-- The original guarded inverse is fixed for this chart, not reselected.
backwardCong : (p : A.Plane4) (q : A.Admissible p) {a b : Pair} →
  PairEq a b → PairEq (backward p q a) (backward p q b)
backwardCong p q {(_ , _)} {(_ , _)} (u , v)
  with A.pivotAt p q
... | H.pivot2 a b c d nz =
  BP.*-congˡ (BP.-cong (BP.*-congˡ (BP.-cong u BP.≃-refl))
                       (BP.*-congˡ (BP.-cong v BP.≃-refl))) ,
  BP.*-congˡ (BP.-cong (BP.*-congˡ (BP.-cong v BP.≃-refl))
                       (BP.*-congˡ (BP.-cong u BP.≃-refl)))

originCancel : (u o : B.ℝ) → B._≃_ (B._+_ o (B._-_ u o)) u
originCancel u o = let open BP.ℝ-Solver in
  solve 2 (λ u o → (o ⊕ (u ⊖ o)) ⊜ u) BP.≃-refl u o

reopen : (p : A.Plane4) (q : A.Admissible p) (x : Pair) →
  PairEq (backward p q (forward p q x)) x
reopen p q (u , v) = A.reopen0 p q u v , A.reopen1 p q u v

-- The other direction: selected ambient coordinates reopen exactly.
reclose : (p : A.Plane4) (q : A.Admissible p) (x : Pair) →
  PairEq (forward p q (backward p q x)) x
reclose p (A.admissible q nz) (u , v)
  with A.at p (A.first q) | A.at p (A.second q)
... | A.row o a b | A.row w c d =
  BP.≃-trans (BP.+-cong BP.≃-refl
    (H.firstReconstruct (H.pivot2 a b c d nz) (B._-_ u o) (B._-_ v w)))
    (originCancel u o) ,
  BP.≃-trans (BP.+-cong BP.≃-refl
    (H.secondReconstruct (H.pivot2 a b c d nz) (B._-_ u o) (B._-_ v w)))
    (originCancel v w)

atNormalized : (p : A.Plane4) (q : A.Admissible p) (k : A.Axis) →
  A.at (A.rechart p q) k ≡ A.normalizedAt p q k
atNormalized p q A.axis0 = refl
atNormalized p q A.axis1 = refl
atNormalized p q A.axis2 = refl
atNormalized p q A.axis3 = refl

samePoint : (p : A.Plane4) (q : A.Admissible p) (k : A.Axis) (x : Pair) →
  B._≃_ (evalPair (A.at (A.rechart p q) k) (forward p q x))
    (evalPair (A.at p k) x)
samePoint p q k (u , v) rewrite atNormalized p q k =
  A.ambientForward p q k u v

samePointReverse : (p : A.Plane4) (q : A.Admissible p) (k : A.Axis) (x : Pair) →
  B._≃_ (evalPair (A.at (A.rechart p q) k) x)
    (evalPair (A.at p k) (backward p q x))
samePointReverse p q k (u , v) rewrite atNormalized p q k =
  A.ambientReverse p q k u v

-- Compare the exact same target mark; admissibility is evidence on
-- each actual plane, not inferred by treating a zero minor as invertible.
markForward : (p : A.Plane4) (q r : A.Admissible p)
  (nz : B._≄0 (A.detAt (A.rechart p q) (A.mark r))) (x : Pair) →
  PairEq (forward (A.rechart p q) (A.admissible (A.mark r) nz) (forward p q x))
    (forward p r x)
markForward p q r nz x =
  samePoint p q (A.first (A.mark r)) x ,
  samePoint p q (A.second (A.mark r)) x

-- Actual two-hop versus direct chart equality at arbitrary target point.
cocycleEval : (p : A.Plane4) (q r : A.Admissible p)
  (nz : B._≄0 (A.detAt (A.rechart p q) (A.mark r)))
  (k : A.Axis) (x : Pair) →
  B._≃_ (evalPair (A.at (A.rechart (A.rechart p q)
                         (A.admissible (A.mark r) nz)) k) x)
         (evalPair (A.at (A.rechart p r) k) x)
cocycleEval p q r nz k x =
  let p′ = A.rechart p q
      r′ = A.admissible (A.mark r) nz
      t = backward p r x
      y = forward p q t
      z = forward p′ r′ y
      zEq = pairTrans {z} {forward p r t} {x}
        (markForward p q r nz t) (reclose p r x)
  in BP.≃-trans
    (evalCong (A.at (A.rechart p′ r′) k) (pairSym {z} {x} zEq))
    (BP.≃-trans (samePoint p′ r′ k y)
      (BP.≃-trans (samePoint p q k t)
        (BP.≃-symm (samePointReverse p r k x))))

-- Coefficient equality is stronger than equality at a single point.
-- Recover each coefficient by probing zero and two independent axes.
originProbe : (r : A.Row) → B._≃_ (evalPair r (B.0ℝ , B.0ℝ)) (A.origin r)
originProbe (A.row o r s) = let open BP.ℝ-Solver in
  solve 3 (λ o r s → (o ⊕ (r ⊗ Κ 0ℚᵘ ⊕ s ⊗ Κ 0ℚᵘ)) ⊜ o) BP.≃-refl o r s

slope0Probe : (r : A.Row) →
  B._≃_ (B._-_ (evalPair r (B.1ℝ , B.0ℝ)) (evalPair r (B.0ℝ , B.0ℝ))) (A.slope0 r)
slope0Probe (A.row o r s) = let open BP.ℝ-Solver in
  solve 3 (λ o r s →
    ((o ⊕ (r ⊗ Κ 1ℚᵘ ⊕ s ⊗ Κ 0ℚᵘ)) ⊖
     (o ⊕ (r ⊗ Κ 0ℚᵘ ⊕ s ⊗ Κ 0ℚᵘ))) ⊜ r) BP.≃-refl o r s

slope1Probe : (r : A.Row) →
  B._≃_ (B._-_ (evalPair r (B.0ℝ , B.1ℝ)) (evalPair r (B.0ℝ , B.0ℝ))) (A.slope1 r)
slope1Probe (A.row o r s) = let open BP.ℝ-Solver in
  solve 3 (λ o r s →
    ((o ⊕ (r ⊗ Κ 0ℚᵘ ⊕ s ⊗ Κ 1ℚᵘ)) ⊖
     (o ⊕ (r ⊗ Κ 0ℚᵘ ⊕ s ⊗ Κ 0ℚᵘ))) ⊜ s) BP.≃-refl o r s

record RowEq (a b : A.Row) : Set where
  constructor rowEq
  field
    originEq : B._≃_ (A.origin a) (A.origin b)
    slope0Eq : B._≃_ (A.slope0 a) (A.slope0 b)
    slope1Eq : B._≃_ (A.slope1 a) (A.slope1 b)

coefficientExt : (a b : A.Row) →
  ((x : Pair) → B._≃_ (evalPair a x) (evalPair b x)) → RowEq a b
coefficientExt a b eq =
  let z = eq (B.0ℝ , B.0ℝ)
      u = eq (B.1ℝ , B.0ℝ)
      v = eq (B.0ℝ , B.1ℝ)
  in rowEq
    (BP.≃-trans (BP.≃-symm (originProbe a)) (BP.≃-trans z (originProbe b)))
    (BP.≃-trans (BP.≃-symm (slope0Probe a))
      (BP.≃-trans (BP.-cong u z) (slope0Probe b)))
    (BP.≃-trans (BP.≃-symm (slope1Probe a))
      (BP.≃-trans (BP.-cong v z) (slope1Probe b)))

-- All four ambient rows, hence all twelve coefficients, are compared.
-- Includes each of the six pivot marks. No global choice of pivot.
coefficientCocycle : (p : A.Plane4) (q r : A.Admissible p)
  (nz : B._≄0 (A.detAt (A.rechart p q) (A.mark r))) (k : A.Axis) →
  RowEq (A.at (A.rechart (A.rechart p q) (A.admissible (A.mark r) nz)) k)
        (A.at (A.rechart p r) k)
coefficientCocycle p q r nz k = coefficientExt _ _ (cocycleEval p q r nz k)

-- Source-written. Guard transport still consumes supplied constructive
-- apartness at the actual recharted target; no automatic total selector.
