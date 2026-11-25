module DASHI.Foundations.BishopChudnovskyPairedTotalityExact where

-- SOURCE-WRITTEN, not kernel checked. Actual positiveView/intervalAt
-- totality from paired signed source updates, no analytic premise.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.Product.Base using (Σ; _,_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Data.Nat using (_^_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; cong₂)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G

-- The witness retains actual integer equality, not just a Bool sign.
record Positive (z : Z.ℤ) : Set where
  constructor pos
  field predecessor : Nat
        value : z ≡ Z.+_ (suc predecessor)
record Negative (z : Z.ℤ) : Set where
  constructor neg
  field predecessor : Nat
        value : z ≡ Z.-[1+_] predecessor
record Nonnegative (z : Z.ℤ) : Set where
  constructor nn
  field magnitude : Nat
        value : z ≡ Z.+_ magnitude

positiveNat : (n : Nat) → N.NonZero n → Positive (Z.+_ n)
positiveNat zero nz = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
positiveNat (suc n) nz = pos n refl

successorWitness : (n : Nat) → N.NonZero n → Σ Nat (λ p → n ≡ suc p)
successorWitness zero nz = ⊥-elim (N.≢-nonZero⁻¹ zero {{nz}} refl)
successorWitness (suc n) nz = n , refl

positiveTimesPositive : ∀ {x y} → Positive x → Positive y →
  Positive (Z._*_ x y)
positiveTimesPositive (pos a refl) (pos b refl) =
  pos (b + a * suc b) refl

positiveTimesNegative : ∀ {x y} → Positive x → Negative y →
  Negative (Z._*_ x y)
positiveTimesNegative (pos a refl) (neg b refl) =
  neg (b + a * suc b) refl

negativeTimesNegative : ∀ {x y} → Negative x → Negative y →
  Positive (Z._*_ x y)
negativeTimesNegative (neg a refl) (neg b refl) =
  pos (b + a * suc b) refl

positiveIsNonnegative : ∀ {x} → Positive x → Nonnegative x
positiveIsNonnegative (pos a e) = nn (suc a) e

nonnegativeTimesPositive : ∀ {x y} → Nonnegative x → Positive y →
  Nonnegative (Z._*_ x y)
nonnegativeTimesPositive (nn a refl) (pos b refl) = nn (a * suc b) refl

nonnegativePlusPositive : ∀ {x y} → Nonnegative x → Positive y →
  Positive (Z._+_ x y)
nonnegativePlusPositive (nn a refl) (pos b refl) =
  pos (a + b) (cong Z.+_ (NP.+-suc a b))

qPositive : (n : Nat) → Positive (CH.sourceQ n)
qPositive n rewrite G.sourceQNatural n =
  positiveNat (G.qNat n) (G.qNatNonZero n)

prefixQPositive : (n : Nat) → Positive (E.Q n)
prefixQPositive n rewrite G.prefixQNatural n =
  positiveNat (G.qProduct n) (G.qProductNonZero n)

weightPositive : (n : Nat) → Positive (E.a n)
weightPositive n = pos (13591408 + CH.B * n) refl

leafPred : Nat → Nat
leafPred i = 119 + i * (1104 + i * (2592 + i * 1728))

leafSuccessor : (i : Nat) → G.leafMagnitude i ≡ suc (leafPred i)
leafSuccessor i =
  solve 1
    (λ x →
      (con 24 :* (con 2 :* x :+ con 1)
              :* (con 6 :* x :+ con 1)
              :* (con 6 :* x :+ con 5))
      := (con 1 :+ (con 119 :+ x :*
         (con 1104 :+ x :* (con 2592 :+ x :* con 1728)))))
    refl i

nextPNegative : (i : Nat) → Negative (CH.sourceP (suc i))
nextPNegative i rewrite G.sourcePNegativeMagnitude i | leafSuccessor i =
  neg (leafPred i) refl

-- Original product W_n = P_n p_n. It alternates without a sign quotient.
W : Nat → Z.ℤ
W n = Z._*_ (E.P n) (CH.sourceP n)

WStep : (n : Nat) → W (suc n) ≡ Z._*_ (W n) (CH.sourceP (suc n))
WStep n rewrite E.prefixPStep n = refl

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

evenWPositive : (k : Nat) → Positive (W (twice k))
evenWPositive zero = pos 0 refl
evenWPositive (suc k) rewrite WStep (suc (twice k)) | WStep (twice k) =
  negativeTimesNegative
    (positiveTimesNegative (evenWPositive k) (nextPNegative (twice k)))
    (nextPNegative (suc (twice k)))

oddWNegative : (k : Nat) → Negative (W (suc (twice k)))
oddWNegative k rewrite WStep (twice k) =
  positiveTimesNegative (evenWPositive k) (nextPNegative (twice k))

term : Nat → Nat
term n = G.leafMagnitude n * G.weight (suc n)

weakGapPred : Nat → Nat
weakGapPred n = 2199023255551 * term n + G.gapTail n

weakGapIdentity : (n : Nat) →
  term n + suc (weakGapPred n) ≡ G.qNat (suc n) * G.weight n
weakGapIdentity n =
  trans
    (solve 2
      (λ t g → t :+ (con 1 :+ (con 2199023255551 :* t :+ g))
        := (con (2 ^ 41) :* t) :+ (con 1 :+ g))
      refl (term n) (G.gapTail n))
    (G.weightedGapIdentity n)

cancelNat : (a b : Nat) →
  Z._+_ (Z.+_ (a + b)) (Z.-_ (Z.+_ a)) ≡ Z.+_ b
cancelNat a b =
  trans (cong (λ x → Z._+_ (Z.+_ x) (Z.-_ (Z.+_ a))) (NP.+-comm a b))
    (trans (ZP.+-assoc (Z.+_ b) (Z.+_ a) (Z.-_ (Z.+_ a)))
      (trans (cong (Z._+_ (Z.+_ b)) (ZP.+-inverseʳ (Z.+_ a)))
             (ZP.+-identityʳ (Z.+_ b))))

pairGap : Nat → Z.ℤ
pairGap n =
  Z._+_ (Z._*_ (E.a n) (CH.sourceQ (suc n)))
         (Z._*_ (CH.sourceP (suc n)) (E.a (suc n)))

pairGapExact : (n : Nat) → pairGap n ≡ Z.+_ (suc (weakGapPred n))
pairGapExact n
  rewrite G.sourceQNatural (suc n) | G.sourcePNegativeMagnitude n
        | sym (ZP.neg-distribˡ-* (Z.+_ (G.leafMagnitude n))
                                 (Z.+_ (G.weight (suc n))))
        | NP.*-comm (G.weight n) (G.qNat (suc n))
        | sym (weakGapIdentity n) =
  cancelNat (term n) (suc (weakGapPred n))

pairGapPositive : (n : Nat) → Positive (pairGap n)
pairGapPositive n = pos (weakGapPred n) (pairGapExact n)

pairedTPositive : (n : Nat) →
  Nonnegative (E.T n) → Positive (W n) →
  Positive (E.T (suc (suc n)))
pairedTPositive n t w rewrite G.twoStepSource n =
  nonnegativePlusPositive
    (nonnegativeTimesPositive
      (nonnegativeTimesPositive t (qPositive n)) (qPositive (suc n)))
    (positiveTimesPositive w (pairGapPositive n))

singleTPositive : (n : Nat) →
  Nonnegative (E.T n) → Positive (W n) → Positive (E.T (suc n))
singleTPositive n t w rewrite E.prefixTStep n =
  nonnegativePlusPositive
    (nonnegativeTimesPositive t (qPositive n))
    (positiveTimesPositive w (weightPositive n))

evenTNonnegative : (k : Nat) → Nonnegative (E.T (twice k))
evenTNonnegative zero = nn 0 refl
evenTNonnegative (suc k) =
  positiveIsNonnegative
    (pairedTPositive (twice k) (evenTNonnegative k) (evenWPositive k))

evenNonemptyTPositive : (k : Nat) → Positive (E.T (twice (suc k)))
evenNonemptyTPositive k =
  pairedTPositive (twice k) (evenTNonnegative k) (evenWPositive k)

oddTPositive : (k : Nat) → Positive (E.T (suc (twice k)))
oddTPositive k =
  singleTPositive (twice k) (evenTNonnegative k) (evenWPositive k)

data Parity : Nat → Set where
  even : (k : Nat) → Parity (twice k)
  odd : (k : Nat) → Parity (suc (twice k))

parity : (n : Nat) → Parity n
parity zero = even 0
parity (suc n) with parity n
... | even k = odd k
... | odd k = even (suc k)

allNonemptyTPositive : (n : Nat) → Positive (E.T (suc n))
allNonemptyTPositive n with parity n
... | even k = oddTPositive k
... | odd k = evenNonemptyTPositive k

-- Bind actual positiveView, no replacement value and no assumed success.
positiveViewTotal : (n : Nat) →
  Σ CH.PositiveSum (λ s → CH.positiveView (CH.sourcePrefix (suc n)) ≡ just s)
positiveViewTotal n with allNonemptyTPositive n | prefixQPositive (suc n)
... | pos t te | pos q qe
  rewrite te | qe | E.prefixBOne (suc n) =
  CH.positiveSum t (q * suc zero + zero) , refl

-- Literal fixed-schedule evaluator success, not a new evaluation stream.
intervalAtTotal : (k : Nat) →
  Σ CH.Interval (λ w → CH.intervalAt k ≡ just w)
intervalAtTotal k
  with successorWitness (CH.rootScale k) (NP.m^n≢0 2 (CH.rootBits k))
     | positiveViewTotal ((k + 4) ND./ 41)
     | positiveViewTotal (CH.cutoff k)
... | (s , se) | (x , xe) | (y , ye)
  rewrite se | xe | ye =
  CH.orderedInterval s (CH.rootNumerator k) x y , refl
