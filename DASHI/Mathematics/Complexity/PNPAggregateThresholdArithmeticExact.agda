module DASHI.Mathematics.Complexity.PNPAggregateThresholdArithmeticExact where

-- Arithmetic of the actual threshold table in PNPAggregateThresholdDAGExact.
-- Keep zero/slack at the source. No completeness or complexity oracle.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec)
open import Data.List.Base using (List; []; _∷_; replicate; drop; length; _++_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as B
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedSemanticsExact as S
import DASHI.Mathematics.Complexity.PNPAggregateThresholdDAGExact as T

inc : Bool → Nat → Nat
inc false w = w
inc true w = suc w

count : List Bool → Nat
count [] = zero
count (b ∷ bs) = inc b (count bs)

sub : Nat → Nat → Nat
sub w zero = w
sub zero (suc c) = zero
sub (suc w) (suc c) = sub w c

mn : Nat → Nat → Nat
mn a zero = zero
mn zero (suc b) = zero
mn (suc a) (suc b) = suc (mn a b)

leB : Nat → Nat → Bool
leB zero w = true
leB (suc j) zero = false
leB (suc j) (suc w) = leB j w

tab : Nat → Nat → Nat → List Bool
tab w j zero = []
tab w j (suc k) = leB j w ∷ tab w (suc j) k

orFalse : (b : Bool) → B.orBool b false ≡ b
orFalse false = refl
orFalse true = refl

orAdjacent : (j w : Nat) →
  B.orBool (leB (suc j) w) (leB j w) ≡ leB j w
orAdjacent zero zero = refl
orAdjacent zero (suc w) = refl
orAdjacent (suc j) zero = refl
orAdjacent (suc j) (suc w) = orAdjacent j w

thresholdTransition : (b : Bool) (j w : Nat) →
  B.orBool (leB (suc j) w) (B.andBool b (leB j w))
  ≡ leB (suc j) (inc b w)
thresholdTransition false j w = orFalse (leB (suc j) w)
thresholdTransition true j w = orAdjacent j w

tailExact : (b : Bool) (w j k : Nat) →
  T.nextTail b (leB j w) (tab w (suc j) k)
  ≡ tab (inc b w) (suc j) k
tailExact b w j zero = refl
tailExact b w j (suc k)
  rewrite thresholdTransition b j w | tailExact b w (suc j) k = refl

rowExact : (b : Bool) (w k : Nat) →
  T.nextRow b (tab w zero (suc k)) ≡ tab (inc b w) zero (suc k)
rowExact b w k = cong (true ∷_) (tailExact b w zero k)

tabZero : (j k : Nat) → tab zero (suc j) k ≡ replicate k false
tabZero j zero = refl
tabZero j (suc k) = cong (false ∷_) (tabZero (suc j) k)

tableExact : (bs : List Bool) (k : Nat) →
  T.table bs k ≡ tab (count bs) zero (suc k)
tableExact [] k = cong (true ∷_) (sym (tabZero zero k))
tableExact (b ∷ bs) k rewrite tableExact bs k = rowExact b (count bs) k

tabShift : (w j k : Nat) → tab (suc w) (suc j) k ≡ tab w j k
tabShift w j zero = refl
tabShift w j (suc k) = cong (leB j w ∷_) (tabShift w (suc j) k)

countFalse : (k : Nat) → count (replicate k false) ≡ zero
countFalse zero = refl
countFalse (suc k) = countFalse k

-- Exact number of active thresholds strictly above cap, truncated to fuel.
countTab : (w cap fuel : Nat) →
  count (tab w (suc cap) fuel) ≡ mn fuel (sub w cap)
countTab zero zero fuel = trans (cong count (tabZero zero fuel)) (countFalse fuel)
countTab zero (suc cap) fuel = trans (cong count (tabZero (suc cap) fuel)) (countFalse fuel)
countTab (suc w) zero zero = refl
countTab (suc w) zero (suc fuel)
  rewrite tabShift w (suc zero) fuel | countTab w zero fuel = refl
countTab (suc w) (suc cap) fuel
  rewrite tabShift w (suc cap) fuel = countTab w cap fuel

advance : Nat → Nat → Nat
advance j zero = j
advance j (suc t) = advance (suc j) t

advanceSuc : (j t : Nat) → advance (suc j) t ≡ suc (advance j t)
advanceSuc j zero = refl
advanceSuc j (suc t) = advanceSuc (suc j) t

advanceZero : (t : Nat) → advance zero t ≡ t
advanceZero zero = refl
advanceZero (suc t) rewrite advanceSuc zero t | advanceZero t = refl

dropTab : (w j k t : Nat) →
  drop t (tab w j k) ≡ tab w (advance j t) (sub k t)
dropTab w j k zero = refl
dropTab w j zero (suc t) = refl
dropTab w j (suc k) (suc t) = dropTab w (suc j) k t

dropRow : (w k cap : Nat) →
  drop (suc cap) (tab w zero (suc k))
  ≡ tab w (suc cap) (sub k cap)
dropRow w k cap rewrite dropTab w zero (suc k) (suc cap)
                      | advanceZero (suc cap) = refl

countBound : (bs : List Bool) → count bs ≤ length bs
countBound [] = z≤n
countBound (false ∷ bs) = N.≤-trans (countBound bs) (N.n≤1+n _)
countBound (true ∷ bs) = s≤s (countBound bs)

subMono : ∀ {a b} → a ≤ b → (c : Nat) → sub a c ≤ sub b c
subMono h zero = h
subMono z≤n (suc c) = z≤n
subMono (s≤s h) (suc c) = subMono h c

mnRight : ∀ {a b} → a ≤ b → mn b a ≡ a
mnRight z≤n = refl
mnRight (s≤s h) = cong suc (mnRight h)

rowExcess : (bs : List Bool) (cap : Nat) →
  count (drop (suc cap) (T.table bs (length bs))) ≡ sub (count bs) cap
rowExcess bs cap
  rewrite tableExact bs (length bs)
        | dropRow (count bs) (length bs) cap
        | countTab (count bs) cap (sub (length bs) cap)
        | mnRight (subMono (countBound bs) cap) = refl

countAppend : (a b : List Bool) → count (a ++ b) ≡ count a + count b
countAppend [] b = refl
countAppend (false ∷ as) b = countAppend as b
countAppend (true ∷ as) b = cong suc (countAppend as b)

potential : ∀ {n} → T.Rows n → Vec Bool n → Nat
potential [] x = zero
potential ((is , cap) ∷ rs) x =
  sub (count (T.inputBits is x)) cap + potential rs x

aggregateCount : ∀ {n} (rs : T.Rows n) (x : Vec Bool n) →
  count (T.aggregateBits rs x) ≡ potential rs x
aggregateCount [] x = refl
aggregateCount ((is , cap) ∷ rs) x
  rewrite countAppend (drop (suc cap) (T.table (T.inputBits is x) (length is))) (T.aggregateBits rs x)
        | inputLength is x
        | rowExcess (T.inputBits is x) cap
        | aggregateCount rs x = refl
  where
    inputLength : ∀ {n} (is : List (Fin n)) (x : Vec Bool n) →
      length is ≡ length (T.inputBits is x)
    inputLength [] x = refl
    inputLength (i ∷ is) x = cong suc (inputLength is x)

tabAt : (w j k t : Nat) → suc t ≤ k →
  T.at false t (tab w j k) ≡ leB (advance j t) w
tabAt w j zero t ()
tabAt w j (suc k) zero h = refl
tabAt w j (suc k) (suc t) (s≤s h) = tabAt w (suc j) k t h

notSuccLE : (w k : Nat) → B.notBool (leB (suc k) w) ≡ leB w k
notSuccLE zero k = refl
notSuccLE (suc w) zero = refl
notSuccLE (suc w) (suc k) = notSuccLE w k

acceptExact : ∀ {n} (rs : T.Rows n) (k : Nat) (x : Vec Bool n) →
  T.aggregateAccept rs k x ≡ leB (potential rs x) k
acceptExact rs k x
  rewrite tableExact (T.aggregateBits rs x) (suc k)
        | tabAt (count (T.aggregateBits rs x)) zero (suc (suc k)) (suc k) (N.≤-refl)
        | advanceZero (suc k)
        | aggregateCount rs x = notSuccLE (potential rs x) k

leSound : (a b : Nat) → leB a b ≡ true → a ≤ b
leSound zero b h = z≤n
leSound (suc a) zero ()
leSound (suc a) (suc b) h = s≤s (leSound a b h)

leComplete : ∀ {a b} → a ≤ b → leB a b ≡ true
leComplete z≤n = refl
leComplete (s≤s h) = leComplete h

-- Literal native shared SAT formula, BIDI on the original input carrier.
-- Hard source predicates must be retained as their original conjuncts;
-- this arithmetic attachment does not claim to decide those conjuncts.
capacityToSAT : ∀ {n} (rs : T.Rows n) (k : Nat) (x : Vec Bool n) →
  potential rs x ≤ k → B.Satisfiable (S.sharedAcceptanceFormula (T.aggregateCircuit rs k))
capacityToSAT rs k x h =
  T.aggregateToSAT rs k x (trans (acceptExact rs k x) (leComplete h))

capacityFromSAT : ∀ {n} (rs : T.Rows n) (k : Nat) →
  B.Satisfiable (S.sharedAcceptanceFormula (T.aggregateCircuit rs k)) →
  Σ (Vec Bool n) (λ x → potential rs x ≤ k)
capacityFromSAT rs k sat with T.aggregateFromSAT rs k sat
... | x , yes = x , leSound (potential rs x) k (trans (sym (acceptExact rs k x)) yes)
