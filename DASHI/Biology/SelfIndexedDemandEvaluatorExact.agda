module DASHI.Biology.SelfIndexedDemandEvaluatorExact where

-- Native demand evaluator for the ORIGINAL self-indexed carrier.
-- Finite programs denote actual functions on I_n, not dense vectors.
-- The matching observation must be supplied explicitly; no decidable
-- propositional equality of arbitrary function spaces is assumed.
open import DASHI.Core.Prelude
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as T

Digit : Set
Digit = Fin 9

record Write (Key : Set) : Set where
  constructor write
  field
    address : Key
    value : Digit

record Program (Key : Set) : Set where
  constructor program
  field
    baseline : Digit
    newestFirst : List (Write Key)

record Result : Set where
  constructor result
  field
    digit : Digit
    comparisons : Nat
open Result public

increment : Result → Result
increment (result d k) = result d (suc k)

-- The same fold defines the evaluator and its comparison-count clock.
-- Later writes have priority; no discarded original execution history.
scan : {Key Query : Set} → (Key → Query → Bool) →
  Digit → List (Write Key) → Query → Result
scan match base [] q = result base zero
scan match base (write k v ∷ rest) q with match k q
... | true = result v 1
... | false = increment (scan match base rest q)

demand : {Key Query : Set} → (Key → Query → Bool) →
  Program Key → Query → Result
demand match (program d ws) = scan match d ws

denote : (n : Nat) {Key : Set} →
  (Key → T.SelfIndexedCarrier n → Bool) →
  Program Key → T.SelfIndexedCarrier (suc n)
denote n match p q = digit (demand match p q)

-- The typed finite write semantics remains separate from equality of
-- arbitrary I_n inhabitants. These are constructive computation laws.
headHit : {Key Query : Set} (m : Key → Query → Bool)
  (d v : Digit) (k : Key) (ws : List (Write Key)) (q : Query) →
  m k q ≡ true → scan m d (write k v ∷ ws) q ≡ result v 1
headHit m d v k ws q eq rewrite eq = refl

headMiss : {Key Query : Set} (m : Key → Query → Bool)
  (d v : Digit) (k : Key) (ws : List (Write Key)) (q : Query) →
  m k q ≡ false →
  scan m d (write k v ∷ ws) q ≡ increment (scan m d ws q)
headMiss m d v k ws q eq rewrite eq = refl

lengthWrites : {Key : Set} → List (Write Key) → Nat
lengthWrites [] = zero
lengthWrites (_ ∷ ws) = suc (lengthWrites ws)

clockBound : {Key Query : Set} (m : Key → Query → Bool)
  (d : Digit) (ws : List (Write Key)) (q : Query) →
  comparisons (scan m d ws q) ≤ lengthWrites ws
clockBound m d [] q = z≤n
clockBound m d (write k v ∷ ws) q with m k q
... | true = s≤s z≤n
... | false = s≤s (clockBound m d ws q)

-- Match by the ACTUAL finite digit functions at the first two levels.
finEqual : {n : Nat} → Fin n → Fin n → Bool
finEqual fzero fzero = true
finEqual fzero (fsuc j) = false
finEqual (fsuc i) fzero = false
finEqual (fsuc i) (fsuc j) = finEqual i j

and : Bool → Bool → Bool
and true b = b
and false b = false

d0 d1 d2 d3 d4 d5 d6 d7 d8 : Digit
d0 = fzero
d1 = fsuc d0'
  where d0' : Fin 8
        d0' = fzero
d2 = fsuc (fsuc fzero)
d3 = fsuc (fsuc (fsuc fzero))
d4 = fsuc (fsuc (fsuc (fsuc fzero)))
d5 = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))
d6 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
d7 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
d8 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))

match0 : T.SelfIndexedCarrier 0 → T.SelfIndexedCarrier 0 → Bool
match0 tt tt = true

match1 : Digit → T.SelfIndexedCarrier 1 → Bool
match1 d f = finEqual d (f tt)

match2 : T.SelfIndexedCarrier 2 → T.SelfIndexedCarrier 2 → Bool
match2 f g =
  and (finEqual (f (λ _ → d0)) (g (λ _ → d0)))
  (and (finEqual (f (λ _ → d1)) (g (λ _ → d1)))
  (and (finEqual (f (λ _ → d2)) (g (λ _ → d2)))
  (and (finEqual (f (λ _ → d3)) (g (λ _ → d3)))
  (and (finEqual (f (λ _ → d4)) (g (λ _ → d4)))
  (and (finEqual (f (λ _ → d5)) (g (λ _ → d5)))
  (and (finEqual (f (λ _ → d6)) (g (λ _ → d6)))
  (and (finEqual (f (λ _ → d7)) (g (λ _ → d7)))
       (finEqual (f (λ _ → d8)) (g (λ _ → d8))))))))))

level2Program : Program Digit
level2Program = program d2 (write d1 d0 ∷ write d0 d8 ∷ [])

level2 : T.SelfIndexedCarrier 2
level2 = denote 1 match1 level2Program

-- An actual nonconstant level-three function, indexed by level-two
-- functions; no enumeration of the 9^9 level-two addresses.
level3Program : Program (T.SelfIndexedCarrier 2)
level3Program = program d2 (write level2 d7 ∷ [])

level3 : T.SelfIndexedCarrier 3
level3 = denote 2 match2 level3Program

level3Hit : level3 level2 ≡ d7
level3Hit = refl

level3Miss : level3 (λ _ → d0) ≡ d2
level3Miss = refl

level2ExplicitZero : level2 (λ _ → d1) ≡ d0
level2ExplicitZero = refl

level3Clock : comparisons (demand match2 level3Program level2) ≡ 1
level3Clock = refl

-- Original typed description-length ledger. Units are declared counts
-- (not bits). Match work inside each comparison is NOT counted here.
demandComplexity : {Key Query : Set} (m : Key → Query → Bool) →
  (p : Program Key) → Query → Nat → Nat → T.WeaveComplexity
demandComplexity m (program d ws) q keyAndTypeUnits residualUnits =
  T.weaveComplexity (suc (lengthWrites ws))
    (comparisons (scan m d ws q)) 1 keyAndTypeUnits residualUnits

-- Native level3 example and generic demand fold are source-written.
-- Higher-level canonical sparse key compilation is executable separately.
-- No all-function compression, functional extensionality or kernel claim.
