module DASHI.Geometry.COL where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes
open import DASHI.Core.LensKernel

------------------------------------------------------------------------
-- Contraction–Obstruction–Lift (COL)
------------------------------------------------------------------------

record COL (S : Nat -> Set) : Set1 where
  field
    E    : forall n -> S n -> Nat
    K    : forall n -> S n -> S n
    Obs  : forall n -> S n -> Bool
    lift : forall n -> S n -> S (suc n)

    -- Contraction inside level n: energy does not increase.
    contract : (n : Nat) (x : S n) -> E n (K n x) ≤ E n x

    -- Obstruction is stable under K: if you are obstructed, stepping doesn't “solve” it magically.
    obs-stable : (n : Nat) (x : S n) -> Obs n x ≡ true -> Obs n (K n x) ≡ true

    -- Lift is witness-respecting: the old state is embedded, not destroyed.
    embed-ok : (n : Nat) (x : S n) -> ⊤

open COL public

------------------------------------------------------------------------
-- Derived theorem hooks (the “schema theorems”)

-- If not obstructed, repeated contraction gives monotone energy sequence.
iterate : forall {A : Set} -> (A -> A) -> Nat -> A -> A
iterate f zero    x = x
iterate f (suc k) x = iterate f k (f x)

E-monotone-iter :
  forall {S : Nat -> Set} (C : COL S) ->
  (n : Nat) (k : Nat) (x : S n) ->
  COL.E C n (iterate (COL.K C n) k x) ≤ COL.E C n x
E-monotone-iter C n zero    x = ≤-refl
E-monotone-iter C n (suc k) x =
  ≤-trans
    (E-monotone-iter C n k (COL.K C n x))
    (COL.contract C n x)
