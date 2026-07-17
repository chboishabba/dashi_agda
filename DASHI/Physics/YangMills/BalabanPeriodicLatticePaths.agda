module DASHI.Physics.YangMills.BalabanPeriodicLatticePaths where

------------------------------------------------------------------------
-- Indexed paths on the literal periodic four-dimensional bond carrier.
--
-- The endpoints are encoded in the type, so only composable bond sequences
-- can be constructed.  Concatenation and reversal are proved directly from
-- the periodic bond-reversal lemmas.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( DirectedBond4
  ; source
  ; target
  ; reverseBond
  ; reverseTargetIsSource
  )

infixr 35 _▷_

data LatticePath4 {N : Nat} {{_ : NonZero N}} :
  Cube4 N → Cube4 N → Set where
  empty :
    ∀ {x} →
    LatticePath4 x x

  _▷_ :
    (b : DirectedBond4 N) →
    ∀ {y} →
    LatticePath4 (target b) y →
    LatticePath4 (source b) y

single :
  ∀ {N : Nat} {{_ : NonZero N}}
  (b : DirectedBond4 N) →
  LatticePath4 (source b) (target b)
single b = b ▷ empty

append :
  ∀ {N : Nat} {{_ : NonZero N}} {x y z : Cube4 N} →
  LatticePath4 x y →
  LatticePath4 y z →
  LatticePath4 x z
append empty q = q
append (b ▷ p) q = b ▷ append p q

appendEmptyRight :
  ∀ {N : Nat} {{_ : NonZero N}} {x y : Cube4 N}
  (p : LatticePath4 x y) →
  append p empty ≡ p
appendEmptyRight empty = refl
appendEmptyRight (b ▷ p) =
  cong (λ q → b ▷ q) (appendEmptyRight p)

appendAssociative :
  ∀ {N : Nat} {{_ : NonZero N}}
  {w x y z : Cube4 N}
  (p : LatticePath4 w x)
  (q : LatticePath4 x y)
  (r : LatticePath4 y z) →
  append (append p q) r ≡ append p (append q r)
appendAssociative empty q r = refl
appendAssociative (b ▷ p) q r =
  cong (λ s → b ▷ s) (appendAssociative p q r)

pathLength :
  ∀ {N : Nat} {{_ : NonZero N}} {x y : Cube4 N} →
  LatticePath4 x y → Nat
pathLength empty = zero
pathLength (b ▷ p) = suc (pathLength p)

pathLengthAppend :
  ∀ {N : Nat} {{_ : NonZero N}}
  {x y z : Cube4 N}
  (p : LatticePath4 x y)
  (q : LatticePath4 y z) →
  pathLength (append p q) ≡ pathLength p + pathLength q
pathLengthAppend empty q = refl
pathLengthAppend (b ▷ p) q =
  cong suc (pathLengthAppend p q)

transportEndpoint :
  ∀ {N : Nat} {{_ : NonZero N}}
  {x y z : Cube4 N} →
  y ≡ z →
  LatticePath4 x y →
  LatticePath4 x z
transportEndpoint eq p = subst (LatticePath4 _) eq p

reverseSingle :
  ∀ {N : Nat} {{_ : NonZero N}}
  (b : DirectedBond4 N) →
  LatticePath4 (target b) (source b)
reverseSingle b =
  transportEndpoint
    (reverseTargetIsSource b)
    (single (reverseBond b))

reversePath :
  ∀ {N : Nat} {{_ : NonZero N}}
  {x y : Cube4 N} →
  LatticePath4 x y →
  LatticePath4 y x
reversePath empty = empty
reversePath (b ▷ p) =
  append (reversePath p) (reverseSingle b)
