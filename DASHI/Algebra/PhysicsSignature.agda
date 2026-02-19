module DASHI.Algebra.PhysicsSignature where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos using (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

-- A 15-bit signature (exactly your existing shape).
record Sig15 : Set where
  constructor sig15
  field
    b2  : Bool; b3  : Bool; b5  : Bool; b7  : Bool; b11 : Bool
    b13 : Bool; b17 : Bool; b19 : Bool; b23 : Bool; b29 : Bool
    b31 : Bool; b41 : Bool; b47 : Bool; b59 : Bool; b71 : Bool

-- Physics “state” is abstract here; you can later:
--   (a) define it constructively, or
--   (b) import it from a computed table (recommended for closure).
postulate
  State : Set

-- A “compatibility detector” is the *lens*:
-- tells you whether prime p is compatible with state s under your rules.
record Lens : Set₁ where
  field
    Compat : SSP → State → Bool

open Lens public

scan : Lens → State → Sig15
scan L s = sig15
  (Compat L p2  s) (Compat L p3  s) (Compat L p5  s) (Compat L p7  s) (Compat L p11 s)
  (Compat L p13 s) (Compat L p17 s) (Compat L p19 s) (Compat L p23 s) (Compat L p29 s)
  (Compat L p31 s) (Compat L p41 s) (Compat L p47 s) (Compat L p59 s) (Compat L p71 s)
