module DASHI.Core.FiniteComponentEnergyAssemblyExact where

------------------------------------------------------------------------
-- FINITE COMPONENT ENERGY ASSEMBLY
--
-- Generic ordered-additive compiler:
--
--   component_i <= envelope_i  for every component
--
-- implies
--
--   sum component_i <= sum envelope_i.
--
-- This is the exact abstract step needed to assemble squared Fourier-shell
-- power bounds after an orthogonal/unitary decomposition.  It deliberately
-- reuses the repository's OrderedMonoid owner rather than defining a second
-- order algebra.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.MDL.MDLDescentTradeoff as Ordered

open Ordered.AddMonoid
open Ordered.OrderedMonoid

sum :
  ∀ {ℓ} →
  (O : Ordered.OrderedMonoid {ℓ}) →
  List (N (M O)) →
  N (M O)
sum O [] = 0# (M O)
sum O (x ∷ xs) = Ordered.AddMonoid._+_ (M O) x (sum O xs)

-- Length-aligned pointwise bounds.
data AlignedPointwiseBound
  {ℓ}
  (O : Ordered.OrderedMonoid {ℓ}) :
  List (N (M O)) →
  List (N (M O)) →
  Set ℓ where
  apb[] : AlignedPointwiseBound O [] []
  _apb∷_ :
    ∀ {x y xs ys} →
    Ordered.OrderedMonoid._≤_ O x y →
    AlignedPointwiseBound O xs ys →
    AlignedPointwiseBound O (x ∷ xs) (y ∷ ys)

pointwiseBoundSums :
  ∀ {ℓ}
    (O : Ordered.OrderedMonoid {ℓ})
    {xs ys : List (N (M O))} →
  AlignedPointwiseBound O xs ys →
  Ordered.OrderedMonoid._≤_ O (sum O xs) (sum O ys)
pointwiseBoundSums O apb[] =
  Ordered.OrderedMonoid.refl≤ O (0# (M O))
pointwiseBoundSums O (headBound apb∷ tailBounds) =
  Ordered.OrderedMonoid.mono+ O
    _ _ _ _
    headBound
    (pointwiseBoundSums O tailBounds)
