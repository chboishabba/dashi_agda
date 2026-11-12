module DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP COMPLEX INVERSE-KOENIGS FINITE ORBIT.
--
-- For ANY concrete endomap g on the actual BishopComplex carrier,
-- and ANY multiplier p, define
--
--     h_n(z) = p^n *C (g^n(z) -C p).
--
-- The orbit recursion is deliberately right-oriented:
--     orbit_(n+1)(z) = orbit_n(g(z))
-- so the shift is definitional, without pretending an arbitrary g
-- respects componentwise Bishop setoid equivalence.
--
-- The key finite relation is proved:
--     p *C h_n(g(z)) ≈C h_(n+1)(z).
--
-- This is the exact finite identity needed for inverse Koenigs
-- convergence. It neither assumes g=Log is a contraction nor
-- assumes that p is an exp fixed point. The next owner must prove
-- the original Bishop log branch, invariant disk, genuine Cauchy
-- modulus, and pass this relation to the limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws

inverseOrbit :
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  Nat → Complex.BishopComplex → Complex.BishopComplex
inverseOrbit g zero z = z
inverseOrbit g (suc n) z = inverseOrbit g n (g z)

inverseOrbitSuccessor :
  ∀ (g : Complex.BishopComplex → Complex.BishopComplex) n z →
  inverseOrbit g (suc n) z ≡ inverseOrbit g n (g z)
inverseOrbitSuccessor g n z = refl

inverseKoenigsPrefix :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  Nat → Complex.BishopComplex → Complex.BishopComplex
inverseKoenigsPrefix p g n z =
  Algebra._*C_
    (Algebra.powC p n)
    (Algebra._-C_ (inverseOrbit g n z) p)

-- Unlike the forward-iteration formula for an attracting fixed point,
-- this uses powers p^n on the iterates of the inverse branch g.
inverseKoenigsPrefixStep :
  ∀ p g n z →
  Complex._≈C_
    (Algebra._*C_
      p
      (inverseKoenigsPrefix p g n (g z)))
    (inverseKoenigsPrefix p g (suc n) z)
inverseKoenigsPrefixStep p g n z =
  let associative =
        Laws.complexMultiplyAssociative
          p
          (Algebra.powC p n)
          (Algebra._-C_ (inverseOrbit g n (g z)) p)
  in
  BishopP.≃-symm (proj₁ associative)
  ,
  BishopP.≃-symm (proj₂ associative)

-- Fixpoints of g give a constant orbit point exactly, with
-- no assumption about analytic differentiability or modulus.
inverseOrbitAtDefinitionalFixedPoint :
  ∀ (g : Complex.BishopComplex → Complex.BishopComplex)
    (p : Complex.BishopComplex) →
  g p ≡ p →
  ∀ n →
  inverseOrbit g n p ≡ p
inverseOrbitAtDefinitionalFixedPoint g p fixed zero = refl
inverseOrbitAtDefinitionalFixedPoint g p fixed (suc n)
  rewrite fixed = inverseOrbitAtDefinitionalFixedPoint g p fixed n
