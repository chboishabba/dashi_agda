module DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact where

------------------------------------------------------------------------
-- SL2(Z) REINDEXING OF THE PUNCTURED INTEGER LATTICE
--
-- The legacy lattice theorem proves a bijection on all Z^2.  Classical
-- Eisenstein series use Z^2 \ {(0,0)}.  This owner proves that the same forward
-- and inverse index maps preserve the puncture, rather than inserting a fake
-- value at the origin.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

import Real as BishopReal

import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

inverseOrigin :
  (g : Lattice.SL2Z) →
  Lattice.inverseIndex g Kernel.origin ≡ Kernel.origin
inverseOrigin g =
  Lattice.lattice-ext
    (solve 4
      (λ a b c d →
        (Κ 0ℤ :* d :- Κ 0ℤ :* c) := Κ 0ℤ)
      refl
      (Lattice.a g) (Lattice.b g) (Lattice.c g) (Lattice.d g))
    (solve 4
      (λ a b c d →
        ((:- Κ 0ℤ) :* b :+ Κ 0ℤ :* a) := Κ 0ℤ)
      refl
      (Lattice.a g) (Lattice.b g) (Lattice.c g) (Lattice.d g))

forwardOrigin :
  (g : Lattice.SL2Z) →
  Lattice.forwardIndex g Kernel.origin ≡ Kernel.origin
forwardOrigin g =
  Lattice.lattice-ext
    (solve 4
      (λ a b c d →
        (Κ 0ℤ :* a :+ Κ 0ℤ :* c) := Κ 0ℤ)
      refl
      (Lattice.a g) (Lattice.b g) (Lattice.c g) (Lattice.d g))
    (solve 4
      (λ a b c d →
        (Κ 0ℤ :* b :+ Κ 0ℤ :* d) := Κ 0ℤ)
      refl
      (Lattice.a g) (Lattice.b g) (Lattice.c g) (Lattice.d g))

forwardReflectsOrigin :
  (g : Lattice.SL2Z) →
  (p : Lattice.LatticePoint) →
  Lattice.forwardIndex g p ≡ Kernel.origin →
  p ≡ Kernel.origin
forwardReflectsOrigin g p forwardIsOrigin =
  trans
    (sym (Lattice.inverseForward g p))
    (trans
      (cong (Lattice.inverseIndex g) forwardIsOrigin)
      (inverseOrigin g))

inverseReflectsOrigin :
  (g : Lattice.SL2Z) →
  (p : Lattice.LatticePoint) →
  Lattice.inverseIndex g p ≡ Kernel.origin →
  p ≡ Kernel.origin
inverseReflectsOrigin g p inverseIsOrigin =
  trans
    (sym (Lattice.forwardInverse g p))
    (trans
      (cong (Lattice.forwardIndex g) inverseIsOrigin)
      (forwardOrigin g))

forwardPunctured :
  Lattice.SL2Z →
  Kernel.NonzeroLatticePoint →
  Kernel.NonzeroLatticePoint
forwardPunctured g index =
  Kernel.nonzero-lattice-point
    (Lattice.forwardIndex g (Kernel.point index))
    (λ forwardIsOrigin →
      Kernel.notOrigin index
        (forwardReflectsOrigin g (Kernel.point index) forwardIsOrigin))

inversePunctured :
  Lattice.SL2Z →
  Kernel.NonzeroLatticePoint →
  Kernel.NonzeroLatticePoint
inversePunctured g index =
  Kernel.nonzero-lattice-point
    (Lattice.inverseIndex g (Kernel.point index))
    (λ inverseIsOrigin →
      Kernel.notOrigin index
        (inverseReflectsOrigin g (Kernel.point index) inverseIsOrigin))

inverseForwardPoint :
  (g : Lattice.SL2Z) →
  (index : Kernel.NonzeroLatticePoint) →
  Kernel.point (inversePunctured g (forwardPunctured g index))
  ≡ Kernel.point index
inverseForwardPoint g index =
  Lattice.inverseForward g (Kernel.point index)

forwardInversePoint :
  (g : Lattice.SL2Z) →
  (index : Kernel.NonzeroLatticePoint) →
  Kernel.point (forwardPunctured g (inversePunctured g index))
  ≡ Kernel.point index
forwardInversePoint g index =
  Lattice.forwardInverse g (Kernel.point index)

record PuncturedLatticeBijection (g : Lattice.SL2Z) : Set where
  field
    forward : Kernel.NonzeroLatticePoint → Kernel.NonzeroLatticePoint
    backward : Kernel.NonzeroLatticePoint → Kernel.NonzeroLatticePoint
    backwardForwardPoint :
      (index : Kernel.NonzeroLatticePoint) →
      Kernel.point (backward (forward index)) ≡ Kernel.point index
    forwardBackwardPoint :
      (index : Kernel.NonzeroLatticePoint) →
      Kernel.point (forward (backward index)) ≡ Kernel.point index

open PuncturedLatticeBijection public

sl2zPuncturedLatticeBijection :
  (g : Lattice.SL2Z) →
  PuncturedLatticeBijection g
sl2zPuncturedLatticeBijection g = record
  { forward = forwardPunctured g
  ; backward = inversePunctured g
  ; backwardForwardPoint = inverseForwardPoint g
  ; forwardBackwardPoint = forwardInversePoint g
  }
