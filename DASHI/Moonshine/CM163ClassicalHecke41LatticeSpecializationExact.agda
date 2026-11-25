module DASHI.Moonshine.CM163ClassicalHecke41LatticeSpecializationExact where

-- Source-written, uncompiled. Reuse the original PR #580 correspondence
-- carrier and the original SL2Z lattice point owner; this is the literal
-- row-basis lift, before taking the analytic modular quotient.
-- Classical prime-degree isogeny geometry: Diamond--Shurman (2005),
-- Broker--Lauter--Sutherland (2012), as cited in the original donor.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat.Properties renaming (_≟_ to nat≟)
open import Relation.Nullary using (yes; no)
open import Data.Integer using (ℤ; +_; 0ℤ; _+_; _-_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong₂)
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as H
import DASHI.Moonshine.PrimeRegularHeckeLocalGeometryExact as G
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as P

-- Ordered original lattice rows. No quotient by j, no fixed Vec15.
record Rows : Set where
  constructor rows
  field
    first second : L.LatticePoint
open Rows public

scale : ℤ → L.LatticePoint → L.LatticePoint
scale s (L.lattice-point m n) = L.lattice-point (s * m) (s * n)

add : L.LatticePoint → L.LatticePoint → L.LatticePoint
add (L.lattice-point m n) (L.lattice-point x y) =
  L.lattice-point (m + x) (n + y)

subtract : L.LatticePoint → L.LatticePoint → L.LatticePoint
subtract (L.lattice-point m n) (L.lattice-point x y) =
  L.lattice-point (m - x) (n - y)

p : ℤ
p = + 41

scaleRows : Rows → Rows
scaleRows (rows u v) = rows (scale p u) (scale p v)

finiteImage : Nat → Rows → Rows
finiteImage k (rows u v) = rows (add u (scale (+ k) v)) (scale p v)

infinityImage : Rows → Rows
infinityImage (rows u v) = rows (scale p u) v

chartImage : Fin 42 → Rows → Rows
chartImage i r with nat≟ (toℕ i) 41
... | yes _ = infinityImage r
... | no _ = finiteImage (toℕ i) r

-- The original variable-degree record, specialized rather than replaced.
correspondence41 : H.ClassicalPrimeDegreeCorrespondence Rows
correspondence41 = record
  { H.degreePrime = 41
  ; H.neighbour = λ r i → chartImage i r
  }

local41 : G.PrimeRegularHeckeLocalGeometry Rows 41
local41 = record { G.neighbour = H.neighbour correspondence41 }

actualArity : G.localArity local41 ≡ 42
actualArity = refl

positiveReadoutSame :
  (observable : Rows → Nat) (r : Rows) →
  P.positiveOperator (G.asPositiveNeighbourSystem local41) observable r
    ≡ H.classicalOperator correspondence41 observable r
positiveReadoutSame observable r = refl

-- Use the ORIGINAL finite fold for a multiplicative readout as well.
-- The analytic value and ring operations are supplied by their owner.
-- This is the norm/product, not the additive Hecke operator.
characteristicProduct :
  ∀ {A : Set} → (A → A → A) → A → (Rows → A) → Rows → A
characteristicProduct mul one factor r =
  H.foldFin mul one (λ i → factor (H.neighbour correspondence41 r i))

-- Dual index plus its integral correction, retaining original chart k.
-- After dual transport the row basis is multiplied by 41, not equal
-- as an ordered integer basis. Only the analytic projective chart forgets
-- that common scale.
finiteCorrection : Nat → Rows → Rows
finiteCorrection k (rows u v) = rows (subtract u (scale (+ k) v)) v

dualIndex : Fin 42 → Fin 42
dualIndex i with nat≟ (toℕ i) 41
... | yes _ = Fin.zero
... | no _ = Fin.fromℕ 41

dualCorrect : Fin 42 → Rows → Rows
dualCorrect i r with nat≟ (toℕ i) 41
... | yes _ = r
... | no _ = finiteCorrection (toℕ i) r

finiteReverseCoordinate : (k m n : ℤ) →
  p * (m + k * n) - k * (p * n) ≡ p * m
finiteReverseCoordinate k m n =
  solve 3 (λ k′ m′ n′ →
    con p :* (m′ :+ k′ :* n′) :- k′ :* (con p :* n′)
      := con p :* m′) refl k m n

finiteReverse : (k : Nat) (r : Rows) →
  finiteCorrection k (infinityImage (finiteImage k r)) ≡ scaleRows r
finiteReverse k (rows (L.lattice-point m n) (L.lattice-point x y)) =
  cong₂ rows
    (L.lattice-ext (finiteReverseCoordinate (+ k) m x)
                   (finiteReverseCoordinate (+ k) n y)) refl

zeroAddCoordinate : (m n : ℤ) → m + 0ℤ * n ≡ m
zeroAddCoordinate m n =
  solve 2 (λ m′ n′ → m′ :+ con 0ℤ :* n′ := m′) refl m n

infinityReverse : (r : Rows) →
  finiteImage 0 (infinityImage r) ≡ scaleRows r
infinityReverse (rows (L.lattice-point m n) (L.lattice-point x y)) =
  cong₂ rows
    (L.lattice-ext (zeroAddCoordinate (p * m) x)
                   (zeroAddCoordinate (p * n) y)) refl

-- The two literal closed index cases reduce through the same chartImage.
-- General dual coordinate arithmetic above does not assume j invariance.
chartZero : (r : Rows) → chartImage Fin.zero r ≡ finiteImage 0 r
chartZero r = refl

chartInfinity : (r : Rows) → chartImage (Fin.fromℕ 41) r ≡ infinityImage r
chartInfinity r = refl

dualReconstruction : (i : Fin 42) (r : Rows) →
  dualCorrect i (chartImage (dualIndex i) (chartImage i r)) ≡ scaleRows r
dualReconstruction i r with nat≟ (toℕ i) 41
... | yes _ = infinityReverse r
... | no _ = finiteReverse (toℕ i) r

-- Actual upper-half-plane/lattice same-object and product Laurent pole
-- removal remain analytical obligations. This module does not infer them
-- from finite arity or from the additive Hecke eigenvalue algebra.
