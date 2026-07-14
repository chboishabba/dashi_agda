module DASHI.Physics.Closure.NSTriadKNFiniteCoordinateAlgebraCore where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar

------------------------------------------------------------------------
-- Structural finite-coordinate primitives.
--
-- This deliberately knows nothing about shells, triads, or retained sectors.
-- Its explicit `Fin n` dimension means proofs may recurse on coordinates even
-- when a physical carrier's dimension is an opaque finite-list length.
------------------------------------------------------------------------

coordinateBasis :
  (S : Scalar.ExactOrderedScalar) → {n : Nat} →
  Fin n → Fin n → Scalar.Scalar S
coordinateBasis S {zero} () j
coordinateBasis S {suc n} zero zero = Scalar.one S
coordinateBasis S {suc n} zero (suc j) = Scalar.zero S
coordinateBasis S {suc n} (suc i) zero = Scalar.zero S
coordinateBasis S {suc n} (suc i) (suc j) = coordinateBasis S i j
