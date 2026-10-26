module DASHI.Mathematics.Symmetry.CrystalFourierLatticeD4hBridgeExact where

-- Reuse the literal Z^3 Fourier lattice owner from Navier-Stokes.
-- The point-group action is an integer signed-permutation action.
-- A reciprocal Fourier-mode lattice and an atomic position lattice
-- are different geometric objects; the same integer coordinate
-- action is valid on both only after lattice-basis compatibility.
-- No Bravais metric or measured diffraction claim is inferred.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Closure.NSIntegerFourierLattice as F
open import Data.Integer.Base using (ℤ)
open import Data.Integer using (-_)

R : F.FourierMode → F.FourierMode
R (F.mode x y z) = F.mode (- y) x z

S : F.FourierMode → F.FourierMode
S (F.mode x y z) = F.mode x (- y) z

H : F.FourierMode → F.FourierMode
H (F.mode x y z) = F.mode x y (- z)

-- Group relations over arbitrary integer variables require integer
-- arithmetic lemmas (especially negation involution), not reflexivity.
-- They are deliberately left out until linked to the existing
-- Data.Integer.Properties library and checked by the Agda kernel.
--
-- The source-level coordinate transformations remain useful, typed
-- executable definitions for the reciprocal-mode lattice carrier.
