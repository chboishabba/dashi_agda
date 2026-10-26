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

R4 : (p : F.FourierMode) → R (R (R (R p))) ≡ p
R4 (F.mode x y z) = refl

S2 : (p : F.FourierMode) → S (S p) ≡ p
S2 (F.mode x y z) = refl

H2 : (p : F.FourierMode) → H (H p) ≡ p
H2 (F.mode x y z) = refl

SRS : (p : F.FourierMode) → S (R (S p)) ≡ R (R (R p))
SRS (F.mode x y z) = refl

HR : (p : F.FourierMode) → H (R p) ≡ R (H p)
HR (F.mode x y z) = refl

HS : (p : F.FourierMode) → H (S p) ≡ S (H p)
HS (F.mode x y z) = refl

-- Direct sum representation supplies the faithful integer action
-- on coordinate triples; embedding into a concrete crystallographic
-- lattice still requires metric and basis preservation witnesses.
