module DASHI.Physics.Photovoltaic.GaAs111BirPikusC3vFiniteExact where

-- FINITE spinless C3v covariance of a prescribed [111] Bir-Pikus orbital
-- strain tensor. Reuse the actual triadic/atomic [111] Cartesian owner.
-- The physical orbital energies, spin-orbit mixed double-group states,
-- deformation potentials and I-V response are NOT inferred from this file.
-- No local Agda Golden typecheck has been performed.
--
-- Source attribution:
-- Bir-Pikus (original strain symmetry); Bahder, PRB 41 (1990) 11992;
-- Vurgaftman et al., JAP 89 (2001) 5815;
-- OghmaNano Cartesian strain convention:
-- https://www.oghma-nano.com/manual/bir-pikus.html
--
-- For homogeneous axial tensor eps = eps_perp I + (eps_par-eps_perp)nn^T,
-- n=(1,1,1)/sqrt3, the XYZ valence strain block is
-- H_BP = av_eff Tr(eps) I + [d*(eps_par-eps_perp)/sqrt3](J-I).
-- This exact symbolic MATRIX ENTRY identity below does not assume b or d
-- values, actual wafer strain, or any spectral advantage.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact as T

-- Distinguish the common diagonal from the common off-diagonal shear.
-- This works for ANY coefficient carrier A and is thus a matrix-shape
-- theorem, not an optical/dipole/energy theorem.
bp111Entry : {A : Set} ->
  A -> A -> T.Cartesian -> T.Cartesian -> A
bp111Entry diagonal shear T.X T.X = diagonal
bp111Entry diagonal shear T.X T.Y = shear
bp111Entry diagonal shear T.X T.Z = shear
bp111Entry diagonal shear T.Y T.X = shear
bp111Entry diagonal shear T.Y T.Y = diagonal
bp111Entry diagonal shear T.Y T.Z = shear
bp111Entry diagonal shear T.Z T.X = shear
bp111Entry diagonal shear T.Z T.Y = shear
bp111Entry diagonal shear T.Z T.Z = diagonal

-- Rotating BOTH matrix indices by the physical Cartesian C3 action
-- preserves the source-qualified [111] orbital strain pattern.
bp111RotationCovariant : {A : Set} (diagonal shear : A) ->
  (i j : T.Cartesian) ->
  bp111Entry diagonal shear (T.rotate111 i) (T.rotate111 j)
  ≡ bp111Entry diagonal shear i j
bp111RotationCovariant diagonal shear T.X T.X = refl
bp111RotationCovariant diagonal shear T.X T.Y = refl
bp111RotationCovariant diagonal shear T.X T.Z = refl
bp111RotationCovariant diagonal shear T.Y T.X = refl
bp111RotationCovariant diagonal shear T.Y T.Y = refl
bp111RotationCovariant diagonal shear T.Y T.Z = refl
bp111RotationCovariant diagonal shear T.Z T.X = refl
bp111RotationCovariant diagonal shear T.Z T.Y = refl
bp111RotationCovariant diagonal shear T.Z T.Z = refl

-- The [111] orbital matrix also survives the Cartesian mirror Y <-> Z.
bp111MirrorCovariant : {A : Set} (diagonal shear : A) ->
  (i j : T.Cartesian) ->
  bp111Entry diagonal shear (T.mirror111 i) (T.mirror111 j)
  ≡ bp111Entry diagonal shear i j
bp111MirrorCovariant diagonal shear T.X T.X = refl
bp111MirrorCovariant diagonal shear T.X T.Y = refl
bp111MirrorCovariant diagonal shear T.X T.Z = refl
bp111MirrorCovariant diagonal shear T.Y T.X = refl
bp111MirrorCovariant diagonal shear T.Y T.Y = refl
bp111MirrorCovariant diagonal shear T.Y T.Z = refl
bp111MirrorCovariant diagonal shear T.Z T.X = refl
bp111MirrorCovariant diagonal shear T.Z T.Y = refl
bp111MirrorCovariant diagonal shear T.Z T.Z = refl

-- A [001] axial deformation with distinct longitudinal/transverse
-- diagonal symbols fails the same [111] C3 covariance in an actual entry.
-- This negative control prevents promoting all shear tensors to C3v.
data DiagonalSymbol : Set where
  transverse axial offdiag : DiagonalSymbol

bp001Entry : T.Cartesian -> T.Cartesian -> DiagonalSymbol
bp001Entry T.X T.X = transverse
bp001Entry T.X T.Y = offdiag
bp001Entry T.X T.Z = offdiag
bp001Entry T.Y T.X = offdiag
bp001Entry T.Y T.Y = transverse
bp001Entry T.Y T.Z = offdiag
bp001Entry T.Z T.X = offdiag
bp001Entry T.Z T.Y = offdiag
bp001Entry T.Z T.Z = axial

data False : Set where

bp001NotC3v :
  bp001Entry (T.rotate111 T.Y) (T.rotate111 T.Y)
    ≡ bp001Entry T.Y T.Y -> False
bp001NotC3v ()

-- The Cartesian [111] 3x3 A1 + E eigenvalue expression is analytically
-- diagonal + 2*shear on a1 and diagonal-shear on E. Proving the complex
-- normalized eigenbasis requires the separate SALC complex-field bridge.
-- Full spinful eight-state Kane/Bir-Pikus and Pmax still OPEN.
