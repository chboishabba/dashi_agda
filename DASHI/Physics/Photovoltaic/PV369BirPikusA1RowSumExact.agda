module DASHI.Physics.Photovoltaic.PV369BirPikusA1RowSumExact where

-- M3 reuse of ORIGINAL GaAs111BirPikusC3vFiniteExact [111] spinless
-- C3v strain operator. Each Cartesian row sum equals d+s+s on the
-- symmetric A1 direction. It is NOT an 8-band eigenenergy or physical
-- 369-specific improvement. No invented optical data. Golden OPEN.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)
open import Data.Nat.Properties as NatP using (+-assoc; +-comm)
import DASHI.Physics.Photovoltaic.Atomic369GaAs111TrigonalCharacterExact as T
import DASHI.Physics.Photovoltaic.GaAs111BirPikusC3vFiniteExact as BP
import DASHI.Physics.Photovoltaic.PV369P2CoulombSolarNonPromotionExact as Scalar

sourceA1RowSum : Nat -> Nat -> T.Cartesian -> Nat
sourceA1RowSum d s i =
  BP.bp111Entry d s i T.X +
    (BP.bp111Entry d s i T.Y + BP.bp111Entry d s i T.Z)

sourceA1UniformEigenrow : (d s : Nat) (i : T.Cartesian) ->
  sourceA1RowSum d s i ≡ d + (s + s)
sourceA1UniformEigenrow d s T.X = refl
sourceA1UniformEigenrow d s T.Y =
  Eq.trans (Eq.sym (NatP.+-assoc s d s))
    (Eq.trans
      (Eq.cong (λ x -> x + s) (NatP.+-comm s d))
      (NatP.+-assoc d s s))
sourceA1UniformEigenrow d s T.Z =
  Eq.trans (Eq.sym (NatP.+-assoc s s d))
    (NatP.+-comm (s + s) d)

commonScalarAdditionKeepsA1Shape :
  (d s h : Nat) (i : T.Cartesian) ->
  sourceA1RowSum (d + h) s i ≡ (d + h) + (s + s)
commonScalarAdditionKeepsA1Shape d s h =
  sourceA1UniformEigenrow (d + h) s

-- E doublet and signed eigenenergy are tested separately using original
-- source matrix in check_pv_369_bp111_scalar_coulomb_distinction.py.
-- Experimental GaAs QW, 8-band Kane/Bahder, optical transitions and
-- same-source loaded PV advantage remain OPEN physical obligations.
