module DASHI.Mathematics.Symmetry.DiamondNVOrderedBondStabilizerExact where

-- Geometric stabiliser of a chosen oriented diamond bond:
-- A origin at (0,0,0), B nearest-neighbour at (1,1,1)
-- (quarter conventional cubic cell units).
-- This is S3 ≅ C3v on spatial coordinates, and NOT an assertion
-- of cyclic permutation symmetry on m_s = -1,0,+1 spin states.
-- Attribution: IUCr Fd-3m (227), classical C3v site symmetry;
-- PR #1238 owns existing four NV axis labels; PR #1262 owns
-- the separate spin-one Sz² cyclic-label obstruction.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _*_)\nopen import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Integer.Properties as IntP

import DASHI.Mathematics.Symmetry.DiamondFccPrimitiveGlideExact as FCC
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as L
import DASHI.Mathematics.Symmetry.DiamondNVFourAxisPermutationExact as NV

cyclePrimitive : FCC.PrimitiveFcc → FCC.PrimitiveFcc
cyclePrimitive (FCC.primitive p q r) = FCC.primitive q r p

cycleSite : FCC.DiamondSite → FCC.DiamondSite
cycleSite (FCC.A p) = FCC.A (cyclePrimitive p)
cycleSite (FCC.B p) = FCC.B (cyclePrimitive p)

reflectSite : FCC.DiamondSite → FCC.DiamondSite
reflectSite = FCC.swapXYSite

cyclePoint : L.Triple ℤ → L.Triple ℤ
cyclePoint (L.xyz x y z) = L.xyz y z x

cyclePrimitivePosition : (p : FCC.PrimitiveFcc) →
  FCC.fccPoint (cyclePrimitive p) ≡
  cyclePoint (FCC.fccPoint p)
cyclePrimitivePosition (FCC.primitive p q r) =
  FCC.tripleExt
    (cong ((+ 2) *_) (IntP.+-comm r p))
    (cong ((+ 2) *_) (IntP.+-comm q p))
    refl

cycleSitePosition : (s : FCC.DiamondSite) →
  FCC.sitePosition (cycleSite s) ≡
  cyclePoint (FCC.sitePosition s)
cycleSitePosition (FCC.A p) = cyclePrimitivePosition p
cycleSitePosition (FCC.B p) =
  cong FCC.quarterDelta (cyclePrimitivePosition p)

cycleSite3 : (s : FCC.DiamondSite) →
  cycleSite (cycleSite (cycleSite s)) ≡ s
cycleSite3 (FCC.A (FCC.primitive p q r)) = refl
cycleSite3 (FCC.B (FCC.primitive p q r)) = refl

reflectSite2 : (s : FCC.DiamondSite) →
  reflectSite (reflectSite s) ≡ s
reflectSite2 (FCC.A (FCC.primitive p q r)) = refl
reflectSite2 (FCC.B (FCC.primitive p q r)) = refl

reflectCycleReflect : (s : FCC.DiamondSite) →
  reflectSite (cycleSite (reflectSite s)) ≡
  cycleSite (cycleSite s)
reflectCycleReflect (FCC.A (FCC.primitive p q r)) = refl
reflectCycleReflect (FCC.B (FCC.primitive p q r)) = refl

aOrigin : FCC.DiamondSite
aOrigin = FCC.A (FCC.primitive (+ 0) (+ 0) (+ 0))

bBond : FCC.DiamondSite
bBond = FCC.B (FCC.primitive (+ 0) (+ 0) (+ 0))

cycleFixesOrigin : cycleSite aOrigin ≡ aOrigin
cycleFixesOrigin = refl

cycleFixesBond : cycleSite bBond ≡ bBond
cycleFixesBond = refl

reflectFixesOrigin : reflectSite aOrigin ≡ aOrigin
reflectFixesOrigin = refl

reflectFixesBond : reflectSite bBond ≡ bBond
reflectFixesBond = refl

-- Six coordinate permutations fixing both physical positions.
-- This finite six-label carrier has a manifest geometric action.
data BondC3v : Set where
  id c c2 s sc sc2 : BondC3v

actBond : BondC3v → FCC.DiamondSite → FCC.DiamondSite
actBond id p = p
actBond c p = cycleSite p
actBond c2 p = cycleSite (cycleSite p)
actBond s p = reflectSite p
actBond sc p = reflectSite (cycleSite p)
actBond sc2 p = reflectSite (cycleSite (cycleSite p))

bondOperationsFixBoth :
  (g : BondC3v) →
  actBond g aOrigin ≡ aOrigin
  × actBond g bBond ≡ bBond
bondOperationsFixBoth id = refl , refl
bondOperationsFixBoth c = refl , refl
bondOperationsFixBoth c2 = refl , refl
bondOperationsFixBoth s = refl , refl
bondOperationsFixBoth sc = refl , refl
bondOperationsFixBoth sc2 = refl , refl

-- Important: this fixes the *ordered atomic-site pair*. A real NV
-- centre requires species (N/C/vacancy), electronic Hamiltonian,
-- strain, magnetic field and orientation witnesses. This statement
-- alone says nothing about the apparatus's spectrum.
