module DASHI.Mathematics.Symmetry.CrystalPointGroup32CatalogExact where

-- IUCr/International Tables crystallographic point-group names.
-- This is a 32-label exhaustive catalog, not 32 constructed
-- matrix groups or 230 space-group proofs. Classical source attribution
-- belongs to IUCr; DASHI supplies this typed catalogue.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Mathematics.Symmetry.CrystalClassificationSevenFourteenExact as C

data CrystalPointGroup : Set where
  pg1 pgBar1 : CrystalPointGroup
  pg2 pgM pg2OverM : CrystalPointGroup
  pg222 pgMM2 pgMMM : CrystalPointGroup
  pg4 pgBar4 pg4OverM pg422 pg4MM pgBar42M pg4OverMMM : CrystalPointGroup
  pg3 pgBar3 pg32 pg3M pgBar3M : CrystalPointGroup
  pg6 pgBar6 pg6OverM pg622 pg6MM pgBar6M2 pg6OverMMM : CrystalPointGroup
  pg23 pgMBar3 pg432 pgBar43M pgMBar3M : CrystalPointGroup

crystalSystem : CrystalPointGroup → C.CrystalSystem
crystalSystem pg1 = C.triclinic
crystalSystem pgBar1 = C.triclinic
crystalSystem pg2 = C.monoclinic
crystalSystem pgM = C.monoclinic
crystalSystem pg2OverM = C.monoclinic
crystalSystem pg222 = C.orthorhombic
crystalSystem pgMM2 = C.orthorhombic
crystalSystem pgMMM = C.orthorhombic
crystalSystem pg4 = C.tetragonal
crystalSystem pgBar4 = C.tetragonal
crystalSystem pg4OverM = C.tetragonal
crystalSystem pg422 = C.tetragonal
crystalSystem pg4MM = C.tetragonal
crystalSystem pgBar42M = C.tetragonal
crystalSystem pg4OverMMM = C.tetragonal
crystalSystem pg3 = C.trigonal
crystalSystem pgBar3 = C.trigonal
crystalSystem pg32 = C.trigonal
crystalSystem pg3M = C.trigonal
crystalSystem pgBar3M = C.trigonal
crystalSystem pg6 = C.hexagonal
crystalSystem pgBar6 = C.hexagonal
crystalSystem pg6OverM = C.hexagonal
crystalSystem pg622 = C.hexagonal
crystalSystem pg6MM = C.hexagonal
crystalSystem pgBar6M2 = C.hexagonal
crystalSystem pg6OverMMM = C.hexagonal
crystalSystem pg23 = C.cubic
crystalSystem pgMBar3 = C.cubic
crystalSystem pg432 = C.cubic
crystalSystem pgBar43M = C.cubic
crystalSystem pgMBar3M = C.cubic

tetragonalD4hIsTetragonal :
  crystalSystem pg4OverMMM ≡ C.tetragonal
tetragonalD4hIsTetragonal = refl

-- Counts: 2+3+3+7+5+7+5=32.
-- Must not conflate an abstract finite-group isomorphism with the
-- embedded point-group class, lattice compatibility, or Seitz space group.
