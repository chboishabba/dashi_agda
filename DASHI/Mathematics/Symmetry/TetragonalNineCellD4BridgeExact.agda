module DASHI.Mathematics.Symmetry.TetragonalNineCellD4BridgeExact where

-- Reuses the original nine-cell D4 owner, not an invented bijection
-- with the eight-site height carrier. These maps preserve rotation
-- and reflection separately on the edge orbit.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.D4NineCellOrbitCompressionExact as Grid
import DASHI.Mathematics.Symmetry.TetragonalD4hGeneratorActionExact as Geo

edge : Geo.Direction → Grid.NineCell
edge Geo.north = Grid.north
edge Geo.east = Grid.east
edge Geo.south = Grid.south
edge Geo.west = Grid.west

edgeRotation : (d : Geo.Direction) →
  edge (Geo.quarter d) ≡ Grid.rotate90 (edge d)
edgeRotation Geo.north = refl
edgeRotation Geo.east = refl
edgeRotation Geo.south = refl
edgeRotation Geo.west = refl

edgeReflection : (d : Geo.Direction) →
  edge (Geo.mirror d) ≡ Grid.reflectVertical (edge d)
edgeReflection Geo.north = refl
edgeReflection Geo.east = refl
edgeReflection Geo.south = refl
edgeReflection Geo.west = refl

-- Both height layers map to the same edge orbit.
-- This projection forgets height and cannot be a site equivalence.
forgetHeight : Geo.Site → Grid.NineCell
forgetHeight (Geo.site d h) = edge d

forgetHeightR : (p : Geo.Site) →
  forgetHeight (Geo.R p) ≡ Grid.rotate90 (forgetHeight p)
forgetHeightR (Geo.site Geo.north Geo.above) = refl
forgetHeightR (Geo.site Geo.east Geo.above) = refl
forgetHeightR (Geo.site Geo.south Geo.above) = refl
forgetHeightR (Geo.site Geo.west Geo.above) = refl
forgetHeightR (Geo.site Geo.north Geo.below) = refl
forgetHeightR (Geo.site Geo.east Geo.below) = refl
forgetHeightR (Geo.site Geo.south Geo.below) = refl
forgetHeightR (Geo.site Geo.west Geo.below) = refl

forgetHeightS : (p : Geo.Site) →
  forgetHeight (Geo.S p) ≡ Grid.reflectVertical (forgetHeight p)
forgetHeightS (Geo.site Geo.north Geo.above) = refl
forgetHeightS (Geo.site Geo.east Geo.above) = refl
forgetHeightS (Geo.site Geo.south Geo.above) = refl
forgetHeightS (Geo.site Geo.west Geo.above) = refl
forgetHeightS (Geo.site Geo.north Geo.below) = refl
forgetHeightS (Geo.site Geo.east Geo.below) = refl
forgetHeightS (Geo.site Geo.south Geo.below) = refl
forgetHeightS (Geo.site Geo.west Geo.below) = refl

forgetHeightH : (p : Geo.Site) →
  forgetHeight (Geo.H p) ≡ forgetHeight p
forgetHeightH (Geo.site d Geo.above) = refl
forgetHeightH (Geo.site d Geo.below) = refl
