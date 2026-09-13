module DASHI.Wikimedia.IbrahimG2SevenTwentyNineOEISNegativeControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine

------------------------------------------------------------------------
-- OEIS NEGATIVE CONTROL: G2 729 VS MONSTER/HEISENBERG 729
--
-- A104599 lists irreducible G2 representation dimensions and contains 729.
-- DASHI independently owns 729 = 3^6 as the finite Heisenberg/Stone-von
-- Neumann model degree.  The shared integer is therefore admissible for
-- all-pairs comparison, but it does not identify the representation carriers.
------------------------------------------------------------------------

monsterHeisenberg729 : Nat
monsterHeisenberg729 = 729

monsterHeisenberg729IsThreePowerSix : Nine.a000244 6 ≡ monsterHeisenberg729
monsterHeisenberg729IsThreePowerSix = refl

record G2OEISCoordinate : Set where
  constructor g2-oeis-coordinate
  field
    g2Qid : String
    g2IrrepDimensionOEIS : String
    sharedValue : Nat
    oeisRole : String
    sameNumberCreatesSameRepresentation : Bool
open G2OEISCoordinate public

canonicalG2OEISCoordinate : G2OEISCoordinate
canonicalG2OEISCoordinate = g2-oeis-coordinate
  "Q869338"
  "A104599"
  729
  "A104599 contains 729 as a G2 irreducible-representation dimension; DASHI Monster uses 729 independently as the finite Heisenberg/Stone-von Neumann degree"
  false

data G2SevenTwentyNineIdentifiesMonsterHeisenberg : Set where
data Shared729CreatesIntertwiner : Set where

g2SevenTwentyNineDoesNotIdentifyMonster :
  G2SevenTwentyNineIdentifiesMonsterHeisenberg → ⊥
g2SevenTwentyNineDoesNotIdentifyMonster ()

shared729DoesNotCreateIntertwiner : Shared729CreatesIntertwiner → ⊥
shared729DoesNotCreateIntertwiner ()

record G2SevenTwentyNineNegativeControlBoundary : Set where
  constructor g2-seven-twenty-nine-negative-control-boundary
  field
    monster729AsThreePowerSixPaid : Bool
    g2A104599Contains729Externally : Bool
    g2QidPaid : Bool
    repoHasSameObjectG2Monster729ActionBridge : Bool
    sharedNumeralPromotesRepresentationIdentity : Bool
    hypothesisTestDisposition : String
open G2SevenTwentyNineNegativeControlBoundary public

canonicalG2SevenTwentyNineNegativeControlBoundary :
  G2SevenTwentyNineNegativeControlBoundary
canonicalG2SevenTwentyNineNegativeControlBoundary =
  g2-seven-twenty-nine-negative-control-boundary
    true true true false false
    "retain as a negative calibration fixture: same OEIS representation dimension is insufficient; reopen only if an independent G2-to-Heisenberg action/intertwiner source appears"
