module DASHI.Philosophy.RelationalAtlas where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- A local chart normalises a situated region and can reconstruct points in
-- its declared domain.

record Chart (X Coordinate : Set) : Set₁ where
  field
    Domain :
      X →
      Set

    normalise :
      X →
      Coordinate

    denormalise :
      Coordinate →
      X

    localRetraction :
      (x : X) →
      Domain x →
      denormalise (normalise x) ≡ x

open Chart public

record ChartTransition
       {X Coordinate : Set}
       (source target : Chart X Coordinate) : Set₁ where
  field
    Overlap :
      X →
      Set

    transition :
      Coordinate →
      Coordinate

    compatibleOnOverlap :
      (x : X) →
      Overlap x →
      transition (normalise source x)
      ≡
      normalise target x

open ChartTransition public

------------------------------------------------------------------------
-- Solidarity is workable translation among situated charts, not identity of
-- standpoints.

record RelationalAtlas (X Coordinate : Set) : Set₁ where
  field
    ChartIndex :
      Set

    chart :
      ChartIndex →
      Chart X Coordinate

    transition :
      (i j : ChartIndex) →
      ChartTransition (chart i) (chart j)

    collectiveUnderstanding :
      Set

    identicalStandpointsRequired :
      Bool

    materialOrganisationPresent :
      Bool

open RelationalAtlas public

record SolidarityBoundary
       {X Coordinate : Set}
       (atlas : RelationalAtlas X Coordinate) : Set₁ where
  field
    transitionsWork :
      Set

    voicesRemainDistinct :
      Set

    noForcedIdentity :
      identicalStandpointsRequired atlas ≡ false

open SolidarityBoundary public
