module DASHI.Physics.ThreeBody.State where

------------------------------------------------------------------------
-- Compile-thin state carrier for a three-body system.

record Triple (A : Set) : Set where
  constructor mkTriple
  field
    first : A
    second : A
    third : A

open Triple public

record ThreeBodyState
  (Coord : Set)
  (Scalar : Set)
  : Set where
  constructor mkThreeBodyState
  field
    positions : Triple Coord
    velocities : Triple Coord
    masses : Triple Scalar

open ThreeBodyState public
