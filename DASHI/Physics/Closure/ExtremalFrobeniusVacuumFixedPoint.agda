module DASHI.Physics.Closure.ExtremalFrobeniusVacuumFixedPoint where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import MonsterOntos using (SSP; p47; p59; p71)
import Ontology.GodelLattice as GL
import DASHI.Statistics.Vec15Order as Vec15Order

------------------------------------------------------------------------
-- +1 extremal Frobenius vacuum slice over the 15-prime carrier.

zeroVec15 :
  GL.Vec15 Nat
zeroVec15 =
  Vec15Order.zeroCarrier15

zeroFactorVec :
  GL.FactorVec
zeroFactorVec =
  zeroVec15

data ExtremalFrobeniusLane : Set where
  frobenius-p47 :
    ExtremalFrobeniusLane

  frobenius-p59 :
    ExtremalFrobeniusLane

  frobenius-p71 :
    ExtremalFrobeniusLane

extremalFrobeniusLanePrime :
  ExtremalFrobeniusLane →
  SSP
extremalFrobeniusLanePrime frobenius-p47 =
  p47
extremalFrobeniusLanePrime frobenius-p59 =
  p59
extremalFrobeniusLanePrime frobenius-p71 =
  p71

-- The three extremal lane actions are explicit Vec15 coordinate
-- permutations on the p47/p59/p71 tail.  No uniqueness or
-- fixed-point-free nonzero claim is made here.

frobeniusP47Action :
  GL.FactorVec →
  GL.FactorVec
frobeniusP47Action
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e59 e47 e71

frobeniusP59Action :
  GL.FactorVec →
  GL.FactorVec
frobeniusP59Action
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e71 e59

frobeniusP71Action :
  GL.FactorVec →
  GL.FactorVec
frobeniusP71Action
  (GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) =
  GL.v15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e71 e59 e47

extremalFrobeniusLaneAction :
  ExtremalFrobeniusLane →
  GL.FactorVec →
  GL.FactorVec
extremalFrobeniusLaneAction frobenius-p47 =
  frobeniusP47Action
extremalFrobeniusLaneAction frobenius-p59 =
  frobeniusP59Action
extremalFrobeniusLaneAction frobenius-p71 =
  frobeniusP71Action

combinedExtremalFrobeniusAction :
  GL.FactorVec →
  GL.FactorVec
combinedExtremalFrobeniusAction v =
  frobeniusP71Action
    (frobeniusP59Action
      (frobeniusP47Action v))

record ExtremalFrobeniusActionSurface : Set where
  field
    p47Action :
      GL.FactorVec →
      GL.FactorVec

    p59Action :
      GL.FactorVec →
      GL.FactorVec

    p71Action :
      GL.FactorVec →
      GL.FactorVec

    combinedAction :
      GL.FactorVec →
      GL.FactorVec

    p47ActionIsCoordinatePermutation :
      p47Action
      ≡
      frobeniusP47Action

    p59ActionIsCoordinatePermutation :
      p59Action
      ≡
      frobeniusP59Action

    p71ActionIsCoordinatePermutation :
      p71Action
      ≡
      frobeniusP71Action

    combinedActionIsCoordinatePermutation :
      combinedAction
      ≡
      combinedExtremalFrobeniusAction

open ExtremalFrobeniusActionSurface public

canonicalExtremalFrobeniusActionSurface :
  ExtremalFrobeniusActionSurface
canonicalExtremalFrobeniusActionSurface =
  record
    { p47Action =
        frobeniusP47Action
    ; p59Action =
        frobeniusP59Action
    ; p71Action =
        frobeniusP71Action
    ; combinedAction =
        combinedExtremalFrobeniusAction
    ; p47ActionIsCoordinatePermutation =
        refl
    ; p59ActionIsCoordinatePermutation =
        refl
    ; p71ActionIsCoordinatePermutation =
        refl
    ; combinedActionIsCoordinatePermutation =
        refl
    }

p47VacuumFixedPoint :
  frobeniusP47Action zeroFactorVec
  ≡
  zeroFactorVec
p47VacuumFixedPoint =
  refl

p59VacuumFixedPoint :
  frobeniusP59Action zeroFactorVec
  ≡
  zeroFactorVec
p59VacuumFixedPoint =
  refl

p71VacuumFixedPoint :
  frobeniusP71Action zeroFactorVec
  ≡
  zeroFactorVec
p71VacuumFixedPoint =
  refl

combinedExtremalVacuumFixedPoint :
  combinedExtremalFrobeniusAction zeroFactorVec
  ≡
  zeroFactorVec
combinedExtremalVacuumFixedPoint =
  refl

record ExtremalFrobeniusVacuumFixedPointSlice : Set where
  field
    actionSurface :
      ExtremalFrobeniusActionSurface

    vacuumVec15 :
      GL.Vec15 Nat

    vacuumFactorVec :
      GL.FactorVec

    vacuumVec15IsZero :
      vacuumVec15
      ≡
      zeroVec15

    vacuumFactorVecIsZero :
      vacuumFactorVec
      ≡
      zeroFactorVec

    p47VacuumFixed :
      p47Action actionSurface vacuumFactorVec
      ≡
      vacuumFactorVec

    p59VacuumFixed :
      p59Action actionSurface vacuumFactorVec
      ≡
      vacuumFactorVec

    p71VacuumFixed :
      p71Action actionSurface vacuumFactorVec
      ≡
      vacuumFactorVec

    combinedVacuumFixed :
      combinedAction actionSurface vacuumFactorVec
      ≡
      vacuumFactorVec

    uniquenessPromoted :
      Bool

    uniquenessPromotedIsFalse :
      uniquenessPromoted
      ≡
      false

open ExtremalFrobeniusVacuumFixedPointSlice public

canonicalExtremalFrobeniusVacuumFixedPointSlice :
  ExtremalFrobeniusVacuumFixedPointSlice
canonicalExtremalFrobeniusVacuumFixedPointSlice =
  record
    { actionSurface =
        canonicalExtremalFrobeniusActionSurface
    ; vacuumVec15 =
        zeroVec15
    ; vacuumFactorVec =
        zeroFactorVec
    ; vacuumVec15IsZero =
        refl
    ; vacuumFactorVecIsZero =
        refl
    ; p47VacuumFixed =
        p47VacuumFixedPoint
    ; p59VacuumFixed =
        p59VacuumFixedPoint
    ; p71VacuumFixed =
        p71VacuumFixedPoint
    ; combinedVacuumFixed =
        combinedExtremalVacuumFixedPoint
    ; uniquenessPromoted =
        false
    ; uniquenessPromotedIsFalse =
        refl
    }
