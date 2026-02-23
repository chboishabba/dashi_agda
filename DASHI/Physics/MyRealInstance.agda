module DASHI.Physics.MyRealInstance where

open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.PhysicsUnificationTarget as PUT

-- Temporary concrete instance based on the existing Bool ultrametric closure.
myKit : RK.RealClosureKit
myKit =
  record
    { S = CCS.realStack .CB.S
    ; U = CCS.realStack .CB.U
    ; C = CCS.realStack .CB.C
    ; P = CCS.realStack .CB.P
    ; R = CCS.realStack .CB.R
    ; nonexpC = CCS.realStack .CB.nonexpC
    ; nonexpR = CCS.realStack .CB.nonexpR
    ; strictP = CCS.realStack .CB.strictP
    ; orderLaws = CCS.realStack .CB.orderLaws
    ; pres≢R = CCS.realStack .CB.pres≢R
    ; fp = CCS.realStack .CB.fp0
    ; fixedT = CCS.realStack .CB.fixedT
    ; uniqueT = CCS.realStack .CB.uniqueT
    ; inv = CCS.realStack .CB.inv
    ; iso = CCS.realStack .CB.iso
    ; fs = CCS.realStack .CB.fs
    }

physicsGoal : PUT.PhysicsGoal myKit
physicsGoal = CCS.physicsUnification
