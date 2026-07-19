module DASHI.Physics.YangMills.YMMassGapRoute where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanSU2GeometryQ0Bundle

open import DASHI.Geometry.Gauge.SUNPrimitives
open import DASHI.Geometry.Gauge.SUNLane
open import DASHI.Physics.YangMills.YMMassGapTarget
open import DASHI.Physics.YangMills.LatticeYangMills
open import DASHI.Physics.YangMills.BalabanRGLane
open import DASHI.Physics.YangMills.OSAxiomBundle
open import DASHI.Physics.YangMills.WightmanReconstructionLane
open import DASHI.Physics.YangMills.MassGapSpectralStatement
open import DASHI.Physics.YangMills.O4RestorationLane

record YMMassGapRoute (N : Nat) : Setω where
  field
    sunLane : SUNLane N
    target : YMMassGapTarget N
    lattice : LatticeYangMills N
    balabanRG : BalabanRGLane
    osBundle : OSAxiomBundle
    wightman : WightmanReconstructionLane
    spectralGap : MassGapSpectralStatement
    o4Restoration : O4RestorationLane
    logSobolev : Bool
    witten : Bool
    qit : Bool
    clayYangMillsPromotedRoute : Bool
    logSobolevIsFalse : logSobolev ≡ false
    wittenIsFalse : witten ≡ false
    qitIsFalse : qit ≡ false
    clayYangMillsPromotedRouteIsFalse : clayYangMillsPromotedRoute ≡ false
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalYMMassGapRoute : (N : Nat) → YMMassGapRoute N
canonicalYMMassGapRoute N = record
  { sunLane = canonicalSUNLane N
  ; target = canonicalYMMassGapTarget N
  ; lattice = canonicalLatticeYangMills N
  ; balabanRG = canonicalBalabanRGLane
  ; osBundle = canonicalOSAxiomBundle
  ; wightman = canonicalWightmanReconstructionLane
  ; spectralGap = canonicalMassGapSpectralStatement
  ; o4Restoration = canonicalO4RestorationLane
  ; logSobolev = false
  ; witten = false
  ; qit = false
  ; clayYangMillsPromotedRoute = false
  ; logSobolevIsFalse = refl
  ; wittenIsFalse = refl
  ; qitIsFalse = refl
  ; clayYangMillsPromotedRouteIsFalse = refl
  ; noClayPromotion = refl
  }
