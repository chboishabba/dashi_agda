module DASHI.Unified.HyperfabricWittenCSWZWMonsterSourceOwnerCutExact where

-- This is a THIN source-original theorem-owner weld, NOT a second model.
-- PRIOR AUTHORS: Witten 1989 Chern-Simons/WZW, Verlinde fusion formula;
-- FLM 1988 Monster VOA, Witten 2007 AdS3 proposal; Maloney/Witten 2007.
-- Reuses the existing SU2_4 integrable representation/weights and the
-- original Monster first q-coefficient. Three Witten uses must be distinct:
-- 3D topological CS boundary WZW, proposed AdS3 gravity/Monster CFT,
-- and independent index/SUSY/Witten-Laplacian mathematical programmes.
--
-- A SOURCE-level observation: SU2_4 CS torus has FIVE chiral
-- conformal-block sectors and c=2. Holomorphic Vnatural c=24
-- has ONE irreducible chiral VOA module. Those distinct chiral
-- representation structures cannot be identified as identical theories.
-- They can occur in DIFFERENT sectors of a larger theory, which would
-- require an actual embedding/extension and operator action.
-- No CS path-integral or physical AdS3 metric/bulk is built here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.SU2Level4Spin1RepReceipt as WZW
import DASHI.Physics.QFT.KacMoodyLevelReceipt as CSLevel
import DASHI.Moonshine.JCoefficientCharacterBridge as J
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Monster

originalWittenBoundaryKFourLevel : WZW.su2Level4 ≡ 4
originalWittenBoundaryKFourLevel = refl

originalWZWJTwoWeight :
  WZW.wzwConformalWeightNumerator WZW.j2Rep
    ≡ WZW.wzwConformalWeightDenominator
originalWZWJTwoWeight = refl

wittenCSBoundaryTorusSectorCount : Nat
wittenCSBoundaryTorusSectorCount = 4 + 1

wittenCSTorusHasFivePrimarySectors :
  wittenCSBoundaryTorusSectorCount ≡ 5
wittenCSTorusHasFivePrimarySectors = refl

witten2007MonsterHolomorphicSimpleModuleCount : Nat
witten2007MonsterHolomorphicSimpleModuleCount = 1

noIdentityOfChiralSectorSets :
  wittenCSBoundaryTorusSectorCount
    ≡ witten2007MonsterHolomorphicSimpleModuleCount → ⊥
noIdentityOfChiralSectorSets ()

sourceSU2KFourChiralCentralCharge : Nat
sourceSU2KFourChiralCentralCharge = 2

sourceMonsterChiralCentralCharge : Nat
sourceMonsterChiralCentralCharge = 24

chiralCentralChargesDiffer :
  sourceSU2KFourChiralCentralCharge
    ≡ sourceMonsterChiralCentralCharge → ⊥
chiralCentralChargesDiffer ()

originalMonsterFirstCharacterCoefficient :
  196884 ≡ 1 + 196883
originalMonsterFirstCharacterCoefficient = J.firstCoefficientArithmetic

-- Deliberate nonpromotion: no same-sector identification between the
-- SO(24) 26D worldsheet matter and Monster c24 holomorphic AdS3
-- boundary, and no Witten 1989 -> Witten 2007 3D bulk duality proof.
