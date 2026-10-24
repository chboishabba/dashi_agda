module DASHI.Unified.HyperfabricWittenD4SU3OriginalOwnerCutExact where

-- 2026-10-24 source-native SU(2)_4 ⊂ SU(3)_1 CONFORMAL EMBEDDING.
-- PRIOR AUTHORS: J. Lacki, Ph. Zaugg, Phys Lett B228 (1989)
-- 223-227 DOI 10.1016/0370-2693(89)90662-X;
-- original SU2 ADE/Cappelli-Itzykson-Zuber modular invariants.
--
-- This reuses the PRE-EXISTING DASHI Agda SU2_4 and SU3_1
-- integrable Wilson line sectors, not a newly invented 369 gauge group.
-- Branching SU3 vac → SU2_4 (0 ⊕ 4), two DISTINCT SU3 charges
-- fundamental/antifundamental → the SAME SU2_4 doubled label 2.
-- The corresponding D4 torus invariant is
-- |chi_0+chi_4|² + 2|chi_2|².
--
-- This is the source-prescribed BRANCHING TABLE and exact
-- finite arithmetic only. No affine VOA extension/Q-system,
-- actual 3D CS path integral, experimental colour, Monster 27A/B
-- correspondence or 27-site graph intertwiner is constructed.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.SU2Level4Spin1RepReceipt as WZW
import DASHI.Physics.QFT.SU3FromAnyon3FoldReceipt as SU3
import DASHI.Physics.QFT.LevelRankDualityReceipt as LevelRank

branching :
  SU3.SU3ChernSimonsLevel1WilsonLineSector →
  WZW.SU2Level4Representation → Nat
branching SU3.trivialWilsonLine WZW.j0Rep = 1
branching SU3.trivialWilsonLine WZW.j2Rep = 1
branching SU3.fundamentalWilsonLine WZW.j1Rep = 1
branching SU3.antiFundamentalWilsonLine WZW.j1Rep = 1
branching _ _ = 0

d4Coupling :
  WZW.SU2Level4Representation →
  WZW.SU2Level4Representation → Nat
d4Coupling a b =
    branching SU3.trivialWilsonLine a * branching SU3.trivialWilsonLine b
  + branching SU3.fundamentalWilsonLine a * branching SU3.fundamentalWilsonLine b
  + branching SU3.antiFundamentalWilsonLine a * branching SU3.antiFundamentalWilsonLine b

oldSU2KFourExact : WZW.su2Level4 ≡ 4
oldSU2KFourExact = refl

oldSU3SourceThreeCharges : SU3.z3BraidedChargeCardinality ≡ 3
oldSU3SourceThreeCharges = refl

oldSU2DoubledSpinTwoIsJOne :
  WZW.doubledSpin WZW.j1Rep ≡ 2
oldSU2DoubledSpinTwoIsJOne = refl

condensingSimpleCurrentHasIntegerWeight :
  WZW.wzwConformalWeightNumerator WZW.j2Rep
    ≡ WZW.wzwConformalWeightDenominator
condensingSimpleCurrentHasIntegerWeight = refl

d4VacuumCurrentMixed :
  d4Coupling WZW.j0Rep WZW.j2Rep ≡ 1
d4VacuumCurrentMixed = refl

d4DoubleFixedPoint :
  d4Coupling WZW.j1Rep WZW.j1Rep ≡ 2
d4DoubleFixedPoint = refl

d4OddHalfSpinRemoved :
  d4Coupling WZW.j1/2Rep WZW.j1/2Rep ≡ 0
d4OddHalfSpinRemoved = refl

distinctSU3ChargeSourcesCollapseOnRestriction :
  branching SU3.fundamentalWilsonLine WZW.j1Rep
    ≡ branching SU3.antiFundamentalWilsonLine WZW.j1Rep
distinctSU3ChargeSourcesCollapseOnRestriction = refl

d4FixedPointMultiplicityNotOne :
  d4Coupling WZW.j1Rep WZW.j1Rep ≡ 1 → ⊥
d4FixedPointMultiplicityNotOne ()

-- Source-owner separation: Agda LevelRankDualityReceipt's
-- SU2_3 <-> SU3_1 is explicitly a CANDIDATE label, NOT this
-- actual k=4 CONFORMAL embedding or the strict SU2_3/SU3_2
-- rank-level partner.
-- C3 fusion AFTER extension != an isomorphic action of the original
-- spatial Cube27, the horned-sphere C3 actor or Monster C27.
