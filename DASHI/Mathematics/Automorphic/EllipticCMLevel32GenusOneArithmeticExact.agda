module DASHI.Mathematics.Automorphic.EllipticCMLevel32GenusOneArithmeticExact where

------------------------------------------------------------------------
-- K4 HIGHEST-ALPHA MODULARITY CUT FOR E:y²=x³-x:
--
-- Instead of reconstructing all a_n from scratch, use:
--
--   dim S₂(Γ₀(32)) = genus(X₀(32)) = 1.
--
-- Then any two NORMALIZED weight-two cusp forms of level 32
-- and trivial Nebentypus are identical. In particular, once
-- (1) eta(4τ)² eta(8τ)² is proved to be such a cusp form
-- and (2) original E's modularity is a same-object theorem,
-- the original f_E and the eta product are equal.
--
-- This module proves ONLY the finite arithmetic of the
-- classical modular curve genus formula for N=32:
--
--   mu=[SL₂(Z):Γ₀(32)] = 32*(1+1/2)=48;
--   e₂=0, e₃=0;
--   cusps=sum_{d|32} φ(gcd(d,32/d))
--       =1+1+2+2+1+1=8;
--   12*g = 12+mu-3e₂-4e₃-6*cusps = 12.
--
-- The named modular curve genus theorem, dimension=genus,
-- eta-quotient cusp holomorphy, normalized q¹=1,
-- and curve modularity are still ORIGINAL ANALYTIC PRODUCERS.
-- No Boolean "modularity witness" replaces these.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Automorphic.EllipticCMLevel32EtaNewmanArithmeticExact as Eta

level32Index : Nat
level32Index = 32 + 16

indexGammaZero32Is48 : level32Index ≡ 48
indexGammaZero32Is48 = refl

ellipticOrder2Points : Nat
ellipticOrder2Points = 0

ellipticOrder3Points : Nat
ellipticOrder3Points = 0

-- The six divisor cusps for d=1,2,4,8,16,32 contribute
-- 1,1,2,2,1,1 respectively.
level32CuspCount : Nat
level32CuspCount = 1 + 1 + 2 + 2 + 1 + 1

level32HasEightCusps : level32CuspCount ≡ 8
level32HasEightCusps = refl

-- Eliminates division by 12 in the formal numeric part:
-- 12*g = 12 + index - 3e2 - 4e3 - 6c.
-- The two elliptic-point counts are zero for N=32.
level32GenusNumeratorEquation :
  12 + level32Index
  ≡ 12 + 6 * level32CuspCount
level32GenusNumeratorEquation = refl

level32GenusOneNumber : Nat
level32GenusOneNumber = 1

level32GenusOneArithmetic :
  12 * level32GenusOneNumber + 6 * level32CuspCount
  ≡ 12 + level32Index
level32GenusOneArithmetic = refl

-- Combine the original Newman q-normalization and numerical
-- genus preflight WITHOUT claiming the analytic dimension
-- theorem or cusp-form identity was constructed in Agda.
level32EtaAndGenusPreflight :
  Eta.etaWeightedExponentSum ≡ 24
  × Eta.etaDualWeightedExponentSum ≡ 24
  × Eta.etaScaleProductSquared ≡ 32 * 32
  × level32GenusOneNumber ≡ 1
level32EtaAndGenusPreflight = refl , refl , refl , refl
