module DASHI.Mathematics.Algebra.RationalAlbertAdvancedFrontierExact where

------------------------------------------------------------------------
-- ADVANCED FRONTIER AFTER UNIVERSAL IDENTITY / CYCLIC SUBGROUP SOURCE WRITING
--
-- This status owner separates source-written universal theorems from observed
-- Agda-kernel receipts.  It also separates a concrete nontrivial C3 subgroup
-- from recognition of the full exceptional groups F4 and E6.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanIdentityExact as J
import DASHI.Mathematics.Algebra.RationalAlbertCharacteristicIdentityExact as C
import DASHI.Mathematics.Algebra.RationalAlbertCyclicAutomorphismExact as G

jordanIdentityPaidInSource : (x y : A.RationalAlbert) →
  A.jordanProduct (A.jordanProduct (A.jordanProduct x x) y) x
  ≡ A.jordanProduct (A.jordanProduct x x) (A.jordanProduct y x)
jordanIdentityPaidInSource = J.jordanIdentity

characteristicIdentityPaidInSource : (x : A.RationalAlbert) →
  C.characteristicResidual x ≡ C.zeroAlbert
characteristicIdentityPaidInSource = C.characteristicIdentity

cyclicProductIntertwinerPaidInSource : (x y : A.RationalAlbert) →
  G.rotateAlbert (A.jordanProduct x y)
  ≡ A.jordanProduct (G.rotateAlbert x) (G.rotateAlbert y)
cyclicProductIntertwinerPaidInSource = G.rotatePreservesJordan

cyclicCubicNormIntertwinerPaidInSource : (x : A.RationalAlbert) →
  A.cubicNorm (G.rotateAlbert x) ≡ A.cubicNorm x
cyclicCubicNormIntertwinerPaidInSource = G.rotatePreservesCubicNorm

record RationalAlbertAdvancedFrontier : Set where
  constructor frontier
  field
    carrierProductUnitNormConstructed : Bool
    universalJordanIdentitySourceWritten : Bool
    cubicCharacteristicIdentitySourceWritten : Bool
    localPolarizedJordanCoefficientAuditPassed : Bool
    localPolarizedCubicAuditPassed : Bool
    localAuditCountsAsAgdaKernelReceipt : Bool
    exactHeadAgdaKernelReceiptObserved : Bool
    concreteC3AlbertAutomorphismSubgroupConstructed : Bool
    concreteC3CubicNormStabilizerSubgroupConstructed : Bool
    fullF4AutomorphismActionConstructed : Bool
    fullE6CubicNormStabilizerActionConstructed : Bool

open RationalAlbertAdvancedFrontier public

currentAdvancedFrontier : RationalAlbertAdvancedFrontier
currentAdvancedFrontier =
  frontier
    true true true
    true true false false
    true true false false
