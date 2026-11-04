module DASHI.Moonshine.Monster27GriessFrobeniusInverseChargeExact where

-- ORIGINAL EXTERNAL OWNER:
-- Frenkel-Lepowsky-Meurman Vnatural, Griess's nondegenerate invariant
-- form on weight two, Dong-Griess-Lam (2007) uniqueness treatment.
-- NATIVE REPO OWNERS:
-- MoonshineGriessAutomorphismClassificationExact (omega/2 is unit)
-- Monster27GriessNeutralSpokeActualVOAWeldExact (same literal VOA)
-- Monster27VOACubeWeightedChargeNoGoExact (chosen 27-site charge chart).
--
-- This theorem derives the inverse-charge nonzero neutral projection
-- conditional on a SAME-VOA Frobenius form / nondegenerate duality
-- producer. Do not mistake this source-written record for its inhabitant.
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Biology.MoonshineGriessAutomorphismClassificationExact as Griess
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.JInvariant369Cube27ModularSliceActionExact as Slice
import DASHI.Moonshine.Monster27VOAOnsiteCube369BridgeExact as Parent
import DASHI.Moonshine.Monster27GriessNeutralSpokeActualVOAWeldExact as Spoke

oppositeSite : Cube.Ternary27Point → Cube.Ternary27Point
oppositeSite (Cube.ternary27Point x y z) =
  Cube.ternary27Point
    (Slice.negateSSP x)
    (Slice.negateSSP y)
    (Slice.negateSSP z)

record SourceGriessFrobeniusDuality
    {Monster K : Set}
    (source : Parent.Monster27VOAOnCubeSource Monster K) : Setω where
  field
    sameVOA : Spoke.SameVOAGriessUnitSource source

    Scalar : Set
    zeroScalar : Scalar
    inner :
      Griess.Carrier (Spoke.griess sameVOA) →
      Griess.Carrier (Spoke.griess sameVOA) → Scalar

    zeroVector : Griess.Carrier (Spoke.griess sameVOA)
    zeroPairsUnit :
      inner zeroVector (Griess.unit (Spoke.griess sameVOA))
        ≡ zeroScalar

    -- This is the literal invariant Frobenius identity evaluated
    -- at the Griess identity e=omega/2:
    -- <u_1 v,e> = <u,v_1 e> = <u,v>.
    frobeniusUnit :
      (u v : Griess.Carrier (Spoke.griess sameVOA)) →
      inner (Griess.multiply (Spoke.griess sameVOA) u v)
            (Griess.unit (Spoke.griess sameVOA))
      ≡ inner u v

    -- True source-owned opposite-charge spectral states are required.
    -- A finite balanced-cube chart alone does not construct them.
    chargeEigen :
      (p : Cube.Ternary27Point) →
      Griess.Carrier (Spoke.griess sameVOA) → Set

    representativeHasCharge :
      (p : Cube.Ternary27Point) →
      chargeEigen p (Spoke.chargedRepresentative sameVOA p)

    inverseChargeDual :
      (p : Cube.Ternary27Point) →
      Griess.Carrier (Spoke.griess sameVOA)

    inverseChargeCertified :
      (p : Cube.Ternary27Point) →
      chargeEigen (oppositeSite p) (inverseChargeDual p)

    nondegeneratePairForChosenCharge :
      (p : Cube.Ternary27Point) →
      inner
        (Spoke.chargedRepresentative sameVOA p)
        (inverseChargeDual p)
      ≡ zeroScalar → ⊥

open SourceGriessFrobeniusDuality public

inverseChargeProductHasNonzeroNeutralPairing :
  ∀ {Monster K : Set}
  {source : Parent.Monster27VOAOnCubeSource Monster K}
  (F : SourceGriessFrobeniusDuality source)
  (p : Cube.Ternary27Point) →
  inner F
    (Griess.multiply (Spoke.griess (sameVOA F))
      (Spoke.chargedRepresentative (sameVOA F) p)
      (inverseChargeDual F p))
    (Griess.unit (Spoke.griess (sameVOA F)))
  ≡ zeroScalar F → ⊥
inverseChargeProductHasNonzeroNeutralPairing F p vanishes =
  nondegeneratePairForChosenCharge F p
    (trans
      (sym
        (frobeniusUnit F
          (Spoke.chargedRepresentative (sameVOA F) p)
          (inverseChargeDual F p)))
      vanishes)

inverseChargeGriessProductIsNonzero :
  ∀ {Monster K : Set}
  {source : Parent.Monster27VOAOnCubeSource Monster K}
  (F : SourceGriessFrobeniusDuality source)
  (p : Cube.Ternary27Point) →
  Griess.multiply (Spoke.griess (sameVOA F))
    (Spoke.chargedRepresentative (sameVOA F) p)
    (inverseChargeDual F p)
  ≡ zeroVector F → ⊥
inverseChargeGriessProductIsNonzero F p vanishes =
  inverseChargeProductHasNonzeroNeutralPairing F p
    (trans
      (cong
        (λ v → inner F v (Griess.unit (Spoke.griess (sameVOA F))))
        vanishes)
      (zeroPairsUnit F))

-- Nonzero source Griess product is NOT a physical cube-edge hopping:
-- opposite charge sites p and -p are separated by an even Manhattan
-- distance and (unless p=0) cannot be native cube neighbours.
-- Inverse spectral pairing still needs a SAME-MONSTER actual witness.
