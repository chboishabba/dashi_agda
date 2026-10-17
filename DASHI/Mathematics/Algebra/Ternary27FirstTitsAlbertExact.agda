module DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

------------------------------------------------------------------------
-- TERNARY-27 -> FIRST-TITS / TRINIFICATION BASIS
--
-- Synchronized from the exceptional/trinification donor branch.  The older
-- 27-point carrier is used as the exact basis index set of M3 + M3 + M3:
-- (sector,row,column) in 3 x 3 x 3.  No point-set/vector-space collapse is
-- made; the full ternary vector carrier is the function space on the 27 slots.
------------------------------------------------------------------------

data MatrixSector3 : Set where
  sector0 sector1 sector2 : MatrixSector3

sectorOfTrit : SSP.SSPTrit → MatrixSector3
sectorOfTrit SSP.sspNegOne = sector0
sectorOfTrit SSP.sspZero = sector1
sectorOfTrit SSP.sspPosOne = sector2

tritOfSector : MatrixSector3 → SSP.SSPTrit
tritOfSector sector0 = SSP.sspNegOne
tritOfSector sector1 = SSP.sspZero
tritOfSector sector2 = SSP.sspPosOne

sectorTritRoundTrip : (s : MatrixSector3) → sectorOfTrit (tritOfSector s) ≡ s
sectorTritRoundTrip sector0 = refl
sectorTritRoundTrip sector1 = refl
sectorTritRoundTrip sector2 = refl

tritSectorRoundTrip : (t : SSP.SSPTrit) → tritOfSector (sectorOfTrit t) ≡ t
tritSectorRoundTrip SSP.sspNegOne = refl
tritSectorRoundTrip SSP.sspZero = refl
tritSectorRoundTrip SSP.sspPosOne = refl

record TitsBasisSlot : Set where
  constructor titsBasisSlot
  field
    sector : MatrixSector3
    row : SSP.SSPTrit
    column : SSP.SSPTrit
open TitsBasisSlot public

pointToBasisSlot : Geometry.Ternary27Point → TitsBasisSlot
pointToBasisSlot (Geometry.ternary27Point s i j) =
  titsBasisSlot (sectorOfTrit s) i j

basisSlotToPoint : TitsBasisSlot → Geometry.Ternary27Point
basisSlotToPoint (titsBasisSlot s i j) =
  Geometry.ternary27Point (tritOfSector s) i j

pointBasisRoundTrip : (p : Geometry.Ternary27Point) → basisSlotToPoint (pointToBasisSlot p) ≡ p
pointBasisRoundTrip (Geometry.ternary27Point SSP.sspNegOne i j) = refl
pointBasisRoundTrip (Geometry.ternary27Point SSP.sspZero i j) = refl
pointBasisRoundTrip (Geometry.ternary27Point SSP.sspPosOne i j) = refl

basisPointRoundTrip : (b : TitsBasisSlot) → pointToBasisSlot (basisSlotToPoint b) ≡ b
basisPointRoundTrip (titsBasisSlot sector0 i j) = refl
basisPointRoundTrip (titsBasisSlot sector1 i j) = refl
basisPointRoundTrip (titsBasisSlot sector2 i j) = refl

basisStateCount : Nat
basisStateCount = 3 * 3 * 3

basisStateCountIs27 : basisStateCount ≡ 27
basisStateCountIs27 = refl

Ternary27FunctionVector : Set
Ternary27FunctionVector = Geometry.Ternary27Point → SSP.SSPTrit

record FirstTitsAlbertStructure : Set₁ where
  field
    Carrier : Set
    carrierIsTernary27FunctionVector : Carrier ≡ Ternary27FunctionVector
    jordanProduct : Carrier → Carrier → Carrier
    jordanUnit : Carrier
    cubicNorm : Carrier → SSP.SSPTrit
    basisStructureConstants : TitsBasisSlot → TitsBasisSlot → Carrier
    bilinearityReceipt : Set
    commutativityReceipt : Set
    unitReceipt : Set
    jordanIdentityReceipt : Set
    cubicCompatibilityReceipt : Set
open FirstTitsAlbertStructure public

record Ternary27FirstTitsLocalReceipt : Set where
  constructor ternary27-first-tits-local-receipt
  field
    exactBasisBijectionPaid : Bool
    vectorCarrierIsFunctionSpaceShape : Bool
    firstTitsFormulaImplementedInPython : Bool
    all729BasisJordanIdentityChecksPass : Bool
    randomFullVectorJordanChecksPass : Bool
    basisPairZeroProductCount : Nat
    basisPairOneCoordinateProductCount : Nat
    basisPairTwoCoordinateProductCount : Nat
    sl3CubedCubicNormChecksPass : Bool
    sameKernelAgdaFirstTitsProductPaid : Bool
    characteristicThreeAlbertSimplicityPaid : Bool
    sameKernelAlbertIntertwinerPaid : Bool
    fullF4RecognitionPaid : Bool
    boundary : String
open Ternary27FirstTitsLocalReceipt public

canonicalTernary27FirstTitsLocalReceipt : Ternary27FirstTitsLocalReceipt
canonicalTernary27FirstTitsLocalReceipt =
  ternary27-first-tits-local-receipt
    true true true true true
    414 291 24 true
    false false false false
    "The literal Ternary27Point carrier is an exact basis-index set for the 27-dimensional M3^3 first-Tits/trinification coordinate space. Local F3 computation pays Jordan/cubic diagnostics; characteristic-three simplicity, same-kernel product/intertwiner, and F4 recognition remain separate obligations."
