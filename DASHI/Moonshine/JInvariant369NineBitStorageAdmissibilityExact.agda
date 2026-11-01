module DASHI.Moonshine.JInvariant369NineBitStorageAdmissibilityExact where

------------------------------------------------------------------------
-- NINE-BIT STORAGE ADMISSIBILITY FOR THE J 27-FIBRE
--
-- FixedNineBitFramed27WordStorageExact proves BinaryWord9 -> three canonical
-- framed-27 cells -> BinaryWord9.  Its reverse serializer intentionally reads
-- only the two-trit payload of each cell.  Therefore arbitrary noncanonical
-- frame trits are residual information and cannot be discarded for the j
-- renderer, where the third trit is the same-point pants continuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.ComputerScience.BinaryThreeBitTrit27FibreLiftExact as Lift27
import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact as Storage
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP

------------------------------------------------------------------------
-- 1. Two 27 words that differ only in one frame trit.
------------------------------------------------------------------------

cellFrameNegative : Orbit.TritTriple
cellFrameNegative =
  Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne

cellFramePositive : Orbit.TritTriple
cellFramePositive =
  Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne

cellCanonical : Orbit.TritTriple
cellCanonical =
  Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero

wordFrameNegative : Storage.Ternary27Word3
wordFrameNegative =
  Storage.ternary27Word3 cellFrameNegative cellCanonical cellCanonical

wordFramePositive : Storage.Ternary27Word3
wordFramePositive =
  Storage.ternary27Word3 cellFramePositive cellCanonical cellCanonical

------------------------------------------------------------------------
-- 2. The nine-bit serializer collides because it observes only payload trits.
------------------------------------------------------------------------

nineBitFrameCollision :
  Storage.ternary27ToBinaryWord9 wordFrameNegative
  ≡ Storage.ternary27ToBinaryWord9 wordFramePositive
nineBitFrameCollision = refl

firstFrame : Storage.Ternary27Word3 → SSP.SSPTrit
firstFrame word = Lift27.projectFrame (Storage.cell0 word)

negativeNotPositive : SSP.sspNegOne ≡ SSP.sspPosOne → ⊥
negativeNotPositive ()

collisionInputsDistinct : wordFrameNegative ≡ wordFramePositive → ⊥
collisionInputsDistinct eq = negativeNotPositive (cong firstFrame eq)

------------------------------------------------------------------------
-- 3. Boundary.
------------------------------------------------------------------------

record JInvariantNineBitStorageAdmissibilityBoundary : Set where
  constructor j-invariant-nine-bit-storage-admissibility-boundary
  field
    binaryWordRoundTripOwnerReusable : Bool
    canonicalNeutralFrameSubcarrierAdmissible : Bool
    arbitraryJFrameLosslessInNineBits : Bool
    explicitFrameResidualRequired : Bool
    physicalBitCostOptimalityProved : Bool

canonicalJInvariantNineBitStorageAdmissibilityBoundary :
  JInvariantNineBitStorageAdmissibilityBoundary
canonicalJInvariantNineBitStorageAdmissibilityBoundary =
  j-invariant-nine-bit-storage-admissibility-boundary
    true true false true false
