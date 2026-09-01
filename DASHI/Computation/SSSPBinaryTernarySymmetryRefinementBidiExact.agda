module DASHI.Computation.SSSPBinaryTernarySymmetryRefinementBidiExact where

-- This owner corrects a possible arity-only reading of 6 and 9.
-- In the Base369 core, C6 is the binary/polarity refinement of C3,
-- C9 is the ternary depth-two refinement of C3, and both refine to C18.
-- Separately, six-line and nine-cell observation objects carry internal
-- permutation/cyclic symmetry.  SSSP reuses those proof shapes only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Base369 as B369
import DASHI.Foundations.Base369BinaryTernaryRefinement as R23
import DASHI.Computation.SSSPSortingBarrierTernaryBidiExact as SSSP

------------------------------------------------------------------------
-- 1. Exact 2^a 3^b resolution diamond.
------------------------------------------------------------------------

SSSPCoarseResolution : R23.Resolution23
SSSPCoarseResolution = R23.phase3Resolution

SSSPBinaryControlResolution : R23.Resolution23
SSSPBinaryControlResolution = R23.phase6Resolution

SSSPTernaryOrderResolution : R23.Resolution23
SSSPTernaryOrderResolution = R23.phase9Resolution

SSSPCommonResolution : R23.Resolution23
SSSPCommonResolution = R23.phase18Resolution

binaryControlRefinesC3ToC6 :
  R23.binaryRefine SSSPCoarseResolution ≡ SSSPBinaryControlResolution
binaryControlRefinesC3ToC6 = R23.phase3-binary-refines-to-phase6

ternaryOrderRefinesC3ToC9 :
  R23.ternaryRefine SSSPCoarseResolution ≡ SSSPTernaryOrderResolution
ternaryOrderRefinesC3ToC9 = R23.phase3-ternary-refines-to-phase9

binaryThenTernaryReachesC18 :
  R23.ternaryRefine SSSPBinaryControlResolution ≡ SSSPCommonResolution
binaryThenTernaryReachesC18 = R23.phase6-ternary-refines-to-phase18

ternaryThenBinaryReachesC18 :
  R23.binaryRefine SSSPTernaryOrderResolution ≡ SSSPCommonResolution
ternaryThenBinaryReachesC18 = R23.phase9-binary-refines-to-phase18

SSSPBinaryTernaryRefinementCommutes :
  R23.binaryRefine (R23.ternaryRefine SSSPCoarseResolution) ≡
  R23.ternaryRefine (R23.binaryRefine SSSPCoarseResolution)
SSSPBinaryTernaryRefinementCommutes =
  R23.binary-ternary-refinement-commutes SSSPCoarseResolution

------------------------------------------------------------------------
-- 2. The paper's binary outcomes and the partial-order ternary observation
--    are independent refinement axes.
--
-- BMSSP success/partial is a genuine two-way control surface.  Pair ordering
-- is a three-way consumer observation: left, deliberately unexposed, right.
-- Neither is coerced into being the other.
------------------------------------------------------------------------

data BinaryControl : Set where
  successfulControl partialControl : BinaryControl

fromBMSSPOutcome : SSSP.BMSSPOutcome → BinaryControl
fromBMSSPOutcome SSSP.successfulExecution = successfulControl
fromBMSSPOutcome SSSP.partialLargeWorkload = partialControl

binaryControlRegression-success :
  fromBMSSPOutcome SSSP.successfulExecution ≡ successfulControl
binaryControlRegression-success = refl

binaryControlRegression-partial :
  fromBMSSPOutcome SSSP.partialLargeWorkload ≡ partialControl
binaryControlRegression-partial = refl

------------------------------------------------------------------------
-- 3. Six is a symmetry carrier here: C6 has a literal six-cycle.
------------------------------------------------------------------------

SSSPHexPhase : Set
SSSPHexPhase = B369.HexTruth

rotateBinaryTernaryPhase : SSSPHexPhase → SSSPHexPhase
rotateBinaryTernaryPhase = B369.rotateHex

sixCycleCloses :
  (h : SSSPHexPhase) →
  B369.spin 6 rotateBinaryTernaryPhase h ≡ h
sixCycleCloses = B369.rotateHex⁶

------------------------------------------------------------------------
-- 4. Nine is likewise a symmetry carrier: C9 has a literal nine-cycle.
------------------------------------------------------------------------

SSSPNonaryPhase : Set
SSSPNonaryPhase = B369.NonaryTruth

rotateTernaryDepthTwoPhase : SSSPNonaryPhase → SSSPNonaryPhase
rotateTernaryDepthTwoPhase = B369.rotateNonary

nineCycleCloses :
  (n : SSSPNonaryPhase) →
  B369.spin 9 rotateTernaryDepthTwoPhase n ≡ n
nineCycleCloses = B369.rotateNonary⁹

------------------------------------------------------------------------
-- 5. BIDI interpretation.
--
-- Forward: a ternary partial-order state may be refined independently by a
-- binary control/polarity axis or by another ternary observation depth.
-- Reverse: observing C6 or C9 does not entitle us to identify their refinements;
-- they only meet at the declared C18 common refinement.
------------------------------------------------------------------------

record SSSPRefinementBoundary : Set where
  constructor ssspRefinementBoundary
  field
    binaryAndTernaryAxesIndependent : Set
    sixIsBinaryTimesTernaryResolution : Set
    nineIsTernaryDepthTwoResolution : Set
    commonRefinementIsEighteen : Set
    sixAndNineAreNotFlatCoordinateCounts : Set

canonicalSSSPRefinementBoundary : SSSPRefinementBoundary
canonicalSSSPRefinementBoundary =
  ssspRefinementBoundary
    (R23.binaryRefine (R23.ternaryRefine SSSPCoarseResolution) ≡
     R23.ternaryRefine (R23.binaryRefine SSSPCoarseResolution))
    (R23.sectorCount SSSPBinaryControlResolution ≡ 6)
    (R23.sectorCount SSSPTernaryOrderResolution ≡ 9)
    (R23.sectorCount SSSPCommonResolution ≡ 18)
    (SSSPHexPhase → SSSPNonaryPhase → Set)

------------------------------------------------------------------------
-- 6. Representation firewall.
--
-- C6/C9 cyclic phase symmetry and T3^6/T3^9 product carriers are separate
-- constructions.  This owner uses the former.  No equality between those
-- carrier roles is asserted here.
------------------------------------------------------------------------

sixSectorCountExact : R23.sectorCount SSSPBinaryControlResolution ≡ 6
sixSectorCountExact = R23.phase6-sector-count

nineSectorCountExact : R23.sectorCount SSSPTernaryOrderResolution ≡ 9
nineSectorCountExact = R23.phase9-sector-count

eighteenSectorCountExact : R23.sectorCount SSSPCommonResolution ≡ 18
eighteenSectorCountExact = R23.phase18-sector-count
