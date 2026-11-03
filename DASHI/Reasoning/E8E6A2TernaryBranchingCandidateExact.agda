module DASHI.Reasoning.E8E6A2TernaryBranchingCandidateExact where

------------------------------------------------------------------------
-- TERNARY 72 + 81 + 81 + 6 + 3 BRANCHING CANDIDATE
--
-- DASHI CONTRIBUTION / CROSS-LANGUAGE AUDIT
--
-- Local Python found an explicit totally isotropic two-plane U in standard
-- F3^5 and a vector v with Q(v)=1, v orthogonal to U.  Therefore v+U is a
-- nine-point affine plane entirely inside the Q=1 shell.  A chosen affine line
-- inside that plane has three points.
--
-- The Lean mirror source-writes the concrete finite carrier and requests
-- `native_decide` proofs of the exact counts.  This Agda owner records the
-- resulting arithmetic architecture and evidence grade without pretending an
-- Agda finite enumeration has run.
--
--   243 = 72 + 81 + 81 + 6 + 3
--   240 = 72 + 81 + 81 + 6
--
-- The pattern is a candidate experiment/recognition decomposition only.  It
-- does not identify the 6-point piece with A2 roots, either 81-point piece with
-- an E8 mixed-root orbit, or the 240-state remainder with E8 roots.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.T5QuadraticOrbitAuditExact as Q

------------------------------------------------------------------------
-- 1. Count architecture.
------------------------------------------------------------------------

e6SectorCount mixedSectorACount mixedSectorBCount a2CandidateCount selectedAffineLineCount : Nat
e6SectorCount = 72
mixedSectorACount = 81
mixedSectorBCount = 81
a2CandidateCount = 6
selectedAffineLineCount = 3

selectedAffinePlaneCount : Nat
selectedAffinePlaneCount = a2CandidateCount + selectedAffineLineCount

selectedAffinePlaneCountIs9 : selectedAffinePlaneCount ≡ 9
selectedAffinePlaneCountIs9 = refl

selectedAffineLineCountIs3 : selectedAffineLineCount ≡ 3
selectedAffineLineCountIs3 = refl

fullCarrierCount : Nat
fullCarrierCount = Q.fullT5Count

relativeCarrierCount : Nat
relativeCarrierCount = 240

fullBranchingCount :
  fullCarrierCount ≡
    e6SectorCount + mixedSectorACount + mixedSectorBCount +
    a2CandidateCount + selectedAffineLineCount
fullBranchingCount = refl

relativeBranchingCount :
  relativeCarrierCount ≡
    e6SectorCount + mixedSectorACount + mixedSectorBCount + a2CandidateCount
relativeBranchingCount = refl

qOneShellSplit : Q.qOneCount ≡ mixedSectorBCount + selectedAffinePlaneCount
qOneShellSplit = refl

qZeroSectorMatchesMixedA : Q.qZeroCount ≡ mixedSectorACount
qZeroSectorMatchesMixedA = refl

qTwoSectorMatchesE6 : Q.qTwoCount ≡ e6SectorCount
qTwoSectorMatchesE6 = refl

------------------------------------------------------------------------
-- 2. Explicit construction coordinates retained as audit metadata.
------------------------------------------------------------------------

record ExplicitAffineConstruction : Set where
  constructor explicit-affine-construction
  field
    fieldLabel : String
    quadraticFormLabel : String
    firstIsotropicGenerator : String
    secondIsotropicGenerator : String
    affineBasePoint : String
    affineLineGenerator : String
    pythonPlaneCount : Nat
    pythonLineCount : Nat
    pythonPlaneInsideQOne : Bool

canonicalExplicitAffineConstruction : ExplicitAffineConstruction
canonicalExplicitAffineConstruction =
  explicit-affine-construction
    "F3^5"
    "Q(x)=sum_i x_i^2"
    "(0,0,1,1,1)"
    "(0,1,0,1,2)"
    "(1,0,0,0,0)"
    "(0,0,1,1,1)"
    9 3 true

------------------------------------------------------------------------
-- 3. Evidence-grade receipt.
------------------------------------------------------------------------

record CrossLanguageBranchingReceipt : Set where
  constructor cross-language-branching-receipt
  field
    pythonTotallyIsotropicPlanesFound : Nat
    pythonCompatibleAffineChoicesFound : Nat
    pythonSelectedPlaneCountChecked : Bool
    pythonSelectedPlaneInsideQOneChecked : Bool
    pythonSelectedLineCountChecked : Bool
    pythonFullBranchingCountChecked : Bool
    leanConcreteCarrierSourceWritten : Bool
    leanKernelVerified : Bool
    agdaConcreteAffineEnumerationProvedHere : Bool
    note : String

open CrossLanguageBranchingReceipt public

canonicalCrossLanguageBranchingReceipt : CrossLanguageBranchingReceipt
canonicalCrossLanguageBranchingReceipt =
  cross-language-branching-receipt
    40 720
    true true true true
    true false false
    "Python exhaustively checked the selected affine geometry. Lean finite owners are source-written. No exact-head Lean or Agda kernel receipt is available in this session."

reflLeanUnverified :
  leanKernelVerified canonicalCrossLanguageBranchingReceipt ≡ false
reflLeanUnverified = refl

------------------------------------------------------------------------
-- 4. Non-promotion boundary.
------------------------------------------------------------------------

record BranchingCandidateBoundary : Set where
  constructor branching-candidate-boundary
  field
    exactCountArchitecturePaid : Bool
    selectedAffineGeometryRecorded : Bool
    e6SectorCountMatchesQTwo : Bool
    selectedLineAutomaticallyEqualsOldDiagonalCut : Bool
    sixPointSectorAutomaticallyA2Roots : Bool
    eightyOnePointSectorAutomaticallyMixedE8Orbit : Bool
    branchingCountsCreateE8Recognition : Bool
    branchingCountsCreatePhysicalMechanism : Bool

open BranchingCandidateBoundary public

canonicalBranchingCandidateBoundary : BranchingCandidateBoundary
canonicalBranchingCandidateBoundary =
  branching-candidate-boundary
    true true true
    false false false false false

reflNoE8Recognition :
  branchingCountsCreateE8Recognition canonicalBranchingCandidateBoundary ≡ false
reflNoE8Recognition = refl
