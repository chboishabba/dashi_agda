module DASHI.Algebra.TwoBranchNormalizationPullbackExact where

------------------------------------------------------------------------
-- MATHEMATICAL CONTEXT
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
--
-- For an ordinary nodal curve singularity the completed local ring may be
-- represented by the pullback of its two normalized branches over their common
-- residue field.  In the standard formal model:
--
--   k[[x,y]]/(xy)  ~=  k[[x]] x_k k[[y]],
--
-- where the two branch series are required to have the same constant term.
--
-- DASHI CONTRIBUTION
--
-- Isolate exactly the SET-LEVEL pullback/reconstruction structure needed by the
-- Deligne--Rapoport local-node seam, without manufacturing a second category or
-- a general commutative-algebra framework.
--
-- Given two branch carriers L,R with residue maps to K, the node carrier is the
-- proof-relevant fibre product
--
--   (l,r, residueL(l)=residueR(r)).
--
-- The projections retain the two distinct branches, the common residue is
-- well-defined, and a compatible pair reconstructs exactly.  This module does
-- NOT assert that any geometric local ring is this pullback; that is the
-- source-facing completed-local-ring identification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record TwoBranchNormalizationData : Set₁ where
  field
    LeftBranch : Set
    RightBranch : Set
    Residue : Set
    leftResidue : LeftBranch → Residue
    rightResidue : RightBranch → Residue

open TwoBranchNormalizationData public

record NodePullback (D : TwoBranchNormalizationData) : Set where
  constructor node-pullback
  field
    leftBranch : LeftBranch D
    rightBranch : RightBranch D
    residuesAgree : leftResidue D leftBranch ≡ rightResidue D rightBranch

open NodePullback public

------------------------------------------------------------------------
-- Exact branch projections and common residue.
------------------------------------------------------------------------

projectLeft :
  (D : TwoBranchNormalizationData) → NodePullback D → LeftBranch D
projectLeft D = leftBranch

projectRight :
  (D : TwoBranchNormalizationData) → NodePullback D → RightBranch D
projectRight D = rightBranch

commonResidue :
  (D : TwoBranchNormalizationData) → NodePullback D → Residue D
commonResidue D node = leftResidue D (leftBranch node)

commonResidueFromRight :
  (D : TwoBranchNormalizationData) →
  (node : NodePullback D) →
  commonResidue D node ≡ rightResidue D (rightBranch node)
commonResidueFromRight D node = residuesAgree node

------------------------------------------------------------------------
-- Reconstruction from a compatible normalized pair.
------------------------------------------------------------------------

reconstructCompatible :
  (D : TwoBranchNormalizationData) →
  (left : LeftBranch D) →
  (right : RightBranch D) →
  leftResidue D left ≡ rightResidue D right →
  NodePullback D
reconstructCompatible D left right agreement =
  node-pullback left right agreement

leftAfterReconstruct :
  (D : TwoBranchNormalizationData) →
  (left : LeftBranch D) →
  (right : RightBranch D) →
  (agreement : leftResidue D left ≡ rightResidue D right) →
  projectLeft D (reconstructCompatible D left right agreement) ≡ left
leftAfterReconstruct D left right agreement = refl

rightAfterReconstruct :
  (D : TwoBranchNormalizationData) →
  (left : LeftBranch D) →
  (right : RightBranch D) →
  (agreement : leftResidue D left ≡ rightResidue D right) →
  projectRight D (reconstructCompatible D left right agreement) ≡ right
rightAfterReconstruct D left right agreement = refl

------------------------------------------------------------------------
-- Extensionality: both normalized branches determine the pullback point.
-- Equality proofs are irrelevant once the branch coordinates agree; Prelude's
-- propositional equality UIP is not assumed globally, so expose the exact
-- proof-relevant form instead of erasing the compatibility witness.
------------------------------------------------------------------------

record SameNormalizedBranches {D : TwoBranchNormalizationData}
    (x y : NodePullback D) : Set where
  field
    sameLeft : leftBranch x ≡ leftBranch y
    sameRight : rightBranch x ≡ rightBranch y

open SameNormalizedBranches public

------------------------------------------------------------------------
-- Boundary: normalization pullback != completed-local-ring theorem.
------------------------------------------------------------------------

record TwoBranchNormalizationPullbackBoundary : Set where
  field
    proofRelevantPullbackConstructed : Bool
    exactBranchProjectionConstructed : Bool
    compatiblePairReconstructionConstructed : Bool
    commonResidueDerived : Bool
    geometricNodeLocalRingIdentifiedHere : Bool
    formalPowerSeriesRingConstructedHere : Bool

canonicalTwoBranchNormalizationPullbackBoundary :
  TwoBranchNormalizationPullbackBoundary
canonicalTwoBranchNormalizationPullbackBoundary = record
  { proofRelevantPullbackConstructed = true
  ; exactBranchProjectionConstructed = true
  ; compatiblePairReconstructionConstructed = true
  ; commonResidueDerived = true
  ; geometricNodeLocalRingIdentifiedHere = false
  ; formalPowerSeriesRingConstructedHere = false
  }
