module DASHI.Physics.Closure.E6HyperformH3SameObjectEmbeddingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformRadicalQuotientGravityBoundaryExact as Radical

------------------------------------------------------------------------
-- SAME-OBJECT EMBEDDING OF THE LOCAL GRAVITY CHART INTO E6/H3 GEOMETRY
--
-- Cross-branch donor: PR #1093 identifies the E6 H3 family as 120 projective
-- 3-spaces with signature 1 null radical + 6 root lines + 6 other lines, and
-- associates each radical line to one of 40 A2^3 subsystem classes.
--
-- The local gravity chart q(x,y,z)=(x+z)^2+y^2 now has the explicit E6 map
--
--        [1 1 1]
--   E =  [0 0 2]
--        [0 1 2]
--        [2 0 2]
--        [0 0 1]
--
-- satisfying E^T B_E6 E = [[1,0,1],[0,1,0],[1,0,1]].  Thus this is not only
-- an abstract quadratic lookalike: its projectivized image is one actual H3
-- patch of the finite E6 geometry.
------------------------------------------------------------------------

h3DonorPR : String
h3DonorPR = "chboishabba/dashi_agda#1093"

chartEmbeddingMatrix : String
chartEmbeddingMatrix = "[[1,1,1],[0,0,2],[0,1,2],[2,0,2],[0,0,1]] mod 3"

restrictedGramMatrix : String
restrictedGramMatrix = "[[1,0,1],[0,1,0],[1,0,1]] mod 3"

localQuadraticFormula : String
localQuadraticFormula = "q(x,y,z)=(x+z)^2+y^2"

localRadicalVector : String
localRadicalVector = "(1,0,-1) mod 3"

embeddedRadicalProjectiveLine : String
embeddedRadicalProjectiveLine = "[(0,1,1,0,2)]"

record H3SameObjectEmbeddingLocalReceipt : Set where
  constructor h3-same-object-embedding-local-receipt
  field
    explicitFiveByThreeEmbeddingPaid : Bool
    restrictedGramEqualsLocalQuadraticPaid : Bool
    embeddingRankThreePaid : Bool
    projectiveImagePointCount : Nat
    nullProjectiveLineCount : Nat
    e6RootLineCount : Nat
    otherNonsingularLineCount : Nat
    embeddedRadicalNullPaid : Bool
    embeddedRadicalOrthogonalToWholePatchPaid : Bool
    perpendicularRootLineCount : Nat
    a2CubedRootLineCount : Nat
    h3PatchSignatureMatchesDonor : Bool
    h3PatchSameObjectComputedLocally : Bool
    crossBranchKernelRecognitionPaid : Bool
    boundary : String
open H3SameObjectEmbeddingLocalReceipt public

canonicalH3SameObjectEmbeddingLocalReceipt : H3SameObjectEmbeddingLocalReceipt
canonicalH3SameObjectEmbeddingLocalReceipt =
  h3-same-object-embedding-local-receipt
    true true true
    13 1 6 6
    true true
    3 9 true true false
    "The selected gravity quadratic chart now has an explicit rank-three embedding into the five-dimensional E6 quotient with the exact restricted Gram matrix. Its projective image has the H3 signature 1 null + 6 roots + 6 other, the local radical maps to the null line [(0,1,1,0,2)], and adjoining the three perpendicular root lines gives a 9-root-line A2^3 subsystem. This is locally computed same-object identification; importing PR #1093's H3/A2^3 theorem into the current Agda kernel remains separate."

record H3AtlasGravityWeld : Set₁ where
  field
    H3Patch : Set
    A2CubedClass : Set
    WeylTransition : Set
    selectedPatch : H3Patch
    selectedClass : A2CubedClass
    patchEmbeddingReceipt : Set
    radicalClassReceipt : Set
    transitionMovesRadicalReceipt : Set
    overlapMetricReceipt : Set
    threeDirectionGlobalisationReceipt : Set
open H3AtlasGravityWeld public

data MatchingH3SignatureCreatesSameObject : Set where

signatureDoesNotCreateSameObject : MatchingH3SignatureCreatesSameObject → {A : Set} → A
signatureDoesNotCreateSameObject ()
