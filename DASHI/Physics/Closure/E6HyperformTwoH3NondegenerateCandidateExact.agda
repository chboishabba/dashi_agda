module DASHI.Physics.Closure.E6HyperformTwoH3NondegenerateCandidateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3SameObjectEmbeddingExact as H3

------------------------------------------------------------------------
-- TWO-H3 NONDEGENERATE AGGREGATE CANDIDATE
--
-- One H3 chart is rank-two because it has a one-dimensional radical.  Two
-- explicit, distinct E6 H3 embeddings can be pulled back to one abstract
-- ternary coordinate carrier with forms
--
--   q_+ = (x+z)^2 + y^2,
--   q_- = (x-z)^2 + y^2.
--
-- Their Gram matrices satisfy
--
--   G_+ + G_- = 2 I_3  (mod 3),
--
-- which is full rank.  The two projective H3 images are genuinely distinct,
-- have different E6 null radical lines, and intersect in exactly one E6 root
-- line.  Thus two co-registered H3 probes are algebraically sufficient to
-- resolve the missing local direction.
--
-- What remains nontrivial is the co-registration/atlas semantics: the common
-- abstract coordinate u used to add the pullbacks must arise from a paid Weyl
-- transition/overlap construction.  A one-root-line projective intersection
-- does not by itself supply that identification.
------------------------------------------------------------------------

plusEmbedding : String
plusEmbedding = "[[1,1,1],[0,0,2],[0,1,2],[2,0,2],[0,0,1]] mod 3"

minusEmbedding : String
minusEmbedding = "[[0,0,0],[0,0,0],[0,0,1],[1,1,1],[1,2,2]] mod 3"

plusGram : String
plusGram = "[[1,0,1],[0,1,0],[1,0,1]]"

minusGram : String
minusGram = "[[1,0,2],[0,1,0],[2,0,1]]"

aggregateGram : String
aggregateGram = "G_plus + G_minus = 2 I_3 mod 3"

plusRadical : String
plusRadical = "[(0,1,1,0,2)]"

minusRadical : String
minusRadical = "[(0,0,1,2,0)]"

commonProjectiveRootLine : String
commonProjectiveRootLine = "[(0,0,1,1,0)]"

record TwoH3NondegenerateLocalReceipt : Set where
  constructor two-h3-nondegenerate-local-receipt
  field
    plusPatchSameObjectH3PaidLocally : Bool
    minusPatchSameObjectH3PaidLocally : Bool
    patchesDistinctPaidLocally : Bool
    radicalsDistinctPaidLocally : Bool
    projectiveIntersectionExactlyOneRootLinePaid : Bool
    aggregateGramFullRankThreePaid : Bool
    commonAbstractCoordinateCoRegistrationPaid : Bool
    weylTransitionRealizesCoRegistrationPaid : Bool
    globalThreeDirectionMetricPaid : Bool
    boundary : String
open TwoH3NondegenerateLocalReceipt public

canonicalTwoH3NondegenerateLocalReceipt : TwoH3NondegenerateLocalReceipt
canonicalTwoH3NondegenerateLocalReceipt =
  two-h3-nondegenerate-local-receipt
    true true true true true true
    false false false
    "Two explicit distinct E6 H3 patches have complementary local radicals and their pulled-back Gram matrices sum to full-rank 2I3. This proves that a two-patch aggregate can algebraically resolve the radical if the patch coordinates are co-registered. The required Weyl/overlap co-registration is not inferred from the one-root-line intersection and remains the exact atlas/descent obligation."

record TwoH3CoRegistrationWeld : Set₁ where
  field
    GlobalCarrier : Set
    PlusLocalCarrier : Set
    MinusLocalCarrier : Set
    plusToGlobal : PlusLocalCarrier → GlobalCarrier
    minusToGlobal : MinusLocalCarrier → GlobalCarrier
    overlapReceipt : Set
    weylTransitionReceipt : Set
    pullbackCompatibilityReceipt : Set
    aggregateMetricIndependenceReceipt : Set
open TwoH3CoRegistrationWeld public

data TwoFormsCreatePhysicalCoRegistration : Set where

twoFormsDoNotCreateCoRegistration : TwoFormsCreatePhysicalCoRegistration → {A : Set} → A
twoFormsDoNotCreateCoRegistration ()
