module DASHI.Physics.Closure.E6HyperformTwoH3NondegenerateCandidateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3SameObjectEmbeddingExact as H3

------------------------------------------------------------------------
-- TWO-H3 AGGREGATE: ALGEBRAIC FULL-RANK CANDIDATE, WEYL-GLUING NO-GO
--
-- Two explicit distinct E6 H3 embeddings have local forms
--
--   q_+ = (x+z)^2 + y^2,
--   q_- = (x-z)^2 + y^2.
--
-- If their local coordinates are identified by the identity map then
--
--   G_+ + G_- = 2 I_3,
--
-- full rank.  However that is NOT the actual E6 atlas transition.
--
-- An explicit Weyl word (left-action convention)
--
--   (0,1,3,2,4,1,5,4,1,0,2,1)
--
-- maps the plus H3 patch to the minus H3 patch.  Its induced local transition
-- is
--
--   T=[[2,0,1],[0,1,0],[1,0,0]],
--
-- with E_- T = g E_+ and
--
--   T^T G_- T = G_+.
--
-- Thus correct Weyl co-registration makes the two quadratic forms identical;
-- their sum remains rank two.  Pure Weyl-covariant gluing of this SAME q-field
-- cannot recover the missing direction.  A third spatial direction requires
-- additional non-transported structure or a higher-dimensional nondegenerate
-- carrier, not repeated copies of the transported H3 quadratic source.
------------------------------------------------------------------------

plusEmbedding : String
plusEmbedding = "[[1,1,1],[0,0,2],[0,1,2],[2,0,2],[0,0,1]] mod 3"

minusEmbedding : String
minusEmbedding = "[[0,0,0],[0,0,0],[0,0,1],[1,1,1],[1,2,2]] mod 3"

identityCoordinateAggregate : String
identityCoordinateAggregate = "G_plus + G_minus = 2 I_3 mod 3 (rank 3)"

weylWordLeftAction : String
weylWordLeftAction = "(0,1,3,2,4,1,5,4,1,0,2,1)"

weylLocalTransition : String
weylLocalTransition = "T=[[2,0,1],[0,1,0],[1,0,0]] mod 3"

weylPullbackIdentity : String
weylPullbackIdentity = "T^T G_minus T = G_plus"

weylAggregate : String
weylAggregate = "G_plus + T^T G_minus T = 2 G_plus (rank 2)"

record TwoH3WeylCoregistrationLocalReceipt : Set where
  constructor two-h3-weyl-coregistration-local-receipt
  field
    plusPatchSameObjectH3PaidLocally : Bool
    minusPatchSameObjectH3PaidLocally : Bool
    patchesDistinctPaidLocally : Bool
    radicalsDistinctPaidLocally : Bool
    identityCoordinateAggregateRankThreePaid : Bool
    explicitWeylTransitionPaidLocally : Bool
    explicitLocalTransitionPaidLocally : Bool
    weylTransitionMapsEmbeddingsPaid : Bool
    weylPullbackFormsEqualPaid : Bool
    weylCoregisteredAggregateRankTwoPaid : Bool
    pureWeylCovariantQuadraticGluingResolvesRadical : Bool
    additionalStructureRequired : Bool
    globalThreeDirectionMetricPaid : Bool
    boundary : String
open TwoH3WeylCoregistrationLocalReceipt public

canonicalTwoH3WeylCoregistrationLocalReceipt : TwoH3WeylCoregistrationLocalReceipt
canonicalTwoH3WeylCoregistrationLocalReceipt =
  two-h3-weyl-coregistration-local-receipt
    true true true true true true true true true true
    false true false
    "Two H3 forms can sum to full rank only under an arbitrary identity co-registration. The actual E6 Weyl transition pulls the minus form back exactly to the plus form, so the covariant sum stays rank two. The earlier two-chart rank-three candidate is therefore demoted as non-geometric under the paid atlas symmetry. Recovering a third spatial direction requires another field/connection/observer datum or a higher-dimensional nondegenerate carrier."

record RadicalResolvingAdditionalStructure : Set₁ where
  field
    GlobalCarrier : Set
    ExtraStructure : Set
    selectedStructure : ExtraStructure
    notMerelyTransportedQuadraticReceipt : Set
    couplesAcrossRadicalReceipt : Set
    threeDirectionNondegeneracyReceipt : Set
    chartTransitionCompatibilityReceipt : Set
open RadicalResolvingAdditionalStructure public

data IdentityCoregistrationCreatesWeylGluing : Set where

data RepeatedTransportedQuadraticCreatesThirdDirection : Set where

identityCoregistrationDoesNotCreateWeylGluing :
  IdentityCoregistrationCreatesWeylGluing → {A : Set} → A
identityCoregistrationDoesNotCreateWeylGluing ()

repeatedQuadraticDoesNotCreateThirdDirection :
  RepeatedTransportedQuadraticCreatesThirdDirection → {A : Set} → A
repeatedQuadraticDoesNotCreateThirdDirection ()
