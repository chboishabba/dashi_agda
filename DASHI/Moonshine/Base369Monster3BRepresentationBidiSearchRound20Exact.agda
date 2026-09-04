module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound20Exact where

open import Agda.Builtin.Bool using (Bool; false; true)

data SearchClass : Set where
  SOURCEBACKED OWNED GENERATED LIVE DOWNSTREAM REJECTED : SearchClass

record Round20Status : Set where
  constructor round20-status
  field
    degree78CoarseCollisionExplicit : Bool
    roleProvenanceResidualSeparatesCandidates : Bool
    degreePlusResidualStrictlyRefinesDegree : Bool
    degreeRecoversResidualRejected : Bool
    roleDifferenceProvesNonisomorphism : Bool
    sameObjectRequiresTwoSidedCarrierEquivalence : Bool
    sameObjectRequiresActionIntertwining : Bool
    actualSuz143ToG2Branch78 : Bool
    actualWilson78SameRestrictedCarrier : Bool
    actualSameObjectWeld : Bool
    coverCoherentTriangle : Bool

canonicalRound20Status : Round20Status
canonicalRound20Status =
  round20-status
    true true true true
    false
    true true
    false false false false

degreeCollisionClass : SearchClass
degreeCollisionClass = OWNED

residualRefinementClass : SearchClass
residualRefinementClass = OWNED

degreeOnlyPromotionClass : SearchClass
degreeOnlyPromotionClass = REJECTED

suz143ConcreteBranchClass : SearchClass
suz143ConcreteBranchClass = LIVE

wilson78RestrictedCarrierClass : SearchClass
wilson78RestrictedCarrierClass = LIVE

sameObjectWeldClass : SearchClass
sameObjectWeldClass = DOWNSTREAM

coverTriangleClass : SearchClass
coverTriangleClass = DOWNSTREAM

------------------------------------------------------------------------
-- Round-20 compression:
--
--   degree 78
--      |
--      +--> Suz143|G2 branch role
--      |
--      +--> Wilson multiplicity role
--
-- is a coarse collision, not an identification.  Reopen the residual:
--
--   (source/cover lineage, restricted carrier, action)
--
-- and promote only after a two-sided carrier equivalence intertwines the SAME
-- restricted action.  Role/provenance separation alone also does not prove the
-- representations are nonisomorphic; the actual class-function/action probe
-- decides that mathematical question.
------------------------------------------------------------------------
