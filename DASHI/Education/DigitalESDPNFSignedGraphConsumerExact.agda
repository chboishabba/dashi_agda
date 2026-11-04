{-# OPTIONS --safe #-}
module DASHI.Education.DigitalESDPNFSignedGraphConsumerExact where

------------------------------------------------------------------------
-- ESD WORLD -> EXISTING SIGNED PNF TRIANGLE: SAME-OBJECT REUSE
--
-- The 1/3/-9 PNF residual triangle belongs to the canonical owner
-- DASHI.Interop.PNFSignedResidualDelta0Exact.  This ESD adapter keeps
-- its literal signed energy and operator, and records source-specific
-- evidence states without manufacturing a reviewed finding.
--
-- The Karp-21 finite Boolean-cut iff owner is currently on a separate
-- PR (#1445); no unmerged Karp module is silently imported here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
import DASHI.Interop.PNFSignedResidualDelta0Exact as PNF
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World

record SourceIndexedSignedTriangle
    (scope : World.StudyWorldScope) : Set₂ where
  constructor source-indexed-signed-triangle
  field
    world : World.AccountedStudyWorld scope
    position0 position1 position2 : World.StudyPart scope
    axis : World.Axis scope

    originalAccount0 :
      World.PartAxisAccounting scope
        (World.study position0) (World.part position0) axis
    originalAccount1 :
      World.PartAxisAccounting scope
        (World.study position1) (World.part position1) axis
    originalAccount2 :
      World.PartAxisAccounting scope
        (World.study position2) (World.part position2) axis

    firstIsWorld :
      originalAccount0 ≡
      World.accounting world
        (World.study position0) (World.part position0) axis
    secondIsWorld :
      originalAccount1 ≡
      World.accounting world
        (World.study position1) (World.part position1) axis
    thirdIsWorld :
      originalAccount2 ≡
      World.accounting world
        (World.study position2) (World.part position2) axis

    -- This field is a candidate NUMERIC/GRAPH VIEW, not an empirical
    -- effect-size estimate, review decision or semantic truth label.
    candidateSignedField : PNF.TriangleField

open SourceIndexedSignedTriangle public

-- Exact canonical integer signed-energy identity on the SAME field
-- selected for this research world.  No new invented edge weights.
signedESDQuadraticIsExact :
  {scope : World.StudyWorldScope} →
  (consumer : SourceIndexedSignedTriangle scope) →
  PNF.signedEdgeEnergy (candidateSignedField consumer) ≡
  PNF.dot (candidateSignedField consumer)
    (PNF.signedResidualDelta0 (candidateSignedField consumer))
signedESDQuadraticIsExact consumer =
  PNF.signedIncidenceEnergyIdentity (candidateSignedField consumer)

-- A signed graph can be used to nominate conflict cuts but cannot
-- turn source-pending statuses into admitted reviewed observations.
data SignedCutScoreCreatesReviewedESDFinding : Set where

signedCutScoreCannotCreateReviewedFinding :
  SignedCutScoreCreatesReviewedESDFinding → ⊥
signedCutScoreCannotCreateReviewedFinding ()
