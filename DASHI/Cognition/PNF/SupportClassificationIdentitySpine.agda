module DASHI.Cognition.PNF.SupportClassificationIdentitySpine where

open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EvidenceClassificationEdge as Classification
import DASHI.Cognition.PNF.ParserArgumentSupportGluing as Support
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

------------------------------------------------------------------------
-- One reference spine, zero new semantic edge implementations.
------------------------------------------------------------------------

StructuralSupport : Support.ParserArgumentProjection → Set
StructuralSupport = Support.ParserArgumentSupportWitness

CandidateClassification : Set
CandidateClassification = Classification.CandidateClassificationEdge

DeductiveIdentity : Set
DeductiveIdentity = Identity.IdentityFibreMember

supportCannotPromoteIdentity :
  Support.SupportIdentityPromotionPermission → ⊥
supportCannotPromoteIdentity = Support.supportAloneCannotCreateIdentity

classificationCannotPromoteIdentity :
  Classification.CandidateClassificationIdentityPermission → ⊥
classificationCannotPromoteIdentity =
  Classification.candidateClassificationCannotPromoteIdentity

record SupportClassificationIdentityBoundary : Set where
  constructor supportClassificationIdentityBoundary
  field
    supportPromotionBlocked :
      Support.SupportIdentityPromotionPermission → ⊥
    classificationPromotionBlocked :
      Classification.CandidateClassificationIdentityPermission → ⊥

open SupportClassificationIdentityBoundary public

canonicalSupportClassificationIdentityBoundary :
  SupportClassificationIdentityBoundary
canonicalSupportClassificationIdentityBoundary =
  supportClassificationIdentityBoundary
    supportCannotPromoteIdentity
    classificationCannotPromoteIdentity
