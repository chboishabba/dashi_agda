module DASHI.Core.FrontierRelationStrengthBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FRONTIER RELATION STRENGTH / BIDI
--
-- Repository-native theorem-transport discipline.
--
-- A cross-pollination may be genuinely useful at several different strengths:
-- exact theorem/lemma transport, same-object realization, a shared analytic
-- problem domain, a reusable exact-certificate schema, a reusable proved no-go
-- search pattern, verification/provenance architecture, or analogy only.
--
-- These are not interchangeable.  In particular, a real mathematical
-- neighbourhood relation is not by itself a theorem bridge.
--
-- This owner is DASHI mathematics.  It is not attributed to any external
-- mathematical source whose results happen to instantiate the classification.
------------------------------------------------------------------------

data RelationKind : Set where
  exactTheoremConsumerBridge
  exactLemmaConsumerBridge
  exactSameObjectRealisation
  sharedAnalyticProblemDomain
  exactCertificateSchemaReuse
  provedSearchObstructionReuse
  verificationProvenanceReuse
  analogyOnlyRelation
  : RelationKind

------------------------------------------------------------------------
-- Only relations carrying an exact theorem/lemma consumer bridge may directly
-- transport theorem-closing authority.  Same-object realization is necessary
-- in many programmes but does not itself prove the downstream theorem.
------------------------------------------------------------------------

data TheoremTransferCapability : RelationKind → Set where
  exactTheoremTransfer :
    TheoremTransferCapability exactTheoremConsumerBridge
  exactLemmaTransfer :
    TheoremTransferCapability exactLemmaConsumerBridge

sharedDomainCannotDirectlyTransferTheorem :
  TheoremTransferCapability sharedAnalyticProblemDomain → ⊥
sharedDomainCannotDirectlyTransferTheorem ()

certificateSchemaCannotDirectlyTransferTheorem :
  TheoremTransferCapability exactCertificateSchemaReuse → ⊥
certificateSchemaCannotDirectlyTransferTheorem ()

searchPatternCannotDirectlyTransferTheorem :
  TheoremTransferCapability provedSearchObstructionReuse → ⊥
searchPatternCannotDirectlyTransferTheorem ()

verificationPatternCannotDirectlyTransferTheorem :
  TheoremTransferCapability verificationProvenanceReuse → ⊥
verificationPatternCannotDirectlyTransferTheorem ()

analogyCannotDirectlyTransferTheorem :
  TheoremTransferCapability analogyOnlyRelation → ⊥
analogyCannotDirectlyTransferTheorem ()

sameObjectAloneCannotDirectlyTransferTheorem :
  TheoremTransferCapability exactSameObjectRealisation → ⊥
sameObjectAloneCannotDirectlyTransferTheorem ()

------------------------------------------------------------------------
-- A theorem-bearing cross-pollination carries both the classified relation and
-- the exact object/statement/consumer evidence.  We do not provide a
-- constructor from names, citations, matching constants, or shared vocabulary.
------------------------------------------------------------------------

record GenuineTheoremCrossPollination : Set₁ where
  constructor genuineTheoremCrossPollination
  field
    relation : RelationKind
    transferCapability : TheoremTransferCapability relation
    sourceReference : String
    targetConsumerReference : String
    exactStatementBridge : Set
    sameObjectBridge : Set
    prerequisiteClosure : Set

open GenuineTheoremCrossPollination public

------------------------------------------------------------------------
-- Non-theorem reuse can still be useful and should be typed positively rather
-- than dismissed as "mere analogy".  It just cannot inherit theorem authority.
------------------------------------------------------------------------

data ReuseCapability : RelationKind → Set where
  reuseSharedDomainForSourceSearch :
    ReuseCapability sharedAnalyticProblemDomain
  reuseExactCertificateSchema :
    ReuseCapability exactCertificateSchemaReuse
  reuseProvedSearchObstruction :
    ReuseCapability provedSearchObstructionReuse
  reuseVerificationProvenance :
    ReuseCapability verificationProvenanceReuse
  reuseAnalogyForHeuristicGeneration :
    ReuseCapability analogyOnlyRelation

------------------------------------------------------------------------
-- Coarse labels can hide relation strength.  Two cross-pollinations may both
-- truthfully be called "related" while only one supports theorem transport.
------------------------------------------------------------------------

data RelationState : Set where
  exactConsumerRelated
  sharedDomainRelated
  : RelationState

data CoarseRelatedSurface : Set where related : CoarseRelatedSurface

data FineRelationSurface : Set where
  theoremBearing
  explorationOnly
  : FineRelationSurface

coarseRelated : RelationState → CoarseRelatedSurface
coarseRelated _ = related

fineRelation : RelationState → FineRelationSurface
fineRelation exactConsumerRelated = theoremBearing
fineRelation sharedDomainRelated = explorationOnly

sameRelatedWordDoesNotRecoverStrength :
  fineRelation exactConsumerRelated ≡ fineRelation sharedDomainRelated → ⊥
sameRelatedWordDoesNotRecoverStrength ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FrontierRelationStrengthBoundary : Set where
  constructor frontierRelationStrengthBoundary
  field
    sharedDomainAutomaticallyClosesTargetTheorem : Bool
    sharedDomainAutomaticallyClosesTargetTheoremIsFalse :
      sharedDomainAutomaticallyClosesTargetTheorem ≡ false

    exactCertificateSchemaAutomaticallyClosesTargetTheorem : Bool
    exactCertificateSchemaAutomaticallyClosesTargetTheoremIsFalse :
      exactCertificateSchemaAutomaticallyClosesTargetTheorem ≡ false

    provedNoGoPatternCanLegitimatelyPruneSearch : Bool
    provedNoGoPatternCanLegitimatelyPruneSearchIsTrue :
      provedNoGoPatternCanLegitimatelyPruneSearch ≡ true

    sameObjectRealisationMayBeNecessaryWithoutBeingSufficient : Bool
    sameObjectRealisationMayBeNecessaryWithoutBeingSufficientIsTrue :
      sameObjectRealisationMayBeNecessaryWithoutBeingSufficient ≡ true

    exactTheoremOrLemmaBridgeCanEnterTransportGate : Bool
    exactTheoremOrLemmaBridgeCanEnterTransportGateIsTrue :
      exactTheoremOrLemmaBridgeCanEnterTransportGate ≡ true

canonicalFrontierRelationStrengthBoundary : FrontierRelationStrengthBoundary
canonicalFrontierRelationStrengthBoundary =
  frontierRelationStrengthBoundary
    false refl
    false refl
    true refl
    true refl
    true refl
