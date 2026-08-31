module DASHI.Governance.ReligiousChildhoodSubjectFormationBidiExact where

------------------------------------------------------------------------
-- RELIGIOUS CHILDHOOD AUTHORITY / SUBJECT-FORMATION BIDI
--
-- Cross-pollination only.  The child-religious-coercion owners supply a
-- dimensional research design; the feminist owners supply non-factorability
-- and positive-recharting structure.  This module does NOT assert that religion
-- is inherently harmful, that compliance proves coercion, or that later
-- alternative spirituality is caused by childhood religious exposure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Governance.ChildReligiousCoercionResearchBridge as Research
import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as Entrapment

------------------------------------------------------------------------
-- Publicly identical religious behaviour can arise from distinct formation
-- routes.  Therefore behavioural conformity cannot generically recover whether
-- the state is authority-dependent attribution or self-endorsed formation.
------------------------------------------------------------------------

data ReligiousFormationState : Set where
  authorityDependentConformity selfEndorsedFormation : ReligiousFormationState

data PublicReligiousBehaviour : Set where
  sameConformingSurface : PublicReligiousBehaviour

data FormationRoute : Set where
  heteronomousRoute selfEndorsedRoute : FormationRoute

publicReligiousBehaviour : ReligiousFormationState → PublicReligiousBehaviour
publicReligiousBehaviour authorityDependentConformity = sameConformingSurface
publicReligiousBehaviour selfEndorsedFormation = sameConformingSurface

formationRoute : ReligiousFormationState → FormationRoute
formationRoute authorityDependentConformity = heteronomousRoute
formationRoute selfEndorsedFormation = selfEndorsedRoute

formationRouteDistinct :
  formationRoute authorityDependentConformity
  ≡ formationRoute selfEndorsedFormation → ⊥
formationRouteDistinct ()

publicBehaviourCannotRecoverFormationRoute :
  INF.FactorsThrough publicReligiousBehaviour formationRoute → ⊥
publicBehaviourCannotRecoverFormationRoute =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      authorityDependentConformity
      selfEndorsedFormation
      refl
      formationRouteDistinct)

------------------------------------------------------------------------
-- Attribution, assent, compliance, identity, and subject formation remain
-- distinct typed positions rather than one inferred scalar.
------------------------------------------------------------------------

data ReligiousSubjectPosition : Set where
  doctrineExposed
  threatUnderstood
  threatFeared
  behaviourCompliant
  identityAttributed
  identitySelfEndorsed
  subjectInMaking
  : ReligiousSubjectPosition

identityAttributed≠identitySelfEndorsed :
  identityAttributed ≡ identitySelfEndorsed → ⊥
identityAttributed≠identitySelfEndorsed ()

behaviourCompliant≠identitySelfEndorsed :
  behaviourCompliant ≡ identitySelfEndorsed → ⊥
behaviourCompliant≠identitySelfEndorsed ()

threatFeared≠identitySelfEndorsed :
  threatFeared ≡ identitySelfEndorsed → ⊥
threatFeared≠identitySelfEndorsed ()

identitySelfEndorsed≠subjectInMaking :
  identitySelfEndorsed ≡ subjectInMaking → ⊥
identitySelfEndorsed≠subjectInMaking ()

------------------------------------------------------------------------
-- Existing owners are retained as independent theorem surfaces.
------------------------------------------------------------------------

religiousResearchBoundary : Research.ChildReligiousCoercionResearchBridge
religiousResearchBoundary = Research.canonicalChildReligiousCoercionResearchBridge

religiousEntrapmentBoundary : Entrapment.DependentReligiousEntrapmentBoundary
religiousEntrapmentBoundary = Entrapment.canonicalDependentReligiousEntrapmentBoundary

representabilityStillDoesNotRecoverSubjectPosition :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
representabilityStillDoesNotRecoverSubjectPosition =
  Subject.categoryVisibilityCannotRecoverSubjectPosition

publicCategoryStillDoesNotRecoverSubjectFormation :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
publicCategoryStillDoesNotRecoverSubjectFormation =
  Trinh.publicCategoryCannotRecoverSubjectFormation

------------------------------------------------------------------------
-- A positive rechart must add a residual that actually separates states the
-- inherited chart collapsed.  This imports the exact generic theorem rather
-- than creating a special religious or feminist recharting calculus.
------------------------------------------------------------------------

data FormationSituated : Set where
  imposedNamedState selfMakingState : FormationSituated

data InheritedReligiousCategory : Set where
  inheritedBelieverCategory : InheritedReligiousCategory

data FormationResidual : Set where
  imposedResidual selfMakingResidual : FormationResidual

inheritedReligiousCategory : FormationSituated → InheritedReligiousCategory
inheritedReligiousCategory imposedNamedState = inheritedBelieverCategory
inheritedReligiousCategory selfMakingState = inheritedBelieverCategory

formationResidual : FormationSituated → FormationResidual
formationResidual imposedNamedState = imposedResidual
formationResidual selfMakingState = selfMakingResidual

canonicalFormationPositiveRecharting :
  Feminist.PositiveRecharting inheritedReligiousCategory
canonicalFormationPositiveRecharting =
  Feminist.positive-recharting
    formationResidual
    imposedNamedState
    selfMakingState
    refl
    (λ ())

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

record ReligiousChildhoodSubjectFormationBoundary : Set where
  constructor religious-childhood-subject-formation-boundary
  field
    complianceEqualsAutonomousBelief : Bool
    attributedIdentityEqualsSelfEndorsedIdentity : Bool
    fearEqualsAssent : Bool
    strongBeliefEqualsCoercion : Bool
    ordinaryReligiousUpbringingEqualsEntrapment : Bool
    laterAlternativeSpiritualityProvesPriorCoercion : Bool
    laterAlternativeSpiritualityIsNecessarilyCausedByPriorReligion : Bool
    publicBehaviourDeterminesFormationRoute : Bool
    positiveRechartRequiresNewResidual : Bool

canonicalReligiousChildhoodSubjectFormationBoundary :
  ReligiousChildhoodSubjectFormationBoundary
canonicalReligiousChildhoodSubjectFormationBoundary =
  religious-childhood-subject-formation-boundary
    false false false false false false false false true
