module DASHI.Governance.AsymmetricReflectionPropositionLocality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Typed relational orbit / asymmetric-reflection core.
--
-- A relation is not a crime predicate, knowledge predicate, facilitation
-- predicate, or participation predicate.  Every promotion requires its own
-- proposition-local witness.  This module is structural: it does not infer
-- wrongdoing, motive, or psychology from public association data.
------------------------------------------------------------------------

data RelationKind : Set where
  namedInRecord social financial political travel employment evidentiary : RelationKind

record RelationalOrbitSystem : Set₁ where
  field
    Actor : Set
    Related : RelationKind → Actor → Actor → Set
    Knowledge : Actor → Actor → Set
    Facilitation : Actor → Actor → Set
    Participation : Actor → Actor → Set

open RelationalOrbitSystem public

record RelationPromotion
    (R : RelationalOrbitSystem)
    (kind : RelationKind)
    (source target : Actor R) : Set₁ where
  field
    relation : Related R kind source target
    PropositionWitness : Set
    propositionWitness : PropositionWitness

open RelationPromotion public

------------------------------------------------------------------------
-- No automatic promotion chain.  The intermediate propositions remain
-- independently witnessed even when a typed relation is established.
------------------------------------------------------------------------

data RelationAutomaticallyProvesKnowledge
    (R : RelationalOrbitSystem)
    {kind : RelationKind}
    {source target : Actor R}
    (r : Related R kind source target) : Set where

data KnowledgeAutomaticallyProvesFacilitation
    (R : RelationalOrbitSystem)
    {source target : Actor R}
    (k : Knowledge R source target) : Set where

data FacilitationAutomaticallyProvesParticipation
    (R : RelationalOrbitSystem)
    {source target : Actor R}
    (f : Facilitation R source target) : Set where

relationDoesNotAutomaticallyProveKnowledge :
  ∀ {R kind source target} {r : Related R kind source target} →
  RelationAutomaticallyProvesKnowledge R r → ⊥
relationDoesNotAutomaticallyProveKnowledge ()

knowledgeDoesNotAutomaticallyProveFacilitation :
  ∀ {R source target} {k : Knowledge R source target} →
  KnowledgeAutomaticallyProvesFacilitation R k → ⊥
knowledgeDoesNotAutomaticallyProveFacilitation ()

facilitationDoesNotAutomaticallyProveParticipation :
  ∀ {R source target} {f : Facilitation R source target} →
  FacilitationAutomaticallyProvesParticipation R f → ⊥
facilitationDoesNotAutomaticallyProveParticipation ()

------------------------------------------------------------------------
-- Proposition-locality must be role-equivariant at the level of promotion
-- rules: equivalent evidentiary support is not allowed one burden for insiders
-- and another merely because of insider/outsider status.
------------------------------------------------------------------------

data BoundaryRole : Set where
  inside outside : BoundaryRole

record PropositionLocalitySystem : Set₁ where
  field
    Actor : Set
    Evidence : Actor → Set
    Proposition : Actor → Set
    role : Actor → BoundaryRole
    Supports : (actor : Actor) → Evidence actor → Proposition actor → Set

open PropositionLocalitySystem public

record RoleEquivariantPromotion (P : PropositionLocalitySystem) : Set₁ where
  field
    EquivalentEvidence :
      ∀ {x y} → Evidence P x → Evidence P y → Set
    EquivalentProposition :
      ∀ {x y} → Proposition P x → Proposition P y → Set
    transportSupport :
      ∀ {x y ex ey px py} →
      EquivalentEvidence ex ey →
      EquivalentProposition px py →
      Supports P x ex px →
      Supports P y ey py

open RoleEquivariantPromotion public

record AsymmetricPropositionLocalityWitness
    (P : PropositionLocalitySystem) : Set₁ where
  field
    insider outsider : Actor P
    insiderIsInside : role P insider ≡ inside
    outsiderIsOutside : role P outsider ≡ outside
    insiderEvidence : Evidence P insider
    outsiderEvidence : Evidence P outsider
    insiderProposition : Proposition P insider
    outsiderProposition : Proposition P outsider
    EquivalentEvidence : Set
    equivalentEvidence : EquivalentEvidence
    EquivalentProposition : Set
    equivalentProposition : EquivalentProposition
    insiderRequiresSupport : Supports P insider insiderEvidence insiderProposition
    OutsiderPromotionWithoutSupport : Set
    outsiderPromotionWithoutSupport : OutsiderPromotionWithoutSupport

open AsymmetricPropositionLocalityWitness public

------------------------------------------------------------------------
-- Corrective reachability: can later evidence still change the accountability
-- / classification state?  The inside/outside comparison is a structural
-- symmetry test, not a claim about any named polity without empirical input.
------------------------------------------------------------------------

record CorrectiveReachabilitySystem : Set₁ where
  field
    Actor : Set
    Evidence : Set
    Classification : Actor → Set
    current : (actor : Actor) → Classification actor
    revise : (actor : Actor) → Evidence → Classification actor

open CorrectiveReachabilitySystem public

record CorrectiveReachable
    (C : CorrectiveReachabilitySystem)
    (actor : Actor C) : Set₁ where
  field
    evidence : Evidence C
    RevisionDiffers :
      Classification C actor → Classification C actor → Set
    differs : RevisionDiffers (current C actor) (revise C actor evidence)

open CorrectiveReachable public

record AsymmetricCorrectiveReachability
    (C : CorrectiveReachabilitySystem) : Set₁ where
  field
    insideActor outsideActor : Actor C
    InsideBlocked : Set
    insideBlocked : InsideBlocked
    outsideReachable : CorrectiveReachable C outsideActor

open AsymmetricCorrectiveReachability public

------------------------------------------------------------------------
-- Externalising attribution is kept as a typed mapping only.  It does not
-- assert unconscious psychological projection or establish causation.
------------------------------------------------------------------------

record ExternalisingBoundaryOperator : Set₁ where
  field
    InternalResidual : Set
    ExternalCarrier : Set
    Attribution : Set
    externalise : InternalResidual → ExternalCarrier → Attribution

open ExternalisingBoundaryOperator public

data ExternalisingOperatorIsPsychologicalDiagnosis
    (E : ExternalisingBoundaryOperator) : Set where

externalisingOperatorDoesNotDiagnose :
  ∀ {E} → ExternalisingOperatorIsPsychologicalDiagnosis E → ⊥
externalisingOperatorDoesNotDiagnose ()
