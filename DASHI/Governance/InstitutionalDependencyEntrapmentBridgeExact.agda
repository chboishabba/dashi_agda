module DASHI.Governance.InstitutionalDependencyEntrapmentBridgeExact where

------------------------------------------------------------------------
-- INSTITUTIONAL DEPENDENCY -> ENTRAPMENT BRIDGE
--
-- An effectively irreplaceable school, hospital, care provider or other
-- institution can increase dependency and exit cost without thereby becoming
-- coercive.  Entrapment requires a second witness that the dependency is used
-- through refusal restriction / meaningful penalty / closure mechanisms.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.DelegatedEssentialServiceAuthorityExact as Service
import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.DependentReligiousEntrapmentCandidateExact as ReligiousEntrapment

record InstitutionalConstraintUse : Set where
  constructor institutionalConstraintUse
  field
    refusalRestricted : Bool
    meaningfulPenalty : Bool
    alternativeInformationRestricted : Bool
    authorityClosure : Bool
    dependencyUsedAsLeverage : Bool

open InstitutionalConstraintUse public

record InstitutionalEntrapmentCandidate
    (provider : Service.DelegatedServiceProvider) : Set where
  constructor institutionalEntrapmentCandidate
  field
    providerDependency : Service.EffectiveProviderDependency provider
    constraintUse : InstitutionalConstraintUse
    refusalRestrictedWitness : refusalRestricted constraintUse ≡ true
    meaningfulPenaltyWitness : meaningfulPenalty constraintUse ≡ true
    dependencyLeverageWitness : dependencyUsedAsLeverage constraintUse ≡ true

open InstitutionalEntrapmentCandidate public

------------------------------------------------------------------------
-- Absence of an accessible alternative is therefore a dependency witness, not
-- a coercion theorem.  This is the institutional-scale analogue of the child
-- kernel's separation of dependency from coercive interaction.
------------------------------------------------------------------------

data EffectiveMonopolyPromotesEntrapment : Set where

data DoctrinalIdentityPromotesEntrapment : Set where

data InstitutionalEntrapmentPromotesLegalConfinement : Set where

effectiveMonopolyDoesNotPromoteEntrapment :
  EffectiveMonopolyPromotesEntrapment → ⊥
effectiveMonopolyDoesNotPromoteEntrapment ()

doctrinalIdentityDoesNotPromoteEntrapment :
  DoctrinalIdentityPromotesEntrapment → ⊥
doctrinalIdentityDoesNotPromoteEntrapment ()

institutionalEntrapmentDoesNotPromoteLegalConfinement :
  InstitutionalEntrapmentPromotesLegalConfinement → ⊥
institutionalEntrapmentDoesNotPromoteLegalConfinement ()

------------------------------------------------------------------------
-- Cross-scale correspondence: same low-level coordinates, different domains.
------------------------------------------------------------------------

record DependencyExitTopology : Set where
  constructor dependencyExitTopology
  field
    materialDependency : Nat
    practicalExitCost : Nat
    socialBelongingCost : Nat
    epistemicAlternativeRestriction : Nat
    refusalPenalty : Nat

open DependencyExitTopology public

childReligiousTopology : DependencyExitTopology
childReligiousTopology = dependencyExitTopology 10 10 10 10 10

institutionalServiceTopology : DependencyExitTopology
institutionalServiceTopology = dependencyExitTopology 10 10 0 0 0

-- Matching some coordinates does not identify the systems.
data SharedTopologyPromotesDomainIdentity : Set where

sharedTopologyDoesNotPromoteDomainIdentity : SharedTopologyPromotesDomainIdentity → ⊥
sharedTopologyDoesNotPromoteDomainIdentity ()

record InstitutionalDependencyEntrapmentBoundary : Set where
  constructor institutionalDependencyEntrapmentBoundary
  field
    effectiveMonopolyRaisesDependencySurface : Bool
    effectiveMonopolyEqualsCoercion : Bool
    coerciveUseRequiresAdditionalWitness : Bool
    institutionalEntrapmentEqualsFalseImprisonment : Bool
    childAndInstitutionalTopologiesCanBeCompared : Bool
    childAndInstitutionalSystemsIdentified : Bool

canonicalInstitutionalDependencyEntrapmentBoundary :
  InstitutionalDependencyEntrapmentBoundary
canonicalInstitutionalDependencyEntrapmentBoundary =
  institutionalDependencyEntrapmentBoundary true false true false true false
