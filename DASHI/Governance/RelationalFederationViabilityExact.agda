module DASHI.Governance.RelationalFederationViabilityExact where

-- DASHI-native synthetic observer tests and donor attachments.
-- Source genealogy: Docs/RelationalFederationViabilitySourceAtlas20261129.md
-- p.m., Beer, Aurello, Kimmerer and other source traditions retain authorship;
-- JMD/meta-introspector implementation and Johl Brown discussion origins
-- are separately attributed in the canonical distributed source atlas.
-- No empirical inhabitant, consent, political authority or ecological result.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Interop.DistributedEpistemicFabricSourceAtlasExact as Sources
import DASHI.Interop.DistributedEpistemicPlaneSeparationExact as Planes
import DASHI.Governance.LocalGlobalCouncilGluing as Councils

-- Preserve actual canonical objects rather than minting another atlas.
jmdOrigin : Sources.ContributionAttribution
jmdOrigin = Sources.jmdRepositoryContribution

discussionOrigin : Sources.ContributionAttribution
discussionOrigin = Sources.johlDiscussionContribution

formalOrigin : Sources.ContributionAttribution
formalOrigin = Sources.dashiFormalContribution

technologyRoles : Planes.TechnologyRoleMap
technologyRoles = Planes.canonicalTechnologyRoleMap

-- Deliberately finite toy state: identical visible connectivity can conceal
-- a single shared revocation gate. Not a real network measurement.
data ControlTopology : Set where
  independent sharedGate : ControlTopology

transportAvailable : ControlTopology → Bool
transportAvailable _ = true

independentControl : ControlTopology → Bool
independentControl independent = true
independentControl sharedGate = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

transportControlCollision :
  NF.NonFactorabilityWitness transportAvailable independentControl
transportControlCollision =
  NF.nonFactorabilityWitness independent sharedGate refl trueNotFalse

federationControlDoesNotFactorThroughTransport :
  NF.FactorsThrough transportAvailable independentControl → ⊥
federationControlDoesNotFactorThroughTransport =
  NF.witnessRulesOutEveryFlatFactorisation transportControlCollision

-- Two independent coordinates, not Aurello's actual dataset or scale.
record CommunityFixture : Set where
  constructor community
  field
    material social : Bool

open CommunityFixture

jointFixture : CommunityFixture → Bool
jointFixture (community true s) = s
jointFixture (community false _) = false

materialCollision : NF.NonFactorabilityWitness material jointFixture
materialCollision =
  NF.nonFactorabilityWitness
    (community true true) (community true false) refl trueNotFalse

socialCollision : NF.NonFactorabilityWitness social jointFixture
socialCollision =
  NF.nonFactorabilityWitness
    (community true true) (community false true) refl trueNotFalse

jointDoesNotFactorThroughMaterial :
  NF.FactorsThrough material jointFixture → ⊥
jointDoesNotFactorThroughMaterial =
  NF.witnessRulesOutEveryFlatFactorisation materialCollision

jointDoesNotFactorThroughSocial :
  NF.FactorsThrough social jointFixture → ⊥
jointDoesNotFactorThroughSocial =
  NF.witnessRulesOutEveryFlatFactorisation socialCollision

-- Reuse actual local compatibility contract, not a fabricated empirical family.
compatibleCouncilWitness :
  (locals : Councils.CouncilBasePoint → Councils.LocalCouncilSection) →
  Councils.CompatibleCouncilFamily locals →
  Councils.CompatibleCouncilFamily locals
compatibleCouncilWitness _ witness = witness

-- A joint gate over independently supplied propositions, not a definition
-- or proof of any actual community's viability or legitimacy.
record JointAdmission
  (Material Ecological Authority FutureOptions IndependentAccess : Set) : Set where
  field
    materialWitness : Material
    ecologicalWitness : Ecological
    authorityWitness : Authority
    futureOptionsWitness : FutureOptions
    independentAccessWitness : IndependentAccess

-- In particular the material coordinate does not fabricate authority.
retainAuthority :
  ∀ {M E A F I : Set} → JointAdmission M E A F I → A
retainAuthority = JointAdmission.authorityWitness
