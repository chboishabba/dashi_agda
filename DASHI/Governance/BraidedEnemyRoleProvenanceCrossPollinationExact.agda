module DASHI.Governance.BraidedEnemyRoleProvenanceCrossPollinationExact where

------------------------------------------------------------------------
-- BRAID / PATTERNMIND / AMALEK / SETTLER-ENEMY CROSS-POLLINATION
--
-- Robin Wall Kimmerer,
-- "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge, and the
-- Teachings of Plants".  Milkweed Editions, 2013.  No DOI asserted here.
-- Bounded source role: inspiration for provenance-preserving braids,
-- reciprocity and relation; DASHI does not claim to formalise or substitute
-- living Potawatomi/Indigenous knowledge.
--
-- Reuven Firestone,
-- "Who Is the Enemy?", chapter in "Holy War in Judaism: The Fall and Rise of
-- a Controversial Idea", Oxford University Press, 2012.
-- DOI 10.1093/acprof:oso/9780199860302.003.0007.
-- Bounded role: reception-history vocabulary distinguishing ancient referent,
-- later role-binding/analogy, and command transport.
--
-- The existing SettlerEnemyAbstractionExact supplies a finite information-loss
-- witness: a rhetorical absolute-enemy category can collapse combatant and
-- civilian actor distinctions.  Structural comparison is not explicit lexical
-- use and does not make histories identical.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.KimmererBraidingAcknowledgement as Kimmerer
import DASHI.Culture.PatternMindReciprocityLoveBridge as Pattern
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Enemy
import DASHI.Governance.FutureSafeCausalCompressionExact as Compression

------------------------------------------------------------------------
-- A provenance braid keeps strands distinct rather than forcing them into one
-- universal historical identity.
------------------------------------------------------------------------

data StrandKind : Set where
  scripturalReceptionStrand : StrandKind
  contemporaryPoliticalRhetoricStrand : StrandKind
  indigenousColonialHistoryStrand : StrandKind
  relationalEpistemologyStrand : StrandKind
  policyActionStrand : StrandKind

record ProvenanceStrand : Set where
  constructor provenanceStrand
  field
    kind : StrandKind
    provenancePreserved : Bool
    authorityScopePreserved : Bool

open ProvenanceStrand public

record BraidedComparison : Set where
  constructor braidedComparison
  field
    strands : List ProvenanceStrand
    forcedFusion : Bool
    sourceSpecificWarrantsRetained : Bool

open BraidedComparison public

canonicalEnemyRoleBraid : BraidedComparison
canonicalEnemyRoleBraid = braidedComparison
  ( provenanceStrand scripturalReceptionStrand true true
  ∷ provenanceStrand contemporaryPoliticalRhetoricStrand true true
  ∷ provenanceStrand indigenousColonialHistoryStrand true true
  ∷ provenanceStrand relationalEpistemologyStrand true true
  ∷ provenanceStrand policyActionStrand true true
  ∷ [] )
  false true

------------------------------------------------------------------------
-- Existing exact theorems reused.
------------------------------------------------------------------------

combatantCivilianCompressionWitness :
  Enemy.rhetoricalCompression Enemy.hamasActor
  ≡ Enemy.rhetoricalCompression Enemy.palestinianCivilianPopulation
combatantCivilianCompressionWitness = Enemy.combatantAndCivilianCollapseUnderCompression

absoluteEnemyCompressionNotInjective : ¬ Enemy.CompressionInjective
absoluteEnemyCompressionNotInjective = Enemy.rhetoricalCompressionIsNotInjective

indigenousComparisonRemainsStructural :
  Enemy.comparisonAuthority Enemy.indigenousAustraliaSettlerStructure
  ≡ Enemy.structuralHomologyOnly
indigenousComparisonRemainsStructural = Enemy.australianComparisonIsStructuralOnly

amalekCommandNeedsSeparateTransportEvidence : Bool
amalekCommandNeedsSeparateTransportEvidence =
  Amalek.commandTransportRequiresSeparateEvidence Amalek.canonicalAmalekBoundary

patternMindReciprocityRequiresFreedom : Bool
patternMindReciprocityRequiresFreedom =
  Pattern.reciprocityRequiresFreedom Pattern.canonicalPatternMindReciprocityLoveBridge

kimmererLivingPracticeNotSubstituted : Bool
kimmererLivingPracticeNotSubstituted =
  Kimmerer.livingPracticeSubstitutedClaim Kimmerer.canonicalKimmererBraidingAcknowledgement

------------------------------------------------------------------------
-- New cross-layer no-go surfaces.
------------------------------------------------------------------------

data StructuralHomologyPromotesLiteralEnemyRole : Set where

data EnemyRolePromotesCollectiveGuilt : Set where

data RelationBeforeObjectPromotesGroupEssentialism : Set where

data ProvenanceBraidPromotesCulturalAuthority : Set where

structuralHomologyDoesNotPromoteLiteralEnemyRole :
  StructuralHomologyPromotesLiteralEnemyRole → ⊥
structuralHomologyDoesNotPromoteLiteralEnemyRole ()

enemyRoleDoesNotPromoteCollectiveGuilt : EnemyRolePromotesCollectiveGuilt → ⊥
enemyRoleDoesNotPromoteCollectiveGuilt ()

relationBeforeObjectDoesNotPromoteGroupEssentialism :
  RelationBeforeObjectPromotesGroupEssentialism → ⊥
relationBeforeObjectDoesNotPromoteGroupEssentialism ()

braidDoesNotPromoteCulturalAuthority : ProvenanceBraidPromotesCulturalAuthority → ⊥
braidDoesNotPromoteCulturalAuthority ()

record BraidedEnemyRoleBoundary : Set where
  constructor braidedEnemyRoleBoundary
  field
    sourceStrandsRemainDistinct : Bool
    contextualRoleEqualsActorIdentity : Bool
    structuralHomologyEqualsLexicalUse : Bool
    absoluteEnemyCompressionCanLoseActorResolution : Bool
    reciprocityWithoutFreedomAccepted : Bool
    indigenousKnowledgeClaimedByFormalAnalogy : Bool
    ancientCommandAutomaticallyTransportedToPolicy : Bool

canonicalBraidedEnemyRoleBoundary : BraidedEnemyRoleBoundary
canonicalBraidedEnemyRoleBoundary =
  braidedEnemyRoleBoundary true false false true false false false
