module DASHI.Ontology.ProgenitorParentPNFPullbackLattice where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Reasoning.TypedHyperfabricCore as Fabric
import DASHI.Cognition.PNF.PNFEvidenceHyperformalism as PNF

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge

------------------------------------------------------------------------
-- Parent predicates form the local PNF lattice over the richer carrier.
--
-- We use Boolean predicates only as decidable local surfaces.  A predicate is
-- not the carrier and a failed predicate is not promoted to global ontology
-- truth.  Meet/join are pointwise conjunction/disjunction over ParentCarrier.
------------------------------------------------------------------------

ParentPredicate : Set
ParentPredicate = ParentCarrier → Bool

boolAnd : Bool → Bool → Bool
boolAnd true true = true
boolAnd _ _ = false

boolOr : Bool → Bool → Bool
boolOr false false = false
boolOr _ _ = true

infixr 6 _⊓p_
infixr 5 _⊔p_

_⊓p_ : ParentPredicate → ParentPredicate → ParentPredicate
(p ⊓p q) carrier = boolAnd (p carrier) (q carrier)

_⊔p_ : ParentPredicate → ParentPredicate → ParentPredicate
(p ⊔p q) carrier = boolOr (p carrier) (q carrier)

progenitorP geneticP gameteP mitochondrialP gestationalP : ParentPredicate
genealogicalParentP intendedParentP legalParentP socialParentP caregiverP : ParentPredicate

progenitorP carrier = progenitorRelation (carrierRelation carrier)
geneticP carrier = geneticContributor (carrierRelation carrier)
gameteP carrier = gameteContributor (carrierRelation carrier)
mitochondrialP carrier = mitochondrialContributor (carrierRelation carrier)
gestationalP carrier = gestationalContributor (carrierRelation carrier)
genealogicalParentP carrier = genealogicalParent (carrierRelation carrier)
intendedParentP carrier = intendedParent (carrierRelation carrier)
legalParentP carrier = legalParent (carrierRelation carrier)
socialParentP carrier = socialParent (carrierRelation carrier)
caregiverP carrier = caregiver (carrierRelation carrier)

-- Two useful composite lattice elements.  They are intentionally not equal.
geneticAndGenealogicalParentP : ParentPredicate
geneticAndGenealogicalParentP = geneticP ⊓p genealogicalParentP

legalOrSocialParentP : ParentPredicate
legalOrSocialParentP = legalParentP ⊔p socialParentP

anonymousDonorSeparatesPredicateCoordinates :
  geneticP anonymousDonorCarrier ≡ true
  × genealogicalParentP anonymousDonorCarrier ≡ false
anonymousDonorSeparatesPredicateCoordinates = refl , refl

adoptiveParentSeparatesPredicateCoordinates :
  geneticP adoptiveCarrier ≡ false
  × genealogicalParentP adoptiveCarrier ≡ true
adoptiveParentSeparatesPredicateCoordinates = refl , refl

------------------------------------------------------------------------
-- Predicate-restricted fibres are the concrete pullback object.
--
-- A point is simultaneously in the fibre of the Wikidata projection and in the
-- inverse image of a local parent predicate.  This is the set-level shape of a
-- fibre product/pullback:
--
--   Carrier --predicate--> Bool
--      |                  |
--      v                  v
--   slot surface       required true
--
-- with the slot equality and predicate equality retained as witnesses.
------------------------------------------------------------------------

record ParentPredicateFibre
    (slot : WikidataParentSlot)
    (predicate : ParentPredicate) : Set where
  constructor parentPredicateFibre
  field
    predicateCarrier : ParentCarrier
    slotWitness : projectParentSlot predicateCarrier ≡ slot
    predicateWitness : predicate predicateCarrier ≡ true
open ParentPredicateFibre public

adoptiveGenealogicalP8810 : ParentPredicateFibre parentP8810 genealogicalParentP
adoptiveGenealogicalP8810 = parentPredicateFibre adoptiveCarrier refl refl

anonymousDonorGeneticP8810 : ParentPredicateFibre parentP8810 geneticP
anonymousDonorGeneticP8810 = parentPredicateFibre anonymousDonorCarrier refl refl

cultivarProgenitorP1531 : ParentPredicateFibre hybridOfP1531 progenitorP
cultivarProgenitorP1531 = parentPredicateFibre cultivarCarrier refl refl

-- Critically, the cultivar witness does not inhabit the genealogical-parent
-- predicate merely because it inhabits the progenitor predicate.
cultivarProgenitorDoesNotCollapseToGenealogicalParent :
  progenitorP cultivarCarrier ≡ true
  × genealogicalParentP cultivarCarrier ≡ false
cultivarProgenitorDoesNotCollapseToGenealogicalParent = refl , refl

------------------------------------------------------------------------
-- Exact specialization of DASHI.Core.FibreRestrictionCore.
------------------------------------------------------------------------

parentFibreRestrictionCore : Fibre.FibreRestrictionCore
parentFibreRestrictionCore = record
  { Carrier = ParentCarrier
  ; Surface = WikidataParentSlot
  ; Evidence = ParentPredicate
  ; project = projectParentSlot
  ; Fibre = ParentSlotFibre
  ; restrictsFibre = λ predicate slot → ParentPredicateFibre slot predicate
  ; doesNotRecoverCarrier = true
  ; promotesTruth = false
  }

parentEvidenceRestrictsWithoutRecoveringCarrier :
  Fibre.doesNotRecoverCarrier parentFibreRestrictionCore ≡ true
parentEvidenceRestrictsWithoutRecoveringCarrier = refl

parentPredicateDoesNotPromoteGlobalTruth :
  Fibre.promotesTruth parentFibreRestrictionCore ≡ false
parentPredicateDoesNotPromoteGlobalTruth = refl

-- PNF already takes FibreRestrictionCore as a first-class component.  This
-- projection function witnesses that the parent construction uses the same PNF
-- carrier interface rather than defining a parallel notion of fibre.
pnfUsesSameFibreCore :
  ∀ {Vertex Edge Candidate : Set} →
  PNF.PNFEvidenceHyperformalism Vertex Edge Candidate →
  Fibre.FibreRestrictionCore
pnfUsesSameFibreCore system = PNF.fibreCore system

------------------------------------------------------------------------
-- Typed parent hyperfabric: full relation vector in the vertex stalk, local
-- semantic predicates on edge stalks.  Restriction is coordinate projection.
------------------------------------------------------------------------

data ParentAxis : Set where
  progenitorAxis geneticAxis gameteAxis mitochondrialAxis gestationalAxis : ParentAxis
  genealogicalParentAxis intendedParentAxis legalParentAxis socialParentAxis caregiverAxis : ParentAxis

axisValue : ParentAxis → RelationVector → Bool
axisValue progenitorAxis = progenitorRelation
axisValue geneticAxis = geneticContributor
axisValue gameteAxis = gameteContributor
axisValue mitochondrialAxis = mitochondrialContributor
axisValue gestationalAxis = gestationalContributor
axisValue genealogicalParentAxis = genealogicalParent
axisValue intendedParentAxis = intendedParent
axisValue legalParentAxis = legalParent
axisValue socialParentAxis = socialParent
axisValue caregiverAxis = caregiver

axisName : ParentAxis → String
axisName progenitorAxis = "progenitor"
axisName geneticAxis = "genetic contributor"
axisName gameteAxis = "gamete contributor"
axisName mitochondrialAxis = "mitochondrial contributor"
axisName gestationalAxis = "gestational contributor"
axisName genealogicalParentAxis = "genealogical parent"
axisName intendedParentAxis = "intended parent"
axisName legalParentAxis = "legal parent"
axisName socialParentAxis = "social parent"
axisName caregiverAxis = "caregiver"

parentRelationHyperfabric : Fabric.TypedHyperfabric ParentCarrier ParentAxis
parentRelationHyperfabric = record
  { vertexStalk = λ _ → RelationVector
  ; edgeStalk = λ _ → Bool
  ; incidence = λ _ _ → ⊤
  ; restrict = λ {edge = edge} _ relationVectorValue → axisValue edge relationVectorValue
  ; edgeProvenance = λ edge → axisName edge ∷ []
  ; edgeSalience = λ _ → zero
  ; fabricLabel = "progenitor-parent orthogonal relation hyperfabric"
  }

-- Restriction along the genetic and genealogical-parent edges gives different
-- values for the same anonymous-donor stalk value.  Overlap/non-overlap is data,
-- not a type error and not an exclusive ParentRole constructor.
anonymousDonorFabricNonCollapse :
  Fabric.restrict parentRelationHyperfabric tt anonymousIVFDonor ≡ true
  × Fabric.restrict {edge = genealogicalParentAxis} parentRelationHyperfabric tt anonymousIVFDonor ≡ false
anonymousDonorFabricNonCollapse = refl , refl

------------------------------------------------------------------------
-- JMD's flat predicates land in this predicate lattice.
------------------------------------------------------------------------

jmdGeneticPredicate : JMDParentRole → ParentPredicate
jmdGeneticPredicate role carrier = jmdIsGenetic role

jmdLegalPredicate : JMDParentRole → ParentPredicate
jmdLegalPredicate role carrier = jmdIsLegal role

jmdSocialPredicate : JMDParentRole → ParentPredicate
jmdSocialPredicate role carrier = jmdIsSocial role

-- The donor and adoptive constructors are equal at the coarse
-- `recorded-as-parent` surface but separate in the richer predicate fibre.
jmdFlatParentSurfaceRefinesToDistinctFibres :
  jmdRecordedAsParent jmdDonor ≡ jmdRecordedAsParent jmdAdoptive
  × geneticP anonymousDonorCarrier ≡ true
  × geneticP adoptiveCarrier ≡ false
jmdFlatParentSurfaceRefinesToDistinctFibres = refl , (refl , refl)

------------------------------------------------------------------------
-- Structural synthesis: JMD base-change/pullback theorems are the categorical
-- theorem surface; ParentPredicateFibre is the concrete DASHI fibre carrier.
-- Keeping the theorem contract in the record prevents us from silently claiming
-- that the Agda construction is itself the Lean proof object.
------------------------------------------------------------------------

record ParentPullbackSynthesis : Set where
  constructor parentPullbackSynthesis
  field
    fibreRestriction : Fibre.FibreRestrictionCore
    fabric : Fabric.TypedHyperfabric ParentCarrier ParentAxis
    jmdBaseChangeContract : LeanTheoremContract
    jmdMetaPullbackContract : LeanTheoremContract
    representationDoesNotRecoverCarrier : Bool
    predicateDoesNotPromoteTruth : Bool
open ParentPullbackSynthesis public

canonicalParentPullbackSynthesis : ParentPullbackSynthesis
canonicalParentPullbackSynthesis = parentPullbackSynthesis
  parentFibreRestrictionCore
  parentRelationHyperfabric
  jmdRetractsStableUnderBaseChange
  jmdMetaOntologyIsPullback
  true
  true

parentPullbackKeepsProjectionBoundary :
  representationDoesNotRecoverCarrier canonicalParentPullbackSynthesis ≡ true
  × predicateDoesNotPromoteTruth canonicalParentPullbackSynthesis ≡ true
parentPullbackKeepsProjectionBoundary = refl , refl
