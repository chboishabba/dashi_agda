module DASHI.Semantics.SIOSemanticSurfaceBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Provenance
import DASHI.Core.ObserverRefinementCore as Observer

------------------------------------------------------------------------
-- Semanticscience Integrated Ontology (SIO) bridge.
--
-- Reference:
-- Michel Dumontier, Christopher JO Baker, Joachim Baran, Alison Callahan,
-- Leonid Chepelev, José Cruz-Toledo, Nicholas R Del Rio, Geraint Duck,
-- Laura I Furlong, Nichealla Keath, Dana Klassen, Jamie P McCusker,
-- Núria Queralt-Rosinach, Matthias Samwald, Natalia Villanueva-Rosales,
-- Mark D Wilkinson, Robert Hoehndorf.
-- "The Semanticscience Integrated Ontology (SIO) for biomedical research
-- and knowledge discovery", Journal of Biomedical Semantics 5, 14 (2014).
-- DOI: 10.1186/2041-1480-5-14
--
-- SIO supplies an interoperable RDF/OWL vocabulary for entities, processes,
-- attributes, information entities, values, units, evidence and roles.
-- DASHI supplies the stronger proof boundary underneath those public semantic
-- surfaces: projection does not imply identity, evidence does not imply world
-- truth, and role assertions do not by themselves imply present authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SIO-style information/measurement surface over an existing DASHI fibre.
------------------------------------------------------------------------

record SIOObservationSurface
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor sioObservationSurface
  field
    InformationEntity : Set
    Attribute : Set
    Value : Set
    Unit : Set

    encodeSurface : Fibre.Surface core → InformationEntity
    denotesAttribute : InformationEntity → Attribute → Set
    hasValue : InformationEntity → Value → Set
    hasUnit : InformationEntity → Unit → Set

open SIOObservationSurface public

------------------------------------------------------------------------
-- SIO-style evidence relations remain graph assertions.  They can be useful
-- observations while still lacking authority to promote themselves to world
-- truth.  This is deliberately parallel to ProvenanceBearingQuotient's rule
-- that a receipt is provenance, not semantic authority.
------------------------------------------------------------------------

record SIOEvidenceSurface
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor sioEvidenceSurface
  field
    EvidenceNode : Set
    Proposition : Set

    encodeEvidence : Fibre.Evidence core → EvidenceNode
    supports : EvidenceNode → Proposition → Set
    disputes : EvidenceNode → Proposition → Set
    refutes : EvidenceNode → Proposition → Set

open SIOEvidenceSurface public

data SIOGraphAssertionAuthority : Set where
  graphAssertionOnly : SIOGraphAssertionAuthority

data WorldTruthPermission : SIOGraphAssertionAuthority → Set where

sioGraphAssertionCannotPromoteWorldTruth :
  WorldTruthPermission graphAssertionOnly → ⊥
sioGraphAssertionCannotPromoteWorldTruth ()

------------------------------------------------------------------------
-- SIO-style role/process modelling with an explicit DASHI authority boundary.
-- Bearing a role and having that role realized in some process can be stated
-- independently of whether the role currently authorizes an action.
------------------------------------------------------------------------

record SIORoleSurface : Set₁ where
  constructor sioRoleSurface
  field
    Entity : Set
    Process : Set
    Role : Set

    bearsRole : Entity → Role → Set
    realizes : Process → Role → Set
    currentlyAuthorized : Entity → Role → Set

open SIORoleSurface public

data SIORoleAssertionAuthority : Set where
  roleAssertionOnly : SIORoleAssertionAuthority

data CurrentAuthorityPermission : SIORoleAssertionAuthority → Set where

sioRoleAssertionCannotCreateCurrentAuthority :
  CurrentAuthorityPermission roleAssertionOnly → ⊥
sioRoleAssertionCannotCreateCurrentAuthority ()

------------------------------------------------------------------------
-- Reopenable SIO surface.
--
-- The public information entity may be a compact ontology-facing rendering
-- of the DASHI surface.  Exact reopening still comes from the separately
-- retained provenance receipt; encoding the projection as RDF/OWL does not
-- erase the hidden carrier.
------------------------------------------------------------------------

record ReopenableSIOSurface
    (core : Fibre.FibreRestrictionCore) : Set₁ where
  constructor reopenableSIOSurface
  field
    observation : SIOObservationSurface core
    quotient : Provenance.ProvenanceBearingQuotient core

open ReopenableSIOSurface public

reopenProjectedExactly :
  ∀ {core : Fibre.FibreRestrictionCore} →
  (bridge : ReopenableSIOSurface core) →
  (x : Fibre.Carrier core) →
  Provenance.reopen (quotient bridge)
    (Fibre.project core x)
    (Provenance.receipt (quotient bridge) x)
    ≡ x
reopenProjectedExactly bridge x =
  Provenance.reopenExact (quotient bridge) x

------------------------------------------------------------------------
-- Attribute observers.
--
-- Multiple SIO attributes are not assumed to lie on one total information
-- ladder.  They are ordinary DASHI observers, so cross-collision witnesses
-- prove incomparability and pairing gives a strict joint refinement.
------------------------------------------------------------------------

SIOAttributeObserver : Set → Set → Set
SIOAttributeObserver X V = X → V

SIOInformationBelow :
  ∀ {X A B : Set} →
  SIOAttributeObserver X A →
  SIOAttributeObserver X B → Set
SIOInformationBelow = Observer.InformationBelow

sioCrossCollisionImpliesIncomparable :
  ∀ {X A B : Set}
    {OA : SIOAttributeObserver X A}
    {OB : SIOAttributeObserver X B} →
  Observer.CrossCollision OA OB →
  Observer.IncomparableObservers OA OB
sioCrossCollisionImpliesIncomparable =
  Observer.crossCollisionImpliesIncomparable

sioPairedObserverStrictlyRefinesBoth :
  ∀ {X A B : Set}
    {OA : SIOAttributeObserver X A}
    {OB : SIOAttributeObserver X B} →
  (witness : Observer.CrossCollision OA OB) →
  Observer.StrictlyRefines (Observer.pairObserver OA OB) OA
  ×
  Observer.StrictlyRefines (Observer.pairObserver OA OB) OB
sioPairedObserverStrictlyRefinesBoth witness =
  Observer.pairStrictlyRefinesLeft witness ,
  Observer.pairStrictlyRefinesRight witness

sioPairedObserverIsLeastJointRefinement :
  ∀ {X A B C : Set}
    {O : SIOAttributeObserver X C}
    {OA : SIOAttributeObserver X A}
    {OB : SIOAttributeObserver X B} →
  Observer.Refines O OA →
  Observer.Refines O OB →
  Observer.Refines O (Observer.pairObserver OA OB)
sioPairedObserverIsLeastJointRefinement =
  Observer.jointRefinesPair

sioPairedObserverIsJoin :
  ∀ {X A B C : Set}
    {O : SIOAttributeObserver X C}
    {OA : SIOAttributeObserver X A}
    {OB : SIOAttributeObserver X B} →
  SIOInformationBelow OA O →
  SIOInformationBelow OB O →
  SIOInformationBelow (Observer.pairObserver OA OB) O
sioPairedObserverIsJoin =
  Observer.pairIsLeastUpperBound

------------------------------------------------------------------------
-- Boundary summary suitable for downstream documentation/tests.
------------------------------------------------------------------------

record SIOSemanticBoundary : Set₁ where
  constructor sioSemanticBoundary
  field
    graphEvidencePromotesWorldTruth : WorldTruthPermission graphAssertionOnly → ⊥
    roleAssertionCreatesCurrentAuthority :
      CurrentAuthorityPermission roleAssertionOnly → ⊥

canonicalSIOSemanticBoundary : SIOSemanticBoundary
canonicalSIOSemanticBoundary =
  sioSemanticBoundary
    sioGraphAssertionCannotPromoteWorldTruth
    sioRoleAssertionCannotCreateCurrentAuthority
