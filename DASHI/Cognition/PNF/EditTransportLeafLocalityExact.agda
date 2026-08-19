module DASHI.Cognition.PNF.EditTransportLeafLocalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; map)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Edit transport and provenance-bearing occurrence identity.
--
-- Runtime motivation: a source edit may move an otherwise unchanged semantic
-- occurrence. Correspondence must therefore transport source coordinates; it
-- must not identify leaves by the semantic value whose change we are trying to
-- measure.
--
-- This is an audit projection, not a second semantic authority carrier. The
-- existing NumericOccurrenceFibre remains the token-occurrence authority; this
-- module abstracts the extra support/structural coordinates needed to compare
-- arbitrary parser/object/factor/residual/export/proof leaves across an edit.
------------------------------------------------------------------------

record OccurrenceSignature : Set where
  constructor occurrenceSignature
  field
    leafFamilyKey : Nat
    sourceCoordinate : Nat
    supportCoordinates : List Nat
    structuralPositionKey : Nat
    provenancePathKey : Nat

open OccurrenceSignature public

record AuditLeaf : Set where
  constructor auditLeaf
  field
    occurrence : OccurrenceSignature
    semanticValueKey : Nat

open AuditLeaf public

record EditTransport : Set where
  constructor editTransport
  field
    transportCoordinate : Nat → Nat

open EditTransport public

record TransportedOccurrenceMatch
  (transport : EditTransport)
  (before after : AuditLeaf) : Set where
  constructor transportedOccurrenceMatch
  field
    familyPreserved :
      leafFamilyKey (occurrence before) ≡ leafFamilyKey (occurrence after)
    sourceCoordinateTransported :
      transportCoordinate transport (sourceCoordinate (occurrence before)) ≡
      sourceCoordinate (occurrence after)
    supportCoordinatesTransported :
      map (transportCoordinate transport) (supportCoordinates (occurrence before)) ≡
      supportCoordinates (occurrence after)
    structuralPositionPreserved :
      structuralPositionKey (occurrence before) ≡
      structuralPositionKey (occurrence after)
    provenancePathPreserved :
      provenancePathKey (occurrence before) ≡
      provenancePathKey (occurrence after)

open TransportedOccurrenceMatch public

SemanticValueChanged : AuditLeaf → AuditLeaf → Set
SemanticValueChanged before after =
  semanticValueKey before ≡ semanticValueKey after → ⊥

------------------------------------------------------------------------
-- Unique occurrence correspondence is a prerequisite for a verified locality
-- certificate. Two different leaves may have the same lexical/content anchor;
-- that is not enough to choose between them.
------------------------------------------------------------------------

UniqueMatch :
  {Before After : Set} →
  (Before → After → Set) →
  Before → Set
UniqueMatch {After = After} Match before =
  Σ After λ chosen →
    Match before chosen ×
    ((other : After) → Match before other → other ≡ chosen)

record VerifiedLeafCorrespondence
  {Before After : Set}
  (Eligible : Before → Set)
  (Match : Before → After → Set) : Set where
  constructor verifiedLeafCorrespondence
  field
    uniqueCorrespondence :
      (before : Before) → Eligible before → UniqueMatch Match before

open VerifiedLeafCorrespondence public

ambiguityRefutesVerifiedCorrespondence :
  {Before After : Set}
  {Eligible : Before → Set}
  {Match : Before → After → Set} →
  VerifiedLeafCorrespondence Eligible Match →
  (before : Before) →
  Eligible before →
  (left right : After) →
  Match before left →
  Match before right →
  (left ≡ right → ⊥) →
  ⊥
ambiguityRefutesVerifiedCorrespondence certificate before eligible left right leftMatch rightMatch distinct =
  distinct (trans leftIsChosen (sym rightIsChosen))
  where
    witness : UniqueMatch Match before
    witness = uniqueCorrespondence certificate before eligible

    chosen : After
    chosen = proj₁ witness

    uniqueness : (other : After) → Match before other → other ≡ chosen
    uniqueness = proj₂ (proj₂ witness)

    leftIsChosen : left ≡ chosen
    leftIsChosen = uniqueness left leftMatch

    rightIsChosen : right ≡ chosen
    rightIsChosen = uniqueness right rightMatch

------------------------------------------------------------------------
-- Reverse-dependency closure locality.
------------------------------------------------------------------------

record EditedDependencyClosure
  (SourceAtom Leaf : Set) : Set₁ where
  constructor editedDependencyClosure
  field
    edited : SourceAtom → Set
    reaches : SourceAtom → Leaf → Set

open EditedDependencyClosure public

InEditedClosure :
  {SourceAtom Leaf : Set} →
  EditedDependencyClosure SourceAtom Leaf →
  Leaf → Set
InEditedClosure {SourceAtom = SourceAtom} closure leaf =
  Σ SourceAtom λ source → edited closure source × reaches closure source leaf

ClosureSound :
  {SourceAtom Leaf : Set} →
  EditedDependencyClosure SourceAtom Leaf →
  (Leaf → Set) → Set
ClosureSound {Leaf = Leaf} closure Changed =
  (leaf : Leaf) → Changed leaf → InEditedClosure closure leaf

ClosureExact :
  {SourceAtom Leaf : Set} →
  EditedDependencyClosure SourceAtom Leaf →
  (Leaf → Set) → Set
ClosureExact {Leaf = Leaf} closure Changed =
  (leaf : Leaf) → InEditedClosure closure leaf → Changed leaf

record ExactClosureLocality
  {SourceAtom Leaf : Set}
  (closure : EditedDependencyClosure SourceAtom Leaf)
  (Changed : Leaf → Set) : Set where
  constructor exactClosureLocality
  field
    sound : ClosureSound closure Changed
    precise : ClosureExact closure Changed

open ExactClosureLocality public

exactClosureImpliesSound :
  {SourceAtom Leaf : Set}
  {closure : EditedDependencyClosure SourceAtom Leaf}
  {Changed : Leaf → Set} →
  ExactClosureLocality closure Changed →
  ClosureSound closure Changed
exactClosureImpliesSound = sound

localityViolationRefutesSoundness :
  {SourceAtom Leaf : Set}
  {closure : EditedDependencyClosure SourceAtom Leaf}
  {Changed : Leaf → Set} →
  ClosureSound closure Changed →
  (leaf : Leaf) →
  Changed leaf →
  (InEditedClosure closure leaf → ⊥) →
  ⊥
localityViolationRefutesSoundness soundness leaf changed outside =
  outside (soundness leaf changed)

------------------------------------------------------------------------
-- Full audit certificate.
------------------------------------------------------------------------

record VerifiedEditLocality
  {Before After SourceAtom : Set}
  (Eligible : Before → Set)
  (Match : Before → After → Set)
  (closure : EditedDependencyClosure SourceAtom After)
  (Changed : After → Set) : Set where
  constructor verifiedEditLocality
  field
    correspondence : VerifiedLeafCorrespondence Eligible Match
    changedInsideDependencyClosure : ClosureSound closure Changed

open VerifiedEditLocality public

verifiedEditLocalityRefutesAmbiguousMatch :
  {Before After SourceAtom : Set}
  {Eligible : Before → Set}
  {Match : Before → After → Set}
  {closure : EditedDependencyClosure SourceAtom After}
  {Changed : After → Set} →
  VerifiedEditLocality Eligible Match closure Changed →
  (before : Before) →
  Eligible before →
  (left right : After) →
  Match before left →
  Match before right →
  (left ≡ right → ⊥) →
  ⊥
verifiedEditLocalityRefutesAmbiguousMatch certificate =
  ambiguityRefutesVerifiedCorrespondence (correspondence certificate)

verifiedEditLocalityRefutesOutsideChange :
  {Before After SourceAtom : Set}
  {Eligible : Before → Set}
  {Match : Before → After → Set}
  {closure : EditedDependencyClosure SourceAtom After}
  {Changed : After → Set} →
  VerifiedEditLocality Eligible Match closure Changed →
  (leaf : After) →
  Changed leaf →
  (InEditedClosure closure leaf → ⊥) →
  ⊥
verifiedEditLocalityRefutesOutsideChange certificate =
  localityViolationRefutesSoundness (changedInsideDependencyClosure certificate)
