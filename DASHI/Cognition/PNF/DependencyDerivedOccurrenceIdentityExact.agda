module DASHI.Cognition.PNF.DependencyDerivedOccurrenceIdentityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

------------------------------------------------------------------------
-- Source-free occurrence identity.
--
-- Exports/proofs need not own lexical/source coordinates.  Once their premise
-- occurrences have unique transported identities, a source-free occurrence is
-- identified by its producer family/slot plus the ordered premise identities.
-- The semantic value produced at that occurrence is deliberately separate.
------------------------------------------------------------------------

record DependencyDerivedOccurrence : Set where
  constructor dependencyDerivedOccurrence
  field
    derivedFamilyKey : Nat
    producerStructuralKey : Nat
    dependencyOccurrenceKeys : List Nat

open DependencyDerivedOccurrence public

record DependencyDerivedLeaf : Set where
  constructor dependencyDerivedLeaf
  field
    derivedOccurrence : DependencyDerivedOccurrence
    derivedSemanticValueKey : Nat

open DependencyDerivedLeaf public

record DependencyDerivedOccurrenceMatch
  (before after : DependencyDerivedLeaf) : Set where
  constructor dependencyDerivedOccurrenceMatch
  field
    familyPreserved :
      derivedFamilyKey (derivedOccurrence before) ≡
      derivedFamilyKey (derivedOccurrence after)
    producerStructurePreserved :
      producerStructuralKey (derivedOccurrence before) ≡
      producerStructuralKey (derivedOccurrence after)
    dependenciesPreserved :
      dependencyOccurrenceKeys (derivedOccurrence before) ≡
      dependencyOccurrenceKeys (derivedOccurrence after)

open DependencyDerivedOccurrenceMatch public

DerivedSemanticValueChanged :
  DependencyDerivedLeaf → DependencyDerivedLeaf → Set
DerivedSemanticValueChanged before after =
  derivedSemanticValueKey before ≡ derivedSemanticValueKey after → ⊥

dependencyDerivedIdentityUsesNoSemanticValue :
  (before after : DependencyDerivedLeaf) →
  derivedOccurrence before ≡ derivedOccurrence after →
  DependencyDerivedOccurrenceMatch before after
dependencyDerivedIdentityUsesNoSemanticValue before after refl =
  dependencyDerivedOccurrenceMatch refl refl refl

------------------------------------------------------------------------
-- Composition across a revision lineage is premise-wise: if an intermediate
-- source-free occurrence preserves family, producer structure and dependency
-- occurrence keys on both legs, the endpoints preserve them too.
------------------------------------------------------------------------

dependencyDerivedMatchTransitive :
  {first middle last : DependencyDerivedLeaf} →
  DependencyDerivedOccurrenceMatch first middle →
  DependencyDerivedOccurrenceMatch middle last →
  DependencyDerivedOccurrenceMatch first last
dependencyDerivedMatchTransitive
  (dependencyDerivedOccurrenceMatch refl refl refl)
  (dependencyDerivedOccurrenceMatch refl refl refl) =
  dependencyDerivedOccurrenceMatch refl refl refl
