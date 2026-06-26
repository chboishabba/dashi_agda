module DASHI.Core.EmpiricalContactReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)

import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.FibreRestrictionCore as Restriction

------------------------------------------------------------------------
-- Bool conjunction
------------------------------------------------------------------------

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

not : Bool → Bool
not true = false
not false = true

------------------------------------------------------------------------
-- Generic receipt metadata
------------------------------------------------------------------------

record SourceBinding : Set where
  constructor sourceBinding
  field
    sourceLabel   : String
    sourceKind    : String
    sourceLocator : String

record ReplayArtifact : Set where
  constructor replayArtifact
  field
    artifactLabel      : String
    artifactLocator    : String
    validationCommand  : String

record EmpiricalContactReceipt : Set₁ where
  constructor empiricalContactReceipt
  field
    contactGeometry          : Geometry.ObservableContactGeometry
    contactHamiltonian       : Hamiltonian.ContactHamiltonian
    source                   : SourceBinding
    replay                   : ReplayArtifact
    sourceBound              : Bool
    projectionLawTyped       : Bool
    observableRecorded       : Bool
    replayable               : Bool
    comparisonLawTyped       : Bool
    fibreRestrictionTyped    : Bool
    diagnosticOnly           : Bool
    externalAuthorityRequired : Bool
    authorityGateClosed      : Bool
    promotesTruth            : Bool

  observableContactClosed : Bool
  observableContactClosed =
    sourceBound
    ∧ projectionLawTyped
    ∧ observableRecorded
    ∧ replayable
    ∧ comparisonLawTyped
    ∧ fibreRestrictionTyped

  nonPromotionBoundaryClosed : Bool
  nonPromotionBoundaryClosed =
    diagnosticOnly
    ∧ externalAuthorityRequired
    ∧ not authorityGateClosed
    ∧ not promotesTruth

  closureStatement : String
  closureStatement =
    "Observable contact is typed as a projection from hidden carrier structure "
    ++ "to an observable surface with replay, comparison law, fibre restriction, "
    ++ "and residual-energy tracking. Contact is recorded without recovering the "
    ++ "whole fibre, and "
    ++ "promotion remains blocked until an external authority chain closes."

open EmpiricalContactReceipt public

canonicalNonPromotingEmpiricalContactReceipt :
  Geometry.ObservableContactGeometry →
  Hamiltonian.ContactHamiltonian →
  SourceBinding →
  ReplayArtifact →
  EmpiricalContactReceipt
canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay =
  empiricalContactReceipt
    geometry
    hamiltonian
    source
    replay
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false

canonicalFibreRestrictionIsNonRecovering :
  (geometry : Geometry.ObservableContactGeometry) →
  Restriction.doesNotRecoverCarrier
    (Geometry.fibreRestrictionCore geometry)
    ≡ true
  → (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  fibreRestrictionTyped
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay)
    ≡ true
canonicalFibreRestrictionIsNonRecovering geometry nonRecovering hamiltonian source replay =
  refl

canonicalObservableContactClosed :
  (geometry : Geometry.ObservableContactGeometry) →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  observableContactClosed
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay)
    ≡ true
canonicalObservableContactClosed geometry hamiltonian source replay = refl

canonicalNonPromotionBoundaryClosed :
  (geometry : Geometry.ObservableContactGeometry) →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  nonPromotionBoundaryClosed
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay)
    ≡ true
canonicalNonPromotionBoundaryClosed geometry hamiltonian source replay = refl
