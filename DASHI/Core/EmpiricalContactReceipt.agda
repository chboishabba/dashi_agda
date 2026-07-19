module DASHI.Core.EmpiricalContactReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.FibreRestrictionCore as Restriction
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.ReplayArtifactCore as Replay

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

not : Bool → Bool
not true = false
not false = true

record SourceBinding : Set where
  constructor sourceBinding
  field
    sourceLabel   : String
    sourceKind    : String
    sourceLocator : String

ReplayArtifact : Set
ReplayArtifact = Replay.ReplayArtifactCore

replayArtifact : String → String → String → ReplayArtifact
replayArtifact = Replay.canonicalReplayArtifact

record EmpiricalContactReceipt : Set₁ where
  constructor empiricalContactReceipt
  field
    contactGeometry           : Geometry.ObservableContactGeometry
    contactHamiltonian        : Hamiltonian.ContactHamiltonian
    source                    : SourceBinding
    replay                    : ReplayArtifact
    sourceBound               : Bool
    projectionLawTyped        : Bool
    observableRecorded        : Bool
    replayable                : Bool
    comparisonLawTyped        : Bool
    fibreRestrictionTyped     : Bool
    diagnosticOnly            : Bool
    externalAuthorityRequired : Bool
    authorityGateClosed       : Bool
    promotesTruth             : Bool

  observableContactClosed : Bool
  observableContactClosed =
    sourceBound ∧ projectionLawTyped ∧ observableRecorded ∧ replayable
    ∧ comparisonLawTyped ∧ fibreRestrictionTyped

  nonPromotionBoundaryClosed : Bool
  nonPromotionBoundaryClosed =
    diagnosticOnly ∧ externalAuthorityRequired
    ∧ not authorityGateClosed ∧ not promotesTruth

  closureStatement : String
  closureStatement =
    "Observable contact is typed as a projection from hidden carrier structure "
    ++ "to an observable surface with replay, comparison law, fibre restriction, "
    ++ "and residual-energy tracking. Contact is recorded without recovering the "
    ++ "whole fibre, and promotion remains blocked until an external authority chain closes."

open EmpiricalContactReceipt public

contactGateCore : EmpiricalContactReceipt → Gate.ContactGateCore
contactGateCore receipt =
  Gate.contactGateCore
    (diagnosticOnly receipt)
    (externalAuthorityRequired receipt)
    (authorityGateClosed receipt)
    false
    (promotesTruth receipt)

replayArtifactCore : EmpiricalContactReceipt → Replay.ReplayArtifactCore
replayArtifactCore = replay

canonicalNonPromotingEmpiricalContactReceipt :
  Geometry.ObservableContactGeometry →
  Hamiltonian.ContactHamiltonian →
  SourceBinding → ReplayArtifact → EmpiricalContactReceipt
canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay =
  empiricalContactReceipt geometry hamiltonian source replay
    true true true true true true true true false false

canonicalFibreRestrictionIsNonRecovering :
  (geometry : Geometry.ObservableContactGeometry) →
  Restriction.doesNotRecoverCarrier (Geometry.fibreRestrictionCore geometry) ≡ true →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  fibreRestrictionTyped
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay) ≡ true
canonicalFibreRestrictionIsNonRecovering geometry nonRecovering hamiltonian source replay = refl

canonicalObservableContactClosed :
  (geometry : Geometry.ObservableContactGeometry) →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  observableContactClosed
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay) ≡ true
canonicalObservableContactClosed geometry hamiltonian source replay = refl

canonicalNonPromotionBoundaryClosed :
  (geometry : Geometry.ObservableContactGeometry) →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  nonPromotionBoundaryClosed
    (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay) ≡ true
canonicalNonPromotionBoundaryClosed geometry hamiltonian source replay = refl

canonicalContactGateIsFailClosed :
  (geometry : Geometry.ObservableContactGeometry) →
  (hamiltonian : Hamiltonian.ContactHamiltonian) →
  (source : SourceBinding) →
  (replay : ReplayArtifact) →
  Gate.promotesTruth
    (contactGateCore
      (canonicalNonPromotingEmpiricalContactReceipt geometry hamiltonian source replay)) ≡ false
canonicalContactGateIsFailClosed geometry hamiltonian source replay = refl
