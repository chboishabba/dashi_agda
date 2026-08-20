module DASHI.Physics.Closure.HEPDataW3GovernedContactAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)

import DASHI.Core.ContactGateCore as Gate
import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.GovernedContactCore as Governed
import DASHI.Core.ObservableContactGeometry as Geometry
import DASHI.Core.ReplayArtifactCore as Replay
import DASHI.Physics.Closure.HEPDataW3ComparisonLawReceipt as W3

------------------------------------------------------------------------
-- Second-domain instance of the governed comparison/contact grammar.
--
-- This adapter does not alter the existing bounded W3 receipt.  It exposes the
-- already-recorded covariance comparison as a projected contact surface and
-- keeps the external-authority/bridge gate fail-closed.
------------------------------------------------------------------------

record Witness : Set where
  constructor witness

w3Projection : W3.W3ComparisonLawAcceptanceCriterion → Float
w3Projection criterion =
  W3.W3ComparisonLawAcceptanceCriterion.chi2PerDof criterion

w3ObservedThreshold : W3.W3ComparisonLawAcceptanceCriterion → Float
w3ObservedThreshold criterion =
  W3.W3ComparisonLawAcceptanceCriterion.acceptanceThreshold criterion

w3Fibre : Float → Set
w3Fibre value = W3.W3ComparisonLawAcceptanceCriterion

w3Residual : Float → Float → Set
w3Residual predicted threshold = Witness

w3ComparisonLaw : Float → Float → Set
w3ComparisonLaw predicted threshold = Witness

w3Geometry : Geometry.ObservableContactGeometry
w3Geometry =
  Geometry.observableContactGeometry
    W3.W3ComparisonLawAcceptanceCriterion
    Float
    W3.W3ComparisonLawAcceptanceCriterion
    W3.W3ComparisonLawAcceptanceCriterion
    w3Projection
    w3Fibre
    w3ObservedThreshold
    w3Residual
    w3ComparisonLaw
    (λ evidence observable → Witness)
    true
    false
    (λ left right → Witness)
    Witness

w3Hamiltonian : Hamiltonian.ContactHamiltonian
w3Hamiltonian =
  Hamiltonian.contactHamiltonian
    Witness
    Float
    (λ residual →
      W3.W3ComparisonLawAcceptanceCriterion.chi2PerDof
        W3.canonicalW3ComparisonLawAcceptanceCriterion)
    (λ energy → Witness)
    (λ energy → Witness)
    true

w3Replay : Replay.ReplayArtifactCore
w3Replay =
  Replay.canonicalReplayArtifact
    "HEPData W3 bounded t43/t44 covariance comparison"
    "DASHI/Physics/Closure/HEPDataW3ComparisonLawReceipt.agda"
    "scripts/run_agda29_parallel_check.sh DASHI/Physics/Closure/HEPDataW3GovernedContactAdapter.agda"

w3Gate : Gate.ContactGateCore
w3Gate = Gate.canonicalFailClosedContactGate

w3GovernedContact : Governed.GovernedContactCore
w3GovernedContact =
  Governed.governedContactCore
    w3Geometry
    w3Hamiltonian
    w3Replay
    w3Gate
    (λ residual → witness)
    refl
    refl
    refl

w3ContactDoesNotPromoteTruth :
  Gate.promotesTruth (Governed.gate w3GovernedContact) ≡ false
w3ContactDoesNotPromoteTruth = refl

w3ComparisonScore : Float
w3ComparisonScore =
  W3.W3ComparisonLawAcceptanceCriterion.chi2PerDof
    W3.canonicalW3ComparisonLawAcceptanceCriterion
