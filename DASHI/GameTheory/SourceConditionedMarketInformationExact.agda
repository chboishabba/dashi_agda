module DASHI.GameTheory.SourceConditionedMarketInformationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian
import DASHI.Core.SourceConditionedObservationExact as Source

------------------------------------------------------------------------
-- SOURCE-CONDITIONED INFORMATION SETS FOR FINITE BAYESIAN GAMES
--
-- The existing Bayesian game already distinguishes world state from player
-- signal.  This module adds an orthogonal evidence/provenance fibre.  Two worlds
-- can expose the same public signal to a player while carrying different source
-- states.  Therefore a coarse public signal must not be promoted to equality of
-- information provenance.
------------------------------------------------------------------------

record SourceConditionedInformation
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G) : Set₁ where
  constructor source-conditioned-information
  field
    EvidenceState : Set
    evidenceAt : Bayesian.World B → EvidenceState
    evidenceReference : EvidenceState → String
    sourceAt : EvidenceState → Source.SourceArtifact
    informationReference : String

open SourceConditionedInformation public

record SameSignalEvidenceCollision
    {G : Game.StrategicGame}
    {B : Bayesian.FiniteBayesianGame G}
    (I : SourceConditionedInformation B) : Set₁ where
  constructor same-signal-evidence-collision
  field
    leftWorld rightWorld : Bayesian.World B
    player : Game.Player G
    samePublicSignal :
      Bayesian.signalAt B leftWorld player
      ≡ Bayesian.signalAt B rightWorld player
    evidenceDifferent :
      evidenceAt I leftWorld ≡ evidenceAt I rightWorld → ⊥
    collisionReference : String

open SameSignalEvidenceCollision public

sameSignalCannotEraseEvidenceDifference :
  ∀ {G B} {I : SourceConditionedInformation {G} B} →
  SameSignalEvidenceCollision I →
  evidenceAt I (leftWorld _) ≡ evidenceAt I (rightWorld _) →
  ⊥
sameSignalCannotEraseEvidenceDifference collision = evidenceDifferent collision

------------------------------------------------------------------------
-- A source-conditioned signal interpretation may be attached to the existing
-- Bayesian game without altering its equilibrium theorem.  Extra evidence may
-- refine an application model, but it does not retroactively change the game's
-- declared prior, strategy language or payoff surface.
------------------------------------------------------------------------

record ProvenanceAwareSignalInterpretation
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G)
    (I : SourceConditionedInformation B) : Set₁ where
  constructor provenance-aware-signal-interpretation
  field
    publicSignalReference : String
    provenanceReference : String
    unresolvedEvidenceReference : String
    interpretationCreatesPosterior : Bool
    interpretationCreatesPosteriorIsFalse : interpretationCreatesPosterior ≡ false

open ProvenanceAwareSignalInterpretation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameSignalMeansSameInformationPermission : Set where
data SourceDifferenceMeansDifferentStrategyPermission : Set where
data EvidenceStateMeansHiddenTypeKnownPermission : Set where
data InformationAsymmetryMeansIllegalTradingPermission : Set where
data BayesianCompatibilityMeansActualMotivePermission : Set where

sameSignalDoesNotMeanSameInformation : SameSignalMeansSameInformationPermission → ⊥
sameSignalDoesNotMeanSameInformation ()

sourceDifferenceDoesNotForceDifferentStrategy : SourceDifferenceMeansDifferentStrategyPermission → ⊥
sourceDifferenceDoesNotForceDifferentStrategy ()

evidenceStateDoesNotRevealHiddenType : EvidenceStateMeansHiddenTypeKnownPermission → ⊥
evidenceStateDoesNotRevealHiddenType ()

informationAsymmetryDoesNotProveIllegalTrading : InformationAsymmetryMeansIllegalTradingPermission → ⊥
informationAsymmetryDoesNotProveIllegalTrading ()

bayesianCompatibilityDoesNotRevealActualMotive : BayesianCompatibilityMeansActualMotivePermission → ⊥
bayesianCompatibilityDoesNotRevealActualMotive ()

record SourceConditionedMarketInformationBoundary : Set where
  constructor source-conditioned-market-information-boundary
  field
    worldSignalAndSourceStateAreSeparate : Bool
    samePublicSignalMayHideDifferentEvidence : Bool
    sourceDifferenceDoesNotForceStrategyDifference : Bool
    evidenceDoesNotRevealHiddenTypeAutomatically : Bool
    informationAsymmetryDoesNotProveIllegality : Bool
    equilibriumCompatibilityDoesNotRevealMotive : Bool

canonicalSourceConditionedMarketInformationBoundary :
  SourceConditionedMarketInformationBoundary
canonicalSourceConditionedMarketInformationBoundary =
  source-conditioned-market-information-boundary true true true true true true
