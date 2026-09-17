module DASHI.Education.DigitalESDEvidenceBraidTensionRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Tension

convergencePinned : Tension.BraidRelation
convergencePinned = Tension.convergence

complementarityPinned : Tension.BraidRelation
complementarityPinned = Tension.complementarity

productiveTensionPinned : Tension.BraidRelation
productiveTensionPinned = Tension.productiveTension

unresolvedConflictPinned : Tension.BraidRelation
unresolvedConflictPinned = Tension.unresolvedConflict

scopeDifferencePinned : Tension.BraidRelation
scopeDifferencePinned = Tension.scopeDifference

authorityDifferencePinned : Tension.BraidRelation
authorityDifferencePinned = Tension.authorityDifference

provenanceDifferencePinned : Tension.BraidRelation
provenanceDifferencePinned = Tension.provenanceDifference

prohibitedCollapsePinned : Tension.BraidRelation
prohibitedCollapsePinned = Tension.prohibitedCollapse

sharedObservationNoProvenanceFusion :
  Tension.SharedObservationCreatesSameProvenance → ⊥
sharedObservationNoProvenanceFusion = Tension.sharedObservationDoesNotCreateSameProvenance

pluralNoForcedConsensus : Tension.PluralObservationsCreateForcedConsensus → ⊥
pluralNoForcedConsensus = Tension.pluralObservationsDoNotCreateForcedConsensus
