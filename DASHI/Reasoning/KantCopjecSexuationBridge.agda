module DASHI.Reasoning.KantCopjecSexuationBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ExceptionalAndNonAllClosure as Closure
import DASHI.Reasoning.KantAntinomyCore as Kant

------------------------------------------------------------------------
-- Scholarly bridge: Kantian antinomy structures to the Lacanian
-- all-with-exception / non-all distinction associated with Joan Copjec and
-- developed by Žižek.  The bridge is structural and non-diagnostic.
------------------------------------------------------------------------

data SexuationPosition : Set where
  allWithExceptionPosition nonAllPosition : SexuationPosition

record KantCopjecHomology : Set where
  field
    dynamicalSource : Kant.AntinomyKind
    mathematicalSource : Kant.AntinomyKind
    dynamicalTarget : SexuationPosition
    mathematicalTarget : SexuationPosition
    dynamicalMapsToAllWithException : Bool
    mathematicalMapsToNonAll : Bool
    mappingIsIdentityTheorem : Bool
    sourceAttribution : String
    bridgeReceipt : String

canonicalKantCopjecHomology : KantCopjecHomology
canonicalKantCopjecHomology = record
  { dynamicalSource = Kant.dynamicalAntinomy
  ; mathematicalSource = Kant.mathematicalAntinomy
  ; dynamicalTarget = allWithExceptionPosition
  ; mathematicalTarget = nonAllPosition
  ; dynamicalMapsToAllWithException = true
  ; mathematicalMapsToNonAll = true
  ; mappingIsIdentityTheorem = false
  ; sourceAttribution =
      "Joan Copjec, Read My Desire: Lacan Against the Historicists"
  ; bridgeReceipt =
      "A governed structural homology: scope-separated dynamical resolution is read beside exception logic; non-totalisable mathematical series beside non-all."
  }

record NonAllPriorityReceipt : Set where
  field
    nonAllGroundLogicallyPrior : Bool
    exceptionalClosureIsCompactificationCandidate : Bool
    nonAllTemporallyProducedByException : Bool
    stageSequenceProvesLogicalPriority : Bool
    priorityReceipt : String

canonicalNonAllPriorityReceipt : NonAllPriorityReceipt
canonicalNonAllPriorityReceipt = record
  { nonAllGroundLogicallyPrior = true
  ; exceptionalClosureIsCompactificationCandidate = true
  ; nonAllTemporallyProducedByException = false
  ; stageSequenceProvesLogicalPriority = false
  ; priorityReceipt =
      "Logical priority is represented as figure/ground, not as a numeral-driven temporal ascent."
  }

record KantCopjecAuthorityBoundary : Set where
  field
    closureStructuresReused : Bool
    sexuationEncodedAsInconsistentClassicalConjunction : Bool
    empiricalPersonsClassified : Bool
    mathematicalAntinomyEqualsCantorTheorem : Bool
    dynamicalAntinomyRequiresLiteralOutsidePerson : Bool
    scholarlyBridgePromotesClinicalAuthority : Bool
    boundaryNote : String

canonicalKantCopjecAuthorityBoundary : KantCopjecAuthorityBoundary
canonicalKantCopjecAuthorityBoundary = record
  { closureStructuresReused = true
  ; sexuationEncodedAsInconsistentClassicalConjunction = false
  ; empiricalPersonsClassified = false
  ; mathematicalAntinomyEqualsCantorTheorem = false
  ; dynamicalAntinomyRequiresLiteralOutsidePerson = false
  ; scholarlyBridgePromotesClinicalAuthority = false
  ; boundaryNote =
      "The Copjec homology connects formal structures without identifying persons, Kantian resolutions, Cantor diagonalisation or stage numbers."
  }
