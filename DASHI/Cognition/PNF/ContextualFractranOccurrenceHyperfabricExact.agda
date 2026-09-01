module DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.NumericOccurrenceFibre as Occurrence
import DASHI.Cognition.PNF.NumericHyperfabric as Document
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Contextual token valuation.
--
-- A lexical surface/POS pair is not assigned one global FRACTRAN value.
-- The value belongs to an occurrence in one admissible document-world context.
-- spaCy supplies structural evidence; document/world restriction supplies the
-- contextual signed SSP valuation.
------------------------------------------------------------------------

data SemanticRole : Set where
  agentRole patientRole sourceRole targetRole giverRole recipientRole : SemanticRole
  premiseRole conclusionRole evidenceRole authorityRole : SemanticRole

record OrientedRolePair : Set where
  constructor orientedRolePair
  field
    sourceRole : SemanticRole
    targetRole : SemanticRole

open OrientedRolePair public

reverseRolePair : OrientedRolePair → OrientedRolePair
reverseRolePair (orientedRolePair source target) = orientedRolePair target source

reverseRolePairInvolutive :
  (roles : OrientedRolePair) →
  reverseRolePair (reverseRolePair roles) ≡ roles
reverseRolePairInvolutive (orientedRolePair source target) = refl

record QueryFrame : Set where
  constructor queryFrame
  field
    roles : OrientedRolePair
    anchorToken : Spacy.TokenId
    asksForSource : Bool

open QueryFrame public

invertQueryFrame : QueryFrame → QueryFrame
invertQueryFrame (queryFrame roles anchor asksSource) =
  queryFrame (reverseRolePair roles) anchor (not asksSource)
  where
    not : Bool → Bool
    not false = true
    not true = false

invertQueryFrameInvolutive :
  (query : QueryFrame) →
  invertQueryFrame (invertQueryFrame query) ≡ query
invertQueryFrameInvolutive (queryFrame roles anchor false)
  rewrite reverseRolePairInvolutive roles = refl
invertQueryFrameInvolutive (queryFrame roles anchor true)
  rewrite reverseRolePairInvolutive roles = refl

ContextualValuation : Set
ContextualValuation = Signed.SSPPrime → Signed.SignedMultiplicity

negateValuation : ContextualValuation → ContextualValuation
negateValuation valuation prime = Signed.negateMultiplicity (valuation prime)

negateValuationInvolutive :
  (valuation : ContextualValuation) →
  (prime : Signed.SSPPrime) →
  negateValuation (negateValuation valuation) prime ≡ valuation prime
negateValuationInvolutive valuation prime with valuation prime
... | Signed.negativeMultiplicity n = refl
... | Signed.zeroMultiplicity = refl
... | Signed.positiveMultiplicity n = refl

coarseSSPTrit : Signed.SignedMultiplicity → Trit.SSPTrit
coarseSSPTrit (Signed.negativeMultiplicity n) = Trit.sspNegOne
coarseSSPTrit Signed.zeroMultiplicity = Trit.sspZero
coarseSSPTrit (Signed.positiveMultiplicity n) = Trit.sspPosOne

coarseNegationCommutes :
  (multiplicity : Signed.SignedMultiplicity) →
  coarseSSPTrit (Signed.negateMultiplicity multiplicity)
  ≡ negateTrit (coarseSSPTrit multiplicity)
  where
    negateTrit : Trit.SSPTrit → Trit.SSPTrit
    negateTrit Trit.sspNegOne = Trit.sspPosOne
    negateTrit Trit.sspZero = Trit.sspZero
    negateTrit Trit.sspPosOne = Trit.sspNegOne
coarseNegationCommutes (Signed.negativeMultiplicity n) = refl
coarseNegationCommutes Signed.zeroMultiplicity = refl
coarseNegationCommutes (Signed.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- FRACTRAN instruction surface.  Numerator and denominator are deliberately
-- retained separately: reciprocal transport is a real machine-level operation,
-- not merely a sign label.
------------------------------------------------------------------------

record FractranFraction : Set where
  constructor fractranFraction
  field
    numeratorLanes : List Signed.SSPPrime
    denominatorLanes : List Signed.SSPPrime

open FractranFraction public

reciprocal : FractranFraction → FractranFraction
reciprocal (fractranFraction numerator denominator) =
  fractranFraction denominator numerator

reciprocalInvolutive :
  (fraction : FractranFraction) →
  reciprocal (reciprocal fraction) ≡ fraction
reciprocalInvolutive (fractranFraction numerator denominator) = refl

------------------------------------------------------------------------
-- Backward restriction from closed document state to one token occurrence.
-- The compiler is intentionally parameterised by the actual restriction law:
-- this module records the shape and the laws rather than inventing one global
-- lexical dictionary.
------------------------------------------------------------------------

record DocumentFractranState : Set where
  constructor documentFractranState
  field
    closedInterface : Document.ClosedInterface
    globalValuation : ContextualValuation

open DocumentFractranState public

data WorldId : Set where
  world : Nat → WorldId

record ContextualOccurrenceState : Set where
  constructor contextualOccurrenceState
  field
    document : DocumentFractranState
    worldId : WorldId
    occurrence : Occurrence.ScopedTokenOccurrence
    query : QueryFrame
    inheritedValuation : ContextualValuation
    localValuation : ContextualValuation
    contextualValuation : ContextualValuation
    enabledProgram : List FractranFraction

open ContextualOccurrenceState public

record BackwardDerivationLaw : Set₁ where
  constructor backwardDerivationLaw
  field
    derive :
      DocumentFractranState →
      WorldId →
      Occurrence.ScopedTokenOccurrence →
      QueryFrame →
      ContextualOccurrenceState

    preservesOccurrence :
      (document : DocumentFractranState) →
      (worldId : WorldId) →
      (occurrence : Occurrence.ScopedTokenOccurrence) →
      (query : QueryFrame) →
      ContextualOccurrenceState.occurrence
        (derive document worldId occurrence query)
      ≡ occurrence

    preservesDocument :
      (document : DocumentFractranState) →
      (worldId : WorldId) →
      (occurrence : Occurrence.ScopedTokenOccurrence) →
      (query : QueryFrame) →
      ContextualOccurrenceState.document
        (derive document worldId occurrence query)
      ≡ document

open BackwardDerivationLaw public

------------------------------------------------------------------------
-- Query observation and residual fibre.
-- Different fine world-relative valuations may have the same requested trit.
------------------------------------------------------------------------

record RequestedPrimeObservation : Set where
  constructor requestedPrimeObservation
  field
    requestedPrime : Signed.SSPPrime
    observedTrit : Trit.SSPTrit

open RequestedPrimeObservation public

observePrime :
  Signed.SSPPrime →
  ContextualValuation →
  RequestedPrimeObservation
observePrime prime valuation =
  requestedPrimeObservation prime (coarseSSPTrit (valuation prime))

record ResidualWorldFibre : Set where
  constructor residualWorldFibre
  field
    worlds : List WorldId
    unresolvedValuations : List ContextualValuation

open ResidualWorldFibre public

record QueryProjectedOccurrence : Set where
  constructor queryProjectedOccurrence
  field
    fine : ContextualOccurrenceState
    observation : RequestedPrimeObservation
    residual : ResidualWorldFibre

open QueryProjectedOccurrence public

------------------------------------------------------------------------
-- Phase inversion is candidate reciprocal transport.  It becomes semantic only
-- under a situated admissibility receipt supplied by the bracket/world layer.
------------------------------------------------------------------------

record PhaseInversionCandidate : Set where
  constructor phaseInversionCandidate
  field
    beforeQuery : QueryFrame
    afterQuery : QueryFrame
    queryIsInverted : afterQuery ≡ invertQueryFrame beforeQuery
    beforeValuation : ContextualValuation
    afterValuation : ContextualValuation
    valuationIsNegated :
      (prime : Signed.SSPPrime) →
      afterValuation prime ≡ negateValuation beforeValuation prime
    beforeInstruction : FractranFraction
    afterInstruction : FractranFraction
    instructionIsReciprocal : afterInstruction ≡ reciprocal beforeInstruction

open PhaseInversionCandidate public

record SituatedAdmissibility : Set where
  constructor situatedAdmissibility
  field
    stratumAllows : Bool
    bracketEnables : Bool
    worldAllows : Bool
    provenanceAllows : Bool

open SituatedAdmissibility public

allSituatedChecksPass : SituatedAdmissibility → Bool
allSituatedChecksPass
  (situatedAdmissibility true true true true) = true
allSituatedChecksPass _ = false

record LawfulPhaseTransport : Set where
  constructor lawfulPhaseTransport
  field
    candidate : PhaseInversionCandidate
    admissibility : SituatedAdmissibility
    admissible : allSituatedChecksPass admissibility ≡ true

open LawfulPhaseTransport public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record ContextualFractranBoundary : Set where
  constructor contextualFractranBoundary
  field
    lexicalSurfaceHasOneGlobalPrime : Bool
    posTagAloneDeterminesValuation : Bool
    parserPromotesWorldFact : Bool
    reciprocalAlwaysSemanticallyLawful : Bool
    sameCoarseTritMeansSameWorld : Bool
    contextualValueIsWorldRelative : Bool
    reciprocalIsCandidatePhaseInverse : Bool

canonicalContextualFractranBoundary : ContextualFractranBoundary
canonicalContextualFractranBoundary =
  contextualFractranBoundary
    false false false false false true true
