module DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.NumericAuthority using (TokenId)
import DASHI.Cognition.PNF.NumericOccurrenceFibre as Occurrence
import DASHI.Cognition.PNF.NumericHyperfabric as Document
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Contextual token valuation.
--
-- A surface/POS pair does not have one global FRACTRAN value.  The value is
-- attached to a concrete token occurrence in one document/world/query fibre.
------------------------------------------------------------------------

data SemanticRole : Set where
  agentSemanticRole patientSemanticRole : SemanticRole
  sourceSemanticRole targetSemanticRole : SemanticRole
  giverSemanticRole recipientSemanticRole : SemanticRole
  premiseSemanticRole conclusionSemanticRole : SemanticRole
  evidenceSemanticRole authoritySemanticRole : SemanticRole

record OrientedRolePair : Set where
  constructor orientedRolePair
  field
    fromRole : SemanticRole
    toRole : SemanticRole

open OrientedRolePair public

reverseRolePair : OrientedRolePair → OrientedRolePair
reverseRolePair (orientedRolePair from to) = orientedRolePair to from

reverseRolePairInvolutive :
  (roles : OrientedRolePair) →
  reverseRolePair (reverseRolePair roles) ≡ roles
reverseRolePairInvolutive (orientedRolePair from to) = refl

record QueryFrame : Set where
  constructor queryFrame
  field
    orientedRoles : OrientedRolePair
    anchorToken : TokenId
    asksForSource : Bool

open QueryFrame public

flipBool : Bool → Bool
flipBool false = true
flipBool true = false

invertQueryFrame : QueryFrame → QueryFrame
invertQueryFrame (queryFrame roles anchor asksSource) =
  queryFrame (reverseRolePair roles) anchor (flipBool asksSource)

invertQueryFrameInvolutive :
  (query : QueryFrame) →
  invertQueryFrame (invertQueryFrame query) ≡ query
invertQueryFrameInvolutive (queryFrame roles anchor false)
  rewrite reverseRolePairInvolutive roles = refl
invertQueryFrameInvolutive (queryFrame roles anchor true)
  rewrite reverseRolePairInvolutive roles = refl

------------------------------------------------------------------------
-- Signed SSP valuation: machine-rich state first, ternary observation second.
------------------------------------------------------------------------

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

negateTrit : Trit.SSPTrit → Trit.SSPTrit
negateTrit Trit.sspNegOne = Trit.sspPosOne
negateTrit Trit.sspZero = Trit.sspZero
negateTrit Trit.sspPosOne = Trit.sspNegOne

coarseNegationCommutes :
  (multiplicity : Signed.SignedMultiplicity) →
  coarseSSPTrit (Signed.negateMultiplicity multiplicity)
  ≡ negateTrit (coarseSSPTrit multiplicity)
coarseNegationCommutes (Signed.negativeMultiplicity n) = refl
coarseNegationCommutes Signed.zeroMultiplicity = refl
coarseNegationCommutes (Signed.positiveMultiplicity n) = refl

------------------------------------------------------------------------
-- FRACTRAN fractions retain numerator and denominator separately.  Reciprocal
-- transport is therefore a real machine-level candidate inversion.
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
-- Backward document -> world -> occurrence restriction.
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
    documentState : DocumentFractranState
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
      ContextualOccurrenceState.documentState
        (derive document worldId occurrence query)
      ≡ document

open BackwardDerivationLaw public

------------------------------------------------------------------------
-- Query projection + retained residual world fibre.
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
-- Inversion is ambient/candidate first; semantic lawfulness is situated.
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
allSituatedChecksPass (situatedAdmissibility true true true true) = true
allSituatedChecksPass _ = false

record LawfulPhaseTransport : Set where
  constructor lawfulPhaseTransport
  field
    candidate : PhaseInversionCandidate
    admissibility : SituatedAdmissibility
    admissible : allSituatedChecksPass admissibility ≡ true

open LawfulPhaseTransport public

------------------------------------------------------------------------
-- Boundary receipts.
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
  contextualFractranBoundary false false false false false true true
