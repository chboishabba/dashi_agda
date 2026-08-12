module DASHI.Cognition.PNF.TypePressure where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; _+_)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Core.ClassificationEdge as Classification
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference

------------------------------------------------------------------------
-- Predicate participation induces type pressure; it does not assert a type.
------------------------------------------------------------------------

record TypePressureContribution
    {Subject CandidateType Evidence : Set}
    (subject : Subject)
    (candidateType : CandidateType) : Set where
  constructor typePressureContribution
  field
    evidence : Evidence
    signedPressure : ℤ
    provenance : String
    scope : String

open TypePressureContribution public

pressureClassification :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType}
    (contribution :
      TypePressureContribution
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType) →
  Interference.ClassifiedInteraction (signedPressure contribution)
pressureClassification contribution =
  Interference.classifySignedInteraction (signedPressure contribution)

pressureDirection :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  TypePressureContribution
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType →
  Selection.InteractionDirection
pressureDirection contribution =
  Interference.interactionDirection (pressureClassification contribution)

pressureMagnitude :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  TypePressureContribution
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType → Nat
pressureMagnitude contribution =
  Interference.interactionMagnitude (pressureClassification contribution)

sumPressure :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  List
    (TypePressureContribution
      {Subject = Subject}
      {CandidateType = CandidateType}
      {Evidence = Evidence}
      subject candidateType) → ℤ
sumPressure [] = + 0
sumPressure (contribution ∷ rest) =
  signedPressure contribution + sumPressure rest

record TypePressureEnvelope
    {Subject CandidateType Evidence : Set}
    (subject : Subject)
    (candidateType : CandidateType) : Set where
  constructor typePressureEnvelope
  field
    contributions :
      List
        (TypePressureContribution
          {Subject = Subject}
          {CandidateType = CandidateType}
          {Evidence = Evidence}
          subject candidateType)

open TypePressureEnvelope public

envelopePressure :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  TypePressureEnvelope
    {Subject = Subject}
    {CandidateType = CandidateType}
    {Evidence = Evidence}
    subject candidateType → ℤ
envelopePressure envelope = sumPressure (contributions envelope)

envelopeClassification :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType}
    (envelope :
      TypePressureEnvelope
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType) →
  Interference.ClassifiedInteraction (envelopePressure envelope)
envelopeClassification envelope =
  Interference.classifySignedInteraction (envelopePressure envelope)

------------------------------------------------------------------------
-- Predicate-role specialization.
------------------------------------------------------------------------

record PredicateRolePressure
    {Subject CandidateType Predicate Role Evidence : Set}
    (subject : Subject)
    (candidateType : CandidateType) : Set where
  constructor predicateRolePressure
  field
    predicate : Predicate
    role : Role
    contribution :
      TypePressureContribution
        {Subject = Subject}
        {CandidateType = CandidateType}
        {Evidence = Evidence}
        subject candidateType

open PredicateRolePressure public

record NumericPredicateRolePressure
    (subject : ObjectId)
    (candidateType : SymbolId) : Set where
  constructor numericPredicateRolePressure
  field
    factor : FactorId
    roleSymbol : SymbolId
    signedRolePressure : ℤ
    pressureProvenance : String
    pressureScope : String

open NumericPredicateRolePressure public

numericRolePressureClassification :
  ∀ {subject candidateType}
    (pressure : NumericPredicateRolePressure subject candidateType) →
  Interference.ClassifiedInteraction (signedRolePressure pressure)
numericRolePressureClassification pressure =
  Interference.classifySignedInteraction (signedRolePressure pressure)

------------------------------------------------------------------------
-- Soft-type classification adapter.
--
-- Type pressure can create a revisable classification edge in the generic
-- classification carrier.  The edge records why the type is plausible; it is
-- still not a type assertion and cannot manufacture identity or ontology truth.
------------------------------------------------------------------------

record NumericTypePressureEvidence : Set where
  constructor numericTypePressureEvidence
  field
    pressureFactor : FactorId
    pressureRole : SymbolId
    pressureResidual : ℤ

open NumericTypePressureEvidence public

TypePressureClassificationEdge : Set
TypePressureClassificationEdge =
  Classification.ClassificationEdge
    ObjectId SymbolId NumericTypePressureEvidence

classificationEdgeFromTypePressure :
  ∀ {subject candidateType} →
  NumericPredicateRolePressure subject candidateType →
  Nat →
  TypePressureClassificationEdge
classificationEdgeFromTypePressure pressure revision =
  Classification.classificationEdge
    _
    _
    (numericTypePressureEvidence
      (factor pressure)
      (roleSymbol pressure)
      (signedRolePressure pressure))
    revision
    (pressureProvenance pressure)
    (pressureScope pressure)

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data TypePressurePromotionPermission : Set where

pressureAloneCannotAssertType : TypePressurePromotionPermission → ⊥
pressureAloneCannotAssertType ()

record TypePressureBoundary : Set₁ where
  constructor typePressureBoundary
  field
    pressureCannotPromoteType : TypePressurePromotionPermission → ⊥
    signedClassifierReused :
      (value : ℤ) → Interference.ClassifiedInteraction value

open TypePressureBoundary public

canonicalTypePressureBoundary : TypePressureBoundary
canonicalTypePressureBoundary =
  typePressureBoundary
    pressureAloneCannotAssertType
    Interference.classifySignedInteraction
