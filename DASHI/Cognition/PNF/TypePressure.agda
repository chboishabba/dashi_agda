module DASHI.Cognition.PNF.TypePressure where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; _+_)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalBranchInterference as Interference

------------------------------------------------------------------------
-- Predicate participation induces type pressure; it does not assert a type.
--
-- This is the formal seam behind the Wikidata presentation's order:
--
--   role binding -> soft type pressure -> validation/alignment.
--
-- Signed pressure remains fine integer evidence.  Reinforcing / independent /
-- interfering is derived by the existing exact signed-interaction classifier.
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
    {candidateType : CandidateType} →
  TypePressureContribution {Evidence = Evidence} subject candidateType →
  Interference.ClassifiedInteraction
    (signedPressure (TypePressureContribution {Evidence = Evidence} subject candidateType))
pressureClassification contribution =
  Interference.classifySignedInteraction (signedPressure contribution)

pressureDirection :
  ∀ {Subject CandidateType Evidence subject candidateType} →
  TypePressureContribution {Subject} {CandidateType} {Evidence}
    subject candidateType →
  Selection.InteractionDirection
pressureDirection contribution =
  Interference.interactionDirection (pressureClassification contribution)

pressureMagnitude :
  ∀ {Subject CandidateType Evidence subject candidateType} →
  TypePressureContribution {Subject} {CandidateType} {Evidence}
    subject candidateType → Nat
pressureMagnitude contribution =
  Interference.interactionMagnitude (pressureClassification contribution)

sumPressure :
  ∀ {Subject CandidateType Evidence}
    {subject : Subject}
    {candidateType : CandidateType} →
  List (TypePressureContribution {Evidence = Evidence} subject candidateType) → ℤ
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
      List (TypePressureContribution {Evidence = Evidence} subject candidateType)

open TypePressureEnvelope public

envelopePressure :
  ∀ {Subject CandidateType Evidence subject candidateType} →
  TypePressureEnvelope {Subject} {CandidateType} {Evidence}
    subject candidateType → ℤ
envelopePressure envelope = sumPressure (contributions envelope)

envelopeClassification :
  ∀ {Subject CandidateType Evidence subject candidateType}
    (envelope : TypePressureEnvelope {Subject} {CandidateType} {Evidence}
      subject candidateType) →
  Interference.ClassifiedInteraction (envelopePressure envelope)
envelopeClassification envelope =
  Interference.classifySignedInteraction (envelopePressure envelope)

------------------------------------------------------------------------
-- Predicate-role specialization: the observed relation explains why the type
-- pressure exists, but still does not grant world/type authority.
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
      TypePressureContribution {Evidence = Evidence} subject candidateType

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
  ∀ {subject candidateType} →
  NumericPredicateRolePressure subject candidateType →
  Interference.ClassifiedInteraction
    (signedRolePressure (NumericPredicateRolePressure subject candidateType))
numericRolePressureClassification pressure =
  Interference.classifySignedInteraction (signedRolePressure pressure)

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data TypePressurePromotionPermission : Set where

pressureAloneCannotAssertType : TypePressurePromotionPermission → ⊥
pressureAloneCannotAssertType ()

record TypePressureBoundary : Set where
  constructor typePressureBoundary
  field
    pressureRequiresFineSignedEvidence :
      ∀ {Subject CandidateType Evidence subject candidateType} →
      TypePressureContribution {Subject} {CandidateType} {Evidence}
        subject candidateType → ℤ
    pressureCannotPromoteType : TypePressurePromotionPermission → ⊥

open TypePressureBoundary public

canonicalTypePressureBoundary : TypePressureBoundary
canonicalTypePressureBoundary =
  typePressureBoundary signedPressure pressureAloneCannotAssertType
