module DASHI.Unified.TOESectorRealizationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Validation is a transport ladder, not a confidence score.

data ValidationGrade : Set where
  conjecturalStructural : ValidationGrade
  sharedCarrier : ValidationGrade
  representationIntertwiner : ValidationGrade
  dynamicsIntertwiner : ValidationGrade
  sameActionHamiltonian : ValidationGrade
  stressObservablePreserved : ValidationGrade
  calibratedSamePhysicalObject : ValidationGrade
  heldOutEmpiricalPrediction : ValidationGrade
  independentReplication : ValidationGrade

canonicalValidationGrades : List ValidationGrade
canonicalValidationGrades =
  conjecturalStructural
  ∷ sharedCarrier
  ∷ representationIntertwiner
  ∷ dynamicsIntertwiner
  ∷ sameActionHamiltonian
  ∷ stressObservablePreserved
  ∷ calibratedSamePhysicalObject
  ∷ heldOutEmpiricalPrediction
  ∷ independentReplication
  ∷ []

data RealizationKind : Set where
  literalEquality : RealizationKind
  equivalenceIsomorphism : RealizationKind
  quotientFactor : RealizationKind
  restrictionInclusion : RealizationKind
  representationIntertwinerKind : RealizationKind
  sharedCharacterOnly : RealizationKind
  conjecturalPhysicalRealization : RealizationKind
  refutedNonDescent : RealizationKind

canonicalRealizationKinds : List RealizationKind
canonicalRealizationKinds =
  literalEquality
  ∷ equivalenceIsomorphism
  ∷ quotientFactor
  ∷ restrictionInclusion
  ∷ representationIntertwinerKind
  ∷ sharedCharacterOnly
  ∷ conjecturalPhysicalRealization
  ∷ refutedNonDescent
  ∷ []

data TOESector : Set where
  hyperfabric369Sector : TOESector
  monster3BSector : TOESector
  exceptionalGeometrySector : TOESector
  yangMillsSector : TOESector
  electromagnetismSector : TOESector
  qftStressSector : TOESector
  generalRelativitySector : TOESector
  quantumMereologySector : TOESector
  matterHamiltonianSector : TOESector
  arithmeticCMSector : TOESector
  continuumDynamicsSector : TOESector
  modularObserverSector : TOESector

data RealizationObligation : Set where
  carrierAgreement : RealizationObligation
  representationActionAgreement : RealizationObligation
  dynamicsEquivariance : RealizationObligation
  actionHamiltonianAgreement : RealizationObligation
  metricVariationCommutes : RealizationObligation
  stressObservableAgreement : RealizationObligation
  scaleCalibrationAgreement : RealizationObligation
  empiricalSameObjectAttachment : RealizationObligation
  heldOutPredictionReceipt : RealizationObligation
  independentReplicationReceipt : RealizationObligation
  nonDescentWitness : RealizationObligation

-- Weakest paid edge controls ordinary composition.  Stronger promotion must be
-- supplied by a separate theorem/witness, never inferred by transitivity.
composeGrade : ValidationGrade → ValidationGrade → ValidationGrade
composeGrade conjecturalStructural _ = conjecturalStructural
composeGrade _ conjecturalStructural = conjecturalStructural
composeGrade sharedCarrier _ = sharedCarrier
composeGrade _ sharedCarrier = sharedCarrier
composeGrade representationIntertwiner _ = representationIntertwiner
composeGrade _ representationIntertwiner = representationIntertwiner
composeGrade dynamicsIntertwiner _ = dynamicsIntertwiner
composeGrade _ dynamicsIntertwiner = dynamicsIntertwiner
composeGrade sameActionHamiltonian _ = sameActionHamiltonian
composeGrade _ sameActionHamiltonian = sameActionHamiltonian
composeGrade stressObservablePreserved _ = stressObservablePreserved
composeGrade _ stressObservablePreserved = stressObservablePreserved
composeGrade calibratedSamePhysicalObject _ = calibratedSamePhysicalObject
composeGrade _ calibratedSamePhysicalObject = calibratedSamePhysicalObject
composeGrade heldOutEmpiricalPrediction _ = heldOutEmpiricalPrediction
composeGrade _ heldOutEmpiricalPrediction = heldOutEmpiricalPrediction
composeGrade independentReplication independentReplication = independentReplication

record SectorRealization (Source Target : Set) : Set₁ where
  field
    sourceSector : TOESector
    targetSector : TOESector
    realize : Source → Target
    relationKind : RealizationKind
    attainedGrade : ValidationGrade
    unpaidObligations : List RealizationObligation

    PreservationWitness : Set
    preservationWitness : PreservationWitness

    externalPromotion : Bool
    externalPromotionIsFalse : externalPromotion ≡ false
    reading : String

open SectorRealization public

conjecturalSocket :
  {Source Target : Set} →
  TOESector → TOESector →
  (Source → Target) →
  List RealizationObligation →
  String →
  SectorRealization Source Target
conjecturalSocket source target map obligations reading =
  record
    { sourceSector = source
    ; targetSector = target
    ; realize = map
    ; relationKind = conjecturalPhysicalRealization
    ; attainedGrade = conjecturalStructural
    ; unpaidObligations = obligations
    ; PreservationWitness = ⊤
    ; preservationWitness = tt
    ; externalPromotion = false
    ; externalPromotionIsFalse = refl
    ; reading = reading
    }

composeRealizations :
  {A B C : Set} →
  SectorRealization A B →
  SectorRealization B C →
  SectorRealization A C
composeRealizations left right =
  record
    { sourceSector = sourceSector left
    ; targetSector = targetSector right
    ; realize = λ a → realize right (realize left a)
    ; relationKind = conjecturalPhysicalRealization
    ; attainedGrade = composeGrade (attainedGrade left) (attainedGrade right)
    ; unpaidObligations = unpaidObligations left ++ unpaidObligations right
    ; PreservationWitness = PreservationWitness left × PreservationWitness right
    ; preservationWitness = preservationWitness left , preservationWitness right
    ; externalPromotion = false
    ; externalPromotionIsFalse = refl
    ; reading =
        "Composed TOE realization. The attained grade is bounded by the weakest paid edge; all unpaid obligations are retained."
    }

record StrongerTransportWitness : Set where
  field
    promotedGrade : ValidationGrade
    justification : String

promoteWithExplicitWitness :
  {A B : Set} →
  SectorRealization A B →
  StrongerTransportWitness →
  ValidationGrade
promoteWithExplicitWitness realization witness =
  StrongerTransportWitness.promotedGrade witness
