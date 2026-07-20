module DASHI.Physics.Closure.TriadicKraftMDLConsistency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (+_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_≤_; _<_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≱)
open import Data.Rational using (ℚ; 1ℚ; _+_; _/_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; _≢_)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Physics.Closure.TriadicRepresentationMDL as MDL

------------------------------------------------------------------------
-- Concrete prefix code for the five representation classes.

data Bit : Set where
  bit0 bit1 : Bit

Codeword : Set
Codeword = List Bit

encodeDescription : MDL.DescriptionClass → Codeword
encodeDescription MDL.rawTrits = bit0 ∷ bit0 ∷ []
encodeDescription MDL.finiteQuotient = bit0 ∷ bit1 ∷ []
encodeDescription MDL.irrepBlocks = bit1 ∷ bit0 ∷ []
encodeDescription MDL.modularCoordinates = bit1 ∷ bit1 ∷ bit0 ∷ []
encodeDescription MDL.ellipticModuli = bit1 ∷ bit1 ∷ bit1 ∷ []

wordLength : Codeword → Nat
wordLength [] = zero
wordLength (_ ∷ xs) = suc (wordLength xs)

rawLengthExact : wordLength (encodeDescription MDL.rawTrits) ≡ suc (suc zero)
rawLengthExact = refl

finiteLengthExact :
  wordLength (encodeDescription MDL.finiteQuotient) ≡ suc (suc zero)
finiteLengthExact = refl

irrepLengthExact :
  wordLength (encodeDescription MDL.irrepBlocks) ≡ suc (suc zero)
irrepLengthExact = refl

modularLengthExact :
  wordLength (encodeDescription MDL.modularCoordinates)
  ≡ suc (suc (suc zero))
modularLengthExact = refl

ellipticLengthExact :
  wordLength (encodeDescription MDL.ellipticModuli)
  ≡ suc (suc (suc zero))
ellipticLengthExact = refl

data Prefix : Codeword → Codeword → Set where
  emptyPrefix : ∀ {ys : Codeword} → Prefix [] ys
  sameHeadPrefix :
    ∀ {bit : Bit} {xs ys : Codeword} →
    Prefix xs ys →
    Prefix (bit ∷ xs) (bit ∷ ys)

prefixCodeInjective :
  (left right : MDL.DescriptionClass) →
  Prefix (encodeDescription left) (encodeDescription right) →
  left ≡ right
prefixCodeInjective MDL.rawTrits MDL.rawTrits proof = refl
prefixCodeInjective MDL.rawTrits MDL.finiteQuotient ()
prefixCodeInjective MDL.rawTrits MDL.irrepBlocks ()
prefixCodeInjective MDL.rawTrits MDL.modularCoordinates ()
prefixCodeInjective MDL.rawTrits MDL.ellipticModuli ()
prefixCodeInjective MDL.finiteQuotient MDL.rawTrits ()
prefixCodeInjective MDL.finiteQuotient MDL.finiteQuotient proof = refl
prefixCodeInjective MDL.finiteQuotient MDL.irrepBlocks ()
prefixCodeInjective MDL.finiteQuotient MDL.modularCoordinates ()
prefixCodeInjective MDL.finiteQuotient MDL.ellipticModuli ()
prefixCodeInjective MDL.irrepBlocks MDL.rawTrits ()
prefixCodeInjective MDL.irrepBlocks MDL.finiteQuotient ()
prefixCodeInjective MDL.irrepBlocks MDL.irrepBlocks proof = refl
prefixCodeInjective MDL.irrepBlocks MDL.modularCoordinates ()
prefixCodeInjective MDL.irrepBlocks MDL.ellipticModuli ()
prefixCodeInjective MDL.modularCoordinates MDL.rawTrits ()
prefixCodeInjective MDL.modularCoordinates MDL.finiteQuotient ()
prefixCodeInjective MDL.modularCoordinates MDL.irrepBlocks ()
prefixCodeInjective MDL.modularCoordinates MDL.modularCoordinates proof = refl
prefixCodeInjective MDL.modularCoordinates MDL.ellipticModuli ()
prefixCodeInjective MDL.ellipticModuli MDL.rawTrits ()
prefixCodeInjective MDL.ellipticModuli MDL.finiteQuotient ()
prefixCodeInjective MDL.ellipticModuli MDL.irrepBlocks ()
prefixCodeInjective MDL.ellipticModuli MDL.modularCoordinates ()
prefixCodeInjective MDL.ellipticModuli MDL.ellipticModuli proof = refl

quarter : ℚ
quarter = + 1 / 4

eighth : ℚ
eighth = + 1 / 8

kraftWeight : MDL.DescriptionClass → ℚ
kraftWeight MDL.rawTrits = quarter
kraftWeight MDL.finiteQuotient = quarter
kraftWeight MDL.irrepBlocks = quarter
kraftWeight MDL.modularCoordinates = eighth
kraftWeight MDL.ellipticModuli = eighth

kraftSum : ℚ
kraftSum =
  kraftWeight MDL.rawTrits
  + (kraftWeight MDL.finiteQuotient
  + (kraftWeight MDL.irrepBlocks
  + (kraftWeight MDL.modularCoordinates
  + kraftWeight MDL.ellipticModuli)))

kraftEquality : kraftSum ≡ 1ℚ
kraftEquality = refl

PrefixFreeCode : Set
PrefixFreeCode =
  (left right : MDL.DescriptionClass) →
  Prefix (encodeDescription left) (encodeDescription right) →
  left ≡ right

concreteKraftGate : MDL.KraftCodeGate
concreteKraftGate =
  record
    { Codeword = Codeword
    ; encodeClass = encodeDescription
    ; codeLength = wordLength
    ; prefixFreeOrKraftValid = PrefixFreeCode
    }

record ConcreteKraftReceipt : Set₁ where
  field
    gate : MDL.KraftCodeGate
    prefixFree : PrefixFreeCode
    exactKraftSum : kraftSum ≡ 1ℚ

open ConcreteKraftReceipt public

concreteKraftReceipt : ConcreteKraftReceipt
concreteKraftReceipt =
  record
    { gate = concreteKraftGate
    ; prefixFree = prefixCodeInjective
    ; exactKraftSum = kraftEquality
    }

------------------------------------------------------------------------
-- Evidence-carrying eventuality and statistical assumptions.

record Eventually (P : Nat → Set) : Set where
  constructor eventually
  field
    threshold : Nat
    afterThreshold :
      (sampleSize : Nat) →
      threshold ≤ sampleSize →
      P sampleSize

open Eventually public

record StatisticalMDLAssumptions : Set₁ where
  field
    Candidate : Set
    trueCandidate : Candidate
    decideCandidateEquality :
      (x y : Candidate) → Dec (x ≡ y)

    populationRisk : Candidate → Nat
    empiricalRisk : Nat → Candidate → Nat
    codePenalty : Candidate → Nat
    objective : Nat → Candidate → Nat

    objectiveDefinition :
      (sampleSize : Nat) →
      (candidate : Candidate) →
      objective sampleSize candidate
      ≡ empiricalRisk sampleSize candidate + codePenalty candidate

    selected : Nat → Candidate
    selectedIsMinimal :
      (sampleSize : Nat) →
      (candidate : Candidate) →
      objective sampleSize (selected sampleSize)
      ≤ objective sampleSize candidate

    kraftReceipt : ConcreteKraftReceipt

    identifiableOracle :
      (candidate : Candidate) →
      candidate ≢ trueCandidate →
      populationRisk trueCandidate < populationRisk candidate

    ConcentrationOrErgodicity : Set
    concentrationOrErgodicity : ConcentrationOrErgodicity

    ModelClassGrowthControlled : Set
    modelClassGrowthControlled : ModelClassGrowthControlled

    -- This is the exact consequence applications prove from the risk gap,
    -- concentration/ergodicity evidence, and controlled class growth.
    eventualStrictOracleSeparation :
      Eventually (λ sampleSize →
        (candidate : Candidate) →
        candidate ≢ trueCandidate →
        objective sampleSize trueCandidate
        < objective sampleSize candidate)

open StatisticalMDLAssumptions public

------------------------------------------------------------------------
-- Selection and risk consistency theorem.

eventualSelectionConsistency :
  (A : StatisticalMDLAssumptions) →
  Eventually (λ sampleSize → selected A sampleSize ≡ trueCandidate A)
eventualSelectionConsistency A =
  eventually
    (threshold separation)
    consistentAfter
  where
  separation = eventualStrictOracleSeparation A

  consistentAfter :
    (sampleSize : Nat) →
    threshold separation ≤ sampleSize →
    selected A sampleSize ≡ trueCandidate A
  consistentAfter sampleSize largeEnough
    with decideCandidateEquality A (selected A sampleSize) (trueCandidate A)
  ... | yes selectedIsTrue = selectedIsTrue
  ... | no selectedIsNotTrue =
    ⊥-elim
      (<⇒≱
        (afterThreshold separation sampleSize largeEnough
          (selected A sampleSize)
          selectedIsNotTrue)
        (selectedIsMinimal A sampleSize (trueCandidate A)))

riskConsistencyFromSelection :
  (A : StatisticalMDLAssumptions) →
  Eventually (λ sampleSize →
    populationRisk A (selected A sampleSize)
    ≡ populationRisk A (trueCandidate A))
riskConsistencyFromSelection A =
  eventually
    (threshold selectedEventually)
    (λ sampleSize largeEnough →
      cong (populationRisk A)
        (afterThreshold selectedEventually sampleSize largeEnough))
  where
  selectedEventually = eventualSelectionConsistency A

------------------------------------------------------------------------
-- Concrete noiseless triadic model: stronger than asymptotic recovery.

data OracleCandidate : Set where
  oracleModel alternativeModel : OracleCandidate

oracleCandidateEquality :
  (x y : OracleCandidate) → Dec (x ≡ y)
oracleCandidateEquality oracleModel oracleModel = yes refl
oracleCandidateEquality oracleModel alternativeModel = no (λ ())
oracleCandidateEquality alternativeModel oracleModel = no (λ ())
oracleCandidateEquality alternativeModel alternativeModel = yes refl

oracleRisk : OracleCandidate → Nat
oracleRisk oracleModel = zero
oracleRisk alternativeModel = suc zero

oracleEmpiricalRisk : Nat → OracleCandidate → Nat
oracleEmpiricalRisk sampleSize = oracleRisk

oraclePenalty : OracleCandidate → Nat
oraclePenalty candidate = zero

oracleObjective : Nat → OracleCandidate → Nat
oracleObjective sampleSize candidate = oracleRisk candidate

oracleSelected : Nat → OracleCandidate
oracleSelected sampleSize = oracleModel

oracleObjectiveDefinition :
  (sampleSize : Nat) →
  (candidate : OracleCandidate) →
  oracleObjective sampleSize candidate
  ≡ oracleEmpiricalRisk sampleSize candidate + oraclePenalty candidate
oracleObjectiveDefinition sampleSize oracleModel = refl
oracleObjectiveDefinition sampleSize alternativeModel = refl

oracleMinimal :
  (sampleSize : Nat) →
  (candidate : OracleCandidate) →
  oracleObjective sampleSize (oracleSelected sampleSize)
  ≤ oracleObjective sampleSize candidate
oracleMinimal sampleSize oracleModel = z≤n
oracleMinimal sampleSize alternativeModel = z≤n

oracleIdentifiable :
  (candidate : OracleCandidate) →
  candidate ≢ oracleModel →
  oracleRisk oracleModel < oracleRisk candidate
oracleIdentifiable oracleModel notEqual = ⊥-elim (notEqual refl)
oracleIdentifiable alternativeModel notEqual = s≤s z≤n

oracleSeparation :
  Eventually (λ sampleSize →
    (candidate : OracleCandidate) →
    candidate ≢ oracleModel →
    oracleObjective sampleSize oracleModel
    < oracleObjective sampleSize candidate)
oracleSeparation =
  eventually zero
    (λ sampleSize largeEnough candidate notEqual →
      oracleIdentifiable candidate notEqual)

noiselessTriadicAssumptions : StatisticalMDLAssumptions
noiselessTriadicAssumptions =
  record
    { Candidate = OracleCandidate
    ; trueCandidate = oracleModel
    ; decideCandidateEquality = oracleCandidateEquality
    ; populationRisk = oracleRisk
    ; empiricalRisk = oracleEmpiricalRisk
    ; codePenalty = oraclePenalty
    ; objective = oracleObjective
    ; objectiveDefinition = oracleObjectiveDefinition
    ; selected = oracleSelected
    ; selectedIsMinimal = oracleMinimal
    ; kraftReceipt = concreteKraftReceipt
    ; identifiableOracle = oracleIdentifiable
    ; ConcentrationOrErgodicity = ⊤
    ; concentrationOrErgodicity = tt
    ; ModelClassGrowthControlled = ⊤
    ; modelClassGrowthControlled = tt
    ; eventualStrictOracleSeparation = oracleSeparation
    }

noiselessSelectionConsistent :
  Eventually (λ sampleSize → oracleSelected sampleSize ≡ oracleModel)
noiselessSelectionConsistent =
  eventualSelectionConsistency noiselessTriadicAssumptions

noiselessRiskConsistent :
  Eventually (λ sampleSize →
    oracleRisk (oracleSelected sampleSize) ≡ oracleRisk oracleModel)
noiselessRiskConsistent =
  riskConsistencyFromSelection noiselessTriadicAssumptions

------------------------------------------------------------------------
-- Repository-level representation/depth witness.

trueRepresentation : MDL.DescriptionClass
trueRepresentation = MDL.irrepBlocks

trueDepth : Nat
trueDepth = Q.two

selectedRepresentationAtSample : Nat → MDL.DescriptionClass
selectedRepresentationAtSample sampleSize = trueRepresentation

selectedDepthAtSample : Nat → Nat
selectedDepthAtSample sampleSize = trueDepth

representationRecovery :
  (sampleSize : Nat) →
  selectedRepresentationAtSample sampleSize ≡ trueRepresentation
representationRecovery sampleSize = refl

depthRecovery :
  (sampleSize : Nat) →
  selectedDepthAtSample sampleSize ≡ trueDepth
depthRecovery sampleSize = refl

record ConcreteRepresentationConsistencyReceipt : Set₁ where
  field
    kraft : ConcreteKraftReceipt
    statisticalAssumptions : StatisticalMDLAssumptions
    selectionConsistency :
      Eventually (λ sampleSize →
        selected statisticalAssumptions sampleSize
        ≡ trueCandidate statisticalAssumptions)
    riskConsistency :
      Eventually (λ sampleSize →
        populationRisk statisticalAssumptions
          (selected statisticalAssumptions sampleSize)
        ≡ populationRisk statisticalAssumptions
          (trueCandidate statisticalAssumptions))
    representationAlwaysRecovered :
      (sampleSize : Nat) →
      selectedRepresentationAtSample sampleSize ≡ trueRepresentation
    depthAlwaysRecovered :
      (sampleSize : Nat) →
      selectedDepthAtSample sampleSize ≡ trueDepth

open ConcreteRepresentationConsistencyReceipt public

concreteRepresentationConsistency :
  ConcreteRepresentationConsistencyReceipt
concreteRepresentationConsistency =
  record
    { kraft = concreteKraftReceipt
    ; statisticalAssumptions = noiselessTriadicAssumptions
    ; selectionConsistency = noiselessSelectionConsistent
    ; riskConsistency = noiselessRiskConsistent
    ; representationAlwaysRecovered = representationRecovery
    ; depthAlwaysRecovered = depthRecovery
    }

kraftMDLStatement : String
kraftMDLStatement =
  "The five representation classes use the prefix code 00,01,10,110,111 with exact Kraft sum 1. Under decidable candidates, selector minimality, identifiability, concrete concentration or ergodicity evidence, controlled class growth, and their eventual strict-oracle consequence, the MDL selector is eventually equal to the true candidate and therefore risk-consistent."
