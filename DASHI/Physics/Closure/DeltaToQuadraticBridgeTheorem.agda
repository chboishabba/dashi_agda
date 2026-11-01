module DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem where

-- Thin Delta-side packaging surface.
-- This module does not derive a new quadratic from arithmetic on its own.
-- It packages a Delta-side quadratic candidate under the theorem-level
-- admissibility seam already used by the contraction -> quadratic stack.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec; []; _∷_)
open import Ontology.GodelLattice using (Vec15)
open import Ontology.GodelLattice renaming (v15 to mkVec15)

import DASHI.Arithmetic.DeltaInteraction as DInt
import DASHI.Arithmetic.KPrimeInteraction as KInt
import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge as AIEB
import DASHI.Arithmetic.ArithmeticPrimeProfileBridge as APPB
import DASHI.Arithmetic.WeightedPressure as WP
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.SignatureUniqueness31 as SU
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QCB

record DeltaToQuadraticBridgeTheorem : Setω where
  field
    deltaInteractionSurface : DInt.DeltaInteractionSurface
    kPrimeInteractionSurface : KInt.KPrimeInteractionSurface
    contractionForcesQuadraticTheorem : CFQT.ContractionForcesQuadraticTheorem
    contractionQuadraticToSignatureBridge :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    deltaQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension
            contractionForcesQuadraticTheorem})
        QES.ScalarFieldℤ
    deltaQuadraticAdmissible :
      CFQS.AdmissibleFor
        (CFQT.ContractionForcesQuadraticTheorem.dimension
          contractionForcesQuadraticTheorem)
        (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap
          contractionForcesQuadraticTheorem)
        deltaQuadratic

  normalizedDeltaQuadratic :
    ∀ x →
      QF.QuadraticForm.Q deltaQuadratic x ≡ QP.Q̂core x
  normalizedDeltaQuadratic =
    CFQS.admissibleForNormalization deltaQuadraticAdmissible

  canonicalQuadraticAgreesWithDelta :
    ∀ x →
      QF.QuadraticForm.Q
        (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic
          contractionForcesQuadraticTheorem)
        x
      ≡
      QF.QuadraticForm.Q deltaQuadratic x
  canonicalQuadraticAgreesWithDelta x =
    CFQT.canonicalOutputAgreement
      contractionForcesQuadraticTheorem
      deltaQuadratic
      (CFQS.AdmissibleFor.uniqueUpToScale deltaQuadraticAdmissible)
      x

  deltaQuadraticAgreesWithCanonical :
    ∀ x →
      QF.QuadraticForm.Q deltaQuadratic x
      ≡
      QF.QuadraticForm.Q
        (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic
          contractionForcesQuadraticTheorem)
        x
  deltaQuadraticAgreesWithCanonical x =
    sym (canonicalQuadraticAgreesWithDelta x)

  inheritedSignature31Theorem :
    SU.Signature31Theorem
  inheritedSignature31Theorem =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Theorem
      contractionQuadraticToSignatureBridge

  inheritedSignature31Value :
    CTI.Signature
  inheritedSignature31Value =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
      contractionQuadraticToSignatureBridge

  inheritedSignatureForced31 :
    inheritedSignature31Value ≡ CTI.sig31
  inheritedSignatureForced31 =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
      contractionQuadraticToSignatureBridge

fromAdmissibleDeltaCandidate :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (signatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (qΔ :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
      QES.ScalarFieldℤ) →
  (admissibleΔ :
    CFQS.AdmissibleFor
      (CFQT.ContractionForcesQuadraticTheorem.dimension theorem)
      (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap theorem)
      qΔ) →
  DeltaToQuadraticBridgeTheorem
fromAdmissibleDeltaCandidate theorem signatureBridge deltaSurface kSurface qΔ admissibleΔ =
  record
    { deltaInteractionSurface = deltaSurface
    ; kPrimeInteractionSurface = kSurface
    ; contractionForcesQuadraticTheorem = theorem
    ; contractionQuadraticToSignatureBridge = signatureBridge
    ; deltaQuadratic = qΔ
    ; deltaQuadraticAdmissible = admissibleΔ
    }

record DeltaQuadraticSignatureCliffordPackage : Setω where
  field
    deltaBridgeTheorem : DeltaToQuadraticBridgeTheorem
    quadraticToCliffordBridge :
      QCB.QuadraticToCliffordBridgeTheorem
    cliffordPresentation :
      QCB.CliffordPresentation
        (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
          (DeltaToQuadraticBridgeTheorem.contractionQuadraticToSignatureBridge
            deltaBridgeTheorem))

  normalizedDeltaQuadratic :
    ∀ x →
      QF.QuadraticForm.Q
        (DeltaToQuadraticBridgeTheorem.deltaQuadratic deltaBridgeTheorem)
        x
      ≡ QP.Q̂core x
  normalizedDeltaQuadratic =
    DeltaToQuadraticBridgeTheorem.normalizedDeltaQuadratic
      deltaBridgeTheorem

  inheritedSignature31Theorem :
    SU.Signature31Theorem
  inheritedSignature31Theorem =
    DeltaToQuadraticBridgeTheorem.inheritedSignature31Theorem
      deltaBridgeTheorem

  inheritedSignature31Value :
    CTI.Signature
  inheritedSignature31Value =
    DeltaToQuadraticBridgeTheorem.inheritedSignature31Value
      deltaBridgeTheorem

  inheritedSignatureForced31 :
    inheritedSignature31Value ≡ CTI.sig31
  inheritedSignatureForced31 =
    DeltaToQuadraticBridgeTheorem.inheritedSignatureForced31
      deltaBridgeTheorem
deltaBridgeToSignatureCliffordPackage :
  (deltaBridge : DeltaToQuadraticBridgeTheorem) →
  (cliffordBridge : QCB.QuadraticToCliffordBridgeTheorem) →
  (presentation :
    QCB.CliffordPresentation
      (CQSB.ContractionQuadraticToSignatureBridgeTheorem.strengthenedContraction
        (DeltaToQuadraticBridgeTheorem.contractionQuadraticToSignatureBridge
          deltaBridge))) →
  DeltaQuadraticSignatureCliffordPackage
deltaBridgeToSignatureCliffordPackage deltaBridge cliffordBridge presentation =
  record
    { deltaBridgeTheorem = deltaBridge
    ; quadraticToCliffordBridge = cliffordBridge
    ; cliffordPresentation = presentation
    }

record DeltaQuadraticCandidate : Setω where
  field
    theoremSurface : CFQT.ContractionForcesQuadraticTheorem
    signatureBridgeSurface :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem
    deltaInteractionInput : DInt.DeltaInteractionSurface
    kPrimeInteractionInput : KInt.KPrimeInteractionSurface
    pressureBridge : AIEB.IntegerEmbeddingPressureBridge
    arithmeticEnergyℤ :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge → ℤ
    stateTransport :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge →
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension
            theoremSurface})
    candidateQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension
            theoremSurface})
        QES.ScalarFieldℤ
    arithmeticEnergyMatchesBridgePressure :
      ∀ s →
        arithmeticEnergyℤ s
        ≡
        + (AIEB.embed-scalarCancellationPressure pressureBridge s)
    transportedEnergyMatchesCandidateQuadratic :
      ∀ s →
        arithmeticEnergyℤ s
        ≡
        QF.QuadraticForm.Q candidateQuadratic (stateTransport s)
    candidateAdmissible :
      CFQS.AdmissibleFor
        (CFQT.ContractionForcesQuadraticTheorem.dimension
          theoremSurface)
        (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap
          theoremSurface)
        candidateQuadratic

  normalizedDeltaQuadratic :
    ∀ x →
      QF.QuadraticForm.Q candidateQuadratic x ≡ QP.Q̂core x
  normalizedDeltaQuadratic =
    CFQS.admissibleForNormalization candidateAdmissible

  canonicalQuadraticAgreesWithDelta :
    ∀ x →
      QF.QuadraticForm.Q
        (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic
          theoremSurface)
        x
      ≡
      QF.QuadraticForm.Q candidateQuadratic x
  canonicalQuadraticAgreesWithDelta x =
    CFQT.canonicalOutputAgreement
      theoremSurface
      candidateQuadratic
      (CFQS.AdmissibleFor.uniqueUpToScale candidateAdmissible)
      x

  inheritedSignature31Theorem :
    SU.Signature31Theorem
  inheritedSignature31Theorem =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Theorem
      signatureBridgeSurface

  inheritedSignature31Value :
    CTI.Signature
  inheritedSignature31Value =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signature31Value
      signatureBridgeSurface

  inheritedSignatureForced31 :
    inheritedSignature31Value ≡ CTI.sig31
  inheritedSignatureForced31 =
    CQSB.ContractionQuadraticToSignatureBridgeTheorem.signatureForced31
      signatureBridgeSurface

DeltaPair : Set
DeltaPair = AIE.Int × AIE.Int

pairIntegerPressureBridge : AIEB.IntegerEmbeddingPressureBridge
pairIntegerPressureBridge =
  record
    { IntegerState = DeltaPair
    ; embed = λ { (x , y) → AIE.embed x y }
    ; totalPrimePressure = λ { (x , y) → AIE.deltaSum x y }
    ; scalarCancellationPressure = λ { (x , y) → AIE.deltaSum x y }
    ; totalPrimePressure-law = λ { (x , y) → AIE.embed-primeIndexedPressure x y }
    ; scalarCancellationPressure-law = λ { (x , y) → AIE.embed-StateCancellationPressure x y }
    ; oneStepSupportBound = λ { (x , y) → AIE.embed-oneStepSupportBound x y }
    }

pairCancellationEnergy : DeltaPair → ℤ
pairCancellationEnergy s =
  + (AIEB.embed-scalarCancellationPressure pairIntegerPressureBridge s)

pairWeightedEnergy : DeltaPair → Nat
pairWeightedEnergy (x , y) = WP.weightedPressure x y

pairWeightedEnergyℤ : DeltaPair → ℤ
pairWeightedEnergyℤ s = + (pairWeightedEnergy s)

liftPrimeContributionVec :
  Vec15 Nat → Vec ℤ 15
liftPrimeContributionVec
  (mkVec15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71) =
  + a2 ∷ + a3 ∷ + a5 ∷ + a7 ∷ + a11 ∷ + a13 ∷ + a17 ∷ + a19 ∷
  + a23 ∷ + a29 ∷ + a31 ∷ + a41 ∷ + a47 ∷ + a59 ∷ + a71 ∷ []

cancellation-is-delta-sum :
  ∀ x y →
  pairCancellationEnergy (x , y) ≡ + (AIE.deltaSum x y)
cancellation-is-delta-sum x y = refl

deltaSum-equals-embeddedPressure :
  ∀ x y →
  + (AIE.deltaSum x y)
  ≡
  + (AIEB.embed-scalarCancellationPressure pairIntegerPressureBridge (x , y))
deltaSum-equals-embeddedPressure x y = refl

pairCancellationEnergyMatchesEmbeddedProfileScore :
  ∀ x y →
    pairCancellationEnergy (x , y)
    ≡
    + (APPB.embeddedProfileScore x y)
pairCancellationEnergyMatchesEmbeddedProfileScore x y =
  trans
    (cancellation-is-delta-sum x y)
    (cong +_
      (sym
        (trans
          (AIE.embed-primeIndexedPressure x y)
          (AIE.embed-StateCancellationPressure x y))))

record EmbeddedProfileScoreCompatibility
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) : Setω where
  field
    pressureBridge : AIEB.IntegerEmbeddingPressureBridge
    arithmeticEnergyℤ :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge → ℤ
    profileScoreℤ :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge → ℤ
    stateTransport :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge →
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
    arithmeticEnergyMatchesBridgePressure :
      ∀ s →
        arithmeticEnergyℤ s
        ≡
        + (AIEB.embed-scalarCancellationPressure pressureBridge s)
    arithmeticEnergyMatchesProfileScore :
      ∀ s →
        arithmeticEnergyℤ s ≡ profileScoreℤ s

open EmbeddedProfileScoreCompatibility public
  renaming
    ( pressureBridge to profilePressureBridge
    ; arithmeticEnergyℤ to profileArithmeticEnergyℤ
    ; profileScoreℤ to embeddedProfileScoreℤ
    ; stateTransport to profileStateTransport
    ; arithmeticEnergyMatchesBridgePressure to
        profileArithmeticEnergyMatchesBridgePressure
    ; arithmeticEnergyMatchesProfileScore to
        profileArithmeticEnergyMatchesProfileScore
    )

contractionEnergy :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem}) →
  ℤ
contractionEnergy theorem v =
  QF.QuadraticForm.Q
    (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic theorem)
    v

canonicalDeltaTransport :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15 →
  DeltaPair →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
canonicalDeltaTransport theorem refl (x , y) =
  liftPrimeContributionVec (APPB.embeddedProfileCarrier x y)

canonicalEmbeddedProfileScoreCompatibility :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  EmbeddedProfileScoreCompatibility theorem dim≡15
canonicalEmbeddedProfileScoreCompatibility theorem dim≡15 =
  record
    { pressureBridge = pairIntegerPressureBridge
    ; arithmeticEnergyℤ = pairCancellationEnergy
    ; profileScoreℤ = λ { (x , y) → + (APPB.embeddedProfileScore x y) }
    ; stateTransport = canonicalDeltaTransport theorem dim≡15
    ; arithmeticEnergyMatchesBridgePressure = λ _ → refl
    ; arithmeticEnergyMatchesProfileScore =
        λ { (x , y) → pairCancellationEnergyMatchesEmbeddedProfileScore x y }
    }

record CancellationPressureCompatibility
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) : Setω where
  field
    pressureBridge : AIEB.IntegerEmbeddingPressureBridge
    arithmeticEnergyℤ :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge → ℤ
    stateTransport :
      AIEB.IntegerEmbeddingPressureBridge.IntegerState pressureBridge →
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
    arithmeticEnergyMatchesBridgePressure :
      ∀ s →
        arithmeticEnergyℤ s
        ≡
        + (AIEB.embed-scalarCancellationPressure pressureBridge s)
    pressurePreserved :
      ∀ s →
        + (AIEB.embed-scalarCancellationPressure pressureBridge s)
        ≡
        contractionEnergy theorem (stateTransport s)

  candidateQuadraticAgreement :
    ∀ s →
      arithmeticEnergyℤ s
      ≡
      QF.QuadraticForm.Q
        (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic theorem)
        (stateTransport s)
  candidateQuadraticAgreement s =
    trans
      (arithmeticEnergyMatchesBridgePressure s)
      (pressurePreserved s)

open CancellationPressureCompatibility public

canonicalCancellationPressureCompatibility :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  (pressureWitness :
    ∀ s →
      + (AIEB.embed-scalarCancellationPressure pairIntegerPressureBridge s)
      ≡
      contractionEnergy theorem (canonicalDeltaTransport theorem dim≡15 s)) →
  CancellationPressureCompatibility theorem dim≡15
canonicalCancellationPressureCompatibility theorem dim≡15 pressureWitness =
  record
    { pressureBridge = pairIntegerPressureBridge
    ; arithmeticEnergyℤ = pairCancellationEnergy
    ; stateTransport = canonicalDeltaTransport theorem dim≡15
    ; arithmeticEnergyMatchesBridgePressure = λ _ → refl
    ; pressurePreserved = pressureWitness
    }

CancellationPressureToCanonicalQuadraticAssumption :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  Setω
CancellationPressureToCanonicalQuadraticAssumption =
  CancellationPressureCompatibility

pairCancellationEnergyMatchesCanonicalQuadratic :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  (pressureWitness :
    ∀ s →
      + (AIEB.embed-scalarCancellationPressure pairIntegerPressureBridge s)
      ≡
      contractionEnergy theorem (canonicalDeltaTransport theorem dim≡15 s)) →
  ∀ s →
    pairCancellationEnergy s
    ≡
    QF.QuadraticForm.Q
      (CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic theorem)
      (canonicalDeltaTransport theorem dim≡15 s)
pairCancellationEnergyMatchesCanonicalQuadratic theorem dim≡15 pressureWitness =
  candidateQuadraticAgreement
    (canonicalCancellationPressureCompatibility
      theorem
      dim≡15
      pressureWitness)

canonicalCancellationDeltaCandidateFromTransportWitness :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (signatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  CancellationPressureCompatibility theorem dim≡15 →
  DeltaQuadraticCandidate
canonicalCancellationDeltaCandidateFromTransportWitness
  theorem signatureBridge deltaSurface kSurface dim≡15 compatibility =
  record
    { theoremSurface = theorem
    ; signatureBridgeSurface = signatureBridge
    ; deltaInteractionInput = deltaSurface
    ; kPrimeInteractionInput = kSurface
    ; pressureBridge =
        CancellationPressureCompatibility.pressureBridge compatibility
    ; arithmeticEnergyℤ =
        CancellationPressureCompatibility.arithmeticEnergyℤ compatibility
    ; stateTransport =
        CancellationPressureCompatibility.stateTransport compatibility
    ; candidateQuadratic =
        CFQT.ContractionForcesQuadraticTheorem.derivedQuadratic theorem
    ; arithmeticEnergyMatchesBridgePressure =
        CancellationPressureCompatibility.arithmeticEnergyMatchesBridgePressure
          compatibility
    ; transportedEnergyMatchesCandidateQuadratic =
        CancellationPressureCompatibility.candidateQuadraticAgreement
          compatibility
    ; candidateAdmissible =
        CFQT.ContractionForcesQuadraticTheorem.admissibleQuadratic theorem
    }

deltaCandidateNormalizesQuadratic :
  (candidate : DeltaQuadraticCandidate) →
  ∀ x →
    QF.QuadraticForm.Q
      (DeltaQuadraticCandidate.candidateQuadratic candidate)
      x
    ≡ QP.Q̂core x
deltaCandidateNormalizesQuadratic candidate =
  DeltaQuadraticCandidate.normalizedDeltaQuadratic candidate

deltaCandidateForcesLorentzSignature :
  (candidate : DeltaQuadraticCandidate) →
  DeltaQuadraticCandidate.inheritedSignature31Value candidate ≡ CTI.sig31
deltaCandidateForcesLorentzSignature candidate =
  DeltaQuadraticCandidate.inheritedSignatureForced31 candidate

record WeightedValuationMeasurementCandidate : Setω where
  field
    theoremSurface : CFQT.ContractionForcesQuadraticTheorem
    deltaInteractionInput : DInt.DeltaInteractionSurface
    kPrimeInteractionInput : KInt.KPrimeInteractionSurface
    weightedSurface : WVE.WeightedValuationEnergySurface
    arithmeticInput : WVE.ArithmeticPair
    weightedValuationEnergyℤ : ℤ
    weightedQuadraticEnergyℤ : ℤ
    valuationTransport :
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface})
    weightedValuationTransport :
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface})
    weightedQuadraticTransport :
      PD.Additive.Carrier
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface})

WeightedInput : Set
WeightedInput = WVE.ArithmeticPair

canonicalWeightedValuationTransport :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15 →
  AIE.Int →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
canonicalWeightedValuationTransport theorem refl n =
  WVE.weightedValuationVecℤ n

canonicalValuationTransport :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15 →
  AIE.Int →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
canonicalValuationTransport theorem refl n =
  WVE.valuationVecℤ n

canonicalWeightedQuadraticTransport :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15 →
  AIE.Int →
  PD.Additive.Carrier
    (QES.AdditiveVecℤ
      {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
canonicalWeightedQuadraticTransport theorem refl n =
  WVE.weightedQuadraticVecℤ n

canonicalWeightedValuationMeasurementCandidate :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  WeightedInput →
  WeightedValuationMeasurementCandidate
canonicalWeightedValuationMeasurementCandidate
  theorem deltaSurface kSurface dim≡15 (x , y) =
  record
    { theoremSurface = theorem
    ; deltaInteractionInput = deltaSurface
    ; kPrimeInteractionInput = kSurface
    ; weightedSurface = WVE.weightedValuationEnergySurface
    ; arithmeticInput = (x , y)
    ; weightedValuationEnergyℤ =
        + (WVE.weightedValuationEnergy x)
    ; weightedQuadraticEnergyℤ =
        + (WVE.weightedQuadraticEnergy x)
    ; valuationTransport =
        canonicalValuationTransport theorem dim≡15 x
    ; weightedValuationTransport =
        canonicalWeightedValuationTransport theorem dim≡15 x
    ; weightedQuadraticTransport =
        canonicalWeightedQuadraticTransport theorem dim≡15 x
    }

canonicalWeightedValuationCandidateWeightedLaneAgreement :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  ∀ x y →
    WeightedValuationMeasurementCandidate.weightedValuationTransport
      (canonicalWeightedValuationMeasurementCandidate
        theorem deltaSurface kSurface dim≡15 (x , y))
    ≡
    canonicalWeightedValuationTransport theorem dim≡15 x
canonicalWeightedValuationCandidateWeightedLaneAgreement theorem deltaSurface kSurface dim≡15 x y =
  refl

canonicalWeightedValuationCandidateQuadraticLaneAgreement :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  ∀ x y →
    WeightedValuationMeasurementCandidate.weightedQuadraticTransport
      (canonicalWeightedValuationMeasurementCandidate
        theorem deltaSurface kSurface dim≡15 (x , y))
    ≡
    canonicalWeightedQuadraticTransport theorem dim≡15 x
canonicalWeightedValuationCandidateQuadraticLaneAgreement theorem deltaSurface kSurface dim≡15 x y =
  refl

record WeightedValuationTransportCompatibility
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15)
  (n : AIE.Int) : Setω where
  field
    candidateQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
        QES.ScalarFieldℤ
    candidateAdmissible :
      CFQS.AdmissibleFor
        (CFQT.ContractionForcesQuadraticTheorem.dimension theorem)
        (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap theorem)
        candidateQuadratic
    valuationTransportCoherent :
      canonicalValuationTransport theorem dim≡15 n
      ≡
      subst (Vec ℤ) (sym dim≡15) (WVE.valuationVecℤ n)
    weightedValuationTransportCoherent :
      canonicalWeightedValuationTransport theorem dim≡15 n
      ≡
      subst (Vec ℤ) (sym dim≡15) (WVE.weightedValuationVecℤ n)
    weightedQuadraticTransportCoherent :
      canonicalWeightedQuadraticTransport theorem dim≡15 n
      ≡
      subst (Vec ℤ) (sym dim≡15) (WVE.weightedQuadraticVecℤ n)
    weightedQuadraticEnergyMatchesCandidateQuadratic :
      + (WVE.weightedQuadraticEnergy n)
      ≡
      QF.QuadraticForm.Q
        candidateQuadratic
        (canonicalWeightedQuadraticTransport theorem dim≡15 n)

open WeightedValuationTransportCompatibility public

record WeightedValuationForwardCandidate : Setω where
  field
    theoremSurface : CFQT.ContractionForcesQuadraticTheorem
    deltaInteractionInput : DInt.DeltaInteractionSurface
    kPrimeInteractionInput : KInt.KPrimeInteractionSurface
    dimension15 :
      CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface ≡ 15
    weightedMeasurement : WeightedValuationMeasurementCandidate
    transportCompatibility :
      WeightedValuationTransportCompatibility
        theoremSurface
        dimension15
        (WVE.left
          (WeightedValuationMeasurementCandidate.arithmeticInput
            weightedMeasurement))

  forwardCandidateQuadratic :
    QF.QuadraticForm
      (QES.AdditiveVecℤ
        {CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface})
      QES.ScalarFieldℤ
  forwardCandidateQuadratic =
    WeightedValuationTransportCompatibility.candidateQuadratic
      transportCompatibility

  forwardCandidateAdmissible :
    CFQS.AdmissibleFor
      (CFQT.ContractionForcesQuadraticTheorem.dimension theoremSurface)
      (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap theoremSurface)
      forwardCandidateQuadratic
  forwardCandidateAdmissible =
    WeightedValuationTransportCompatibility.candidateAdmissible
      transportCompatibility

  weightedQuadraticCandidateAgreement :
    + (WVE.weightedQuadraticEnergy
        (WVE.left
          (WeightedValuationMeasurementCandidate.arithmeticInput
            weightedMeasurement)))
    ≡
    QF.QuadraticForm.Q
      forwardCandidateQuadratic
      (canonicalWeightedQuadraticTransport
        theoremSurface
        dimension15
        (WVE.left
          (WeightedValuationMeasurementCandidate.arithmeticInput
            weightedMeasurement)))
  weightedQuadraticCandidateAgreement =
    WeightedValuationTransportCompatibility.weightedQuadraticEnergyMatchesCandidateQuadratic
      transportCompatibility

canonicalWeightedValuationForwardCandidate :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (deltaSurface : DInt.DeltaInteractionSurface) →
  (kSurface : KInt.KPrimeInteractionSurface) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  (input : WeightedInput) →
  WeightedValuationTransportCompatibility theorem dim≡15 (WVE.left input) →
  WeightedValuationForwardCandidate
canonicalWeightedValuationForwardCandidate
  theorem deltaSurface kSurface dim≡15 input compatibility =
  record
    { theoremSurface = theorem
    ; deltaInteractionInput = deltaSurface
    ; kPrimeInteractionInput = kSurface
    ; dimension15 = dim≡15
    ; weightedMeasurement =
        canonicalWeightedValuationMeasurementCandidate
          theorem deltaSurface kSurface dim≡15 input
    ; transportCompatibility = compatibility
    }

weightedValuationForwardCandidateToDeltaBridge :
  (signatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem) →
  (candidate : WeightedValuationForwardCandidate) →
  DeltaToQuadraticBridgeTheorem
weightedValuationForwardCandidateToDeltaBridge signatureBridge candidate =
  fromAdmissibleDeltaCandidate
    (WeightedValuationForwardCandidate.theoremSurface candidate)
    signatureBridge
    (WeightedValuationForwardCandidate.deltaInteractionInput candidate)
    (WeightedValuationForwardCandidate.kPrimeInteractionInput candidate)
    (WeightedValuationForwardCandidate.forwardCandidateQuadratic candidate)
    (WeightedValuationForwardCandidate.forwardCandidateAdmissible candidate)

weightedValuationForwardCandidateNormalizesQuadratic :
  (signatureBridge : CQSB.ContractionQuadraticToSignatureBridgeTheorem) →
  (candidate : WeightedValuationForwardCandidate) →
  ∀ x →
    QF.QuadraticForm.Q
      (WeightedValuationForwardCandidate.forwardCandidateQuadratic candidate)
      x
    ≡ QP.Q̂core x
weightedValuationForwardCandidateNormalizesQuadratic signatureBridge candidate =
  DeltaToQuadraticBridgeTheorem.normalizedDeltaQuadratic
    (weightedValuationForwardCandidateToDeltaBridge signatureBridge candidate)
