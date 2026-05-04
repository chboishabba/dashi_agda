module DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation where

-- W9n: narrow next-obligation surface for the cancellation-pressure seam.
--
-- This module is intentionally non-promoting.  It does not inhabit
-- CancellationPressureCompatibility.  It names the exact witness needed for
-- the existing route, and the extra identification needed before the
-- weighted-valuation route can replace that theorem-level assumption.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_,_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge as AIEB
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
import DASHI.Geometry.QuadraticForm as QF
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.QuadraticPolarization as QP
import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data W9CompatibilityRoute : Set where
  dischargeExistingCancellationPressureCompatibility : W9CompatibilityRoute
  replaceWithWeightedValuationForwardCandidate : W9CompatibilityRoute
  diagnosticOnly : W9CompatibilityRoute

record ExistingCancellationPressureCompatibilityObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    -- This is exactly the open argument of
    -- DQ.canonicalCancellationPressureCompatibility.
    pressureWitness :
      ∀ s →
        + (AIEB.embed-scalarCancellationPressure
            DQ.pairIntegerPressureBridge
            s)
        ≡
        DQ.contractionEnergy theorem
          (DQ.canonicalDeltaTransport theorem dim≡15 s)

  dischargesExisting :
    DQ.CancellationPressureCompatibility theorem dim≡15
  dischargesExisting =
    DQ.canonicalCancellationPressureCompatibility
      theorem
      dim≡15
      pressureWitness

record WeightedValuationReplacementObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    input : DQ.WeightedInput

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
      DQ.canonicalValuationTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.valuationVecℤ (WVE.left input))

    weightedValuationTransportCoherent :
      DQ.canonicalWeightedValuationTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.weightedValuationVecℤ (WVE.left input))

    weightedQuadraticTransportCoherent :
      DQ.canonicalWeightedQuadraticTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.weightedQuadraticVecℤ (WVE.left input))

    weightedQuadraticEnergyMatchesCandidateQuadratic :
      + (WVE.weightedQuadraticEnergy (WVE.left input))
      ≡
      QF.QuadraticForm.Q
        candidateQuadratic
        (DQ.canonicalWeightedQuadraticTransport
          theorem
          dim≡15
          (WVE.left input))

    -- This is the missing replacement seam.  Without it, the weighted lane
    -- can produce a forward delta candidate, but it cannot replace the
    -- cancellation-pressure compatibility expected by current consumers.
    cancellationPressureIdentifiesWeightedQuadraticEnergy :
      + (AIE.deltaSum (WVE.left input) (WVE.right input))
      ≡
      + (WVE.weightedQuadraticEnergy (WVE.left input))

  weightedTransportCompatibility :
    DQ.WeightedValuationTransportCompatibility
      theorem
      dim≡15
      (WVE.left input)
  weightedTransportCompatibility =
    record
      { candidateQuadratic = candidateQuadratic
      ; candidateAdmissible = candidateAdmissible
      ; valuationTransportCoherent = valuationTransportCoherent
      ; weightedValuationTransportCoherent = weightedValuationTransportCoherent
      ; weightedQuadraticTransportCoherent = weightedQuadraticTransportCoherent
      ; weightedQuadraticEnergyMatchesCandidateQuadratic =
          weightedQuadraticEnergyMatchesCandidateQuadratic
      }

record WeightedCancellationPressureCandidateReceipt
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15)
  (replacement :
    WeightedValuationReplacementObligation theorem dim≡15) :
  Setω where
  open WeightedValuationReplacementObligation replacement

  field
    weightedCompatibility :
      DQ.WeightedValuationTransportCompatibility
        theorem
        dim≡15
        (WVE.left input)

  cancellationPressureMatchesWeightedCandidateQuadratic :
    + (AIE.deltaSum (WVE.left input) (WVE.right input))
    ≡
    QF.QuadraticForm.Q
      candidateQuadratic
      (DQ.canonicalWeightedQuadraticTransport
        theorem
        dim≡15
        (WVE.left input))
  cancellationPressureMatchesWeightedCandidateQuadratic =
    trans
      cancellationPressureIdentifiesWeightedQuadraticEnergy
      weightedQuadraticEnergyMatchesCandidateQuadratic

weightedReplacementCandidateReceipt :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  (replacement :
    WeightedValuationReplacementObligation theorem dim≡15) →
  WeightedCancellationPressureCandidateReceipt theorem dim≡15 replacement
weightedReplacementCandidateReceipt theorem dim≡15 replacement =
  record
    { weightedCompatibility =
        WeightedValuationReplacementObligation.weightedTransportCompatibility
          replacement
    }

one : AIE.Int
one = suc zero

two : AIE.Int
two = suc one

three : AIE.Int
three = suc two

cancellationPressureWeightedQuadraticConcreteMismatch :
  (+ (AIE.deltaSum one one))
  ≢
  (+ (WVE.weightedQuadraticEnergy one))
cancellationPressureWeightedQuadraticConcreteMismatch ()

record CancellationToWeightedQuadraticIdentificationObstruction : Set where
  field
    counterexampleInput : DQ.WeightedInput

    counterexampleMismatch :
      (+ (AIE.deltaSum
          (WVE.left counterexampleInput)
          (WVE.right counterexampleInput)))
      ≢
      (+ (WVE.weightedQuadraticEnergy (WVE.left counterexampleInput)))

    noUniformIdentification :
      (∀ input →
        + (AIE.deltaSum (WVE.left input) (WVE.right input))
        ≡
        + (WVE.weightedQuadraticEnergy (WVE.left input))) →
      ⊥

canonicalCancellationToWeightedQuadraticIdentificationObstruction :
  CancellationToWeightedQuadraticIdentificationObstruction
canonicalCancellationToWeightedQuadraticIdentificationObstruction =
  record
    { counterexampleInput = one , one
    ; counterexampleMismatch =
        cancellationPressureWeightedQuadraticConcreteMismatch
    ; noUniformIdentification =
        λ identify →
          cancellationPressureWeightedQuadraticConcreteMismatch
            (identify (one , one))
    }

canonical15Theorem : CFQT.ContractionForcesQuadraticTheorem
canonical15Theorem =
  CFQT.canonicalContractionForcesQuadraticTheorem 15

canonical15Dimension : CFQT.ContractionForcesQuadraticTheorem.dimension
  canonical15Theorem ≡ 15
canonical15Dimension = refl

canonical15PressureWitnessConcreteMismatch :
  (+ (AIE.deltaSum one three))
  ≢
  (DQ.contractionEnergy
    canonical15Theorem
    (DQ.canonicalDeltaTransport
      canonical15Theorem
      canonical15Dimension
      (one , three)))
canonical15PressureWitnessConcreteMismatch eq =
  canonical15PressureToQcoreMismatch
    (trans
      eq
      (CFQT.ContractionForcesQuadraticTheorem.normalizedQuadratic
        canonical15Theorem
        (DQ.canonicalDeltaTransport
          canonical15Theorem
          canonical15Dimension
          (one , three))))
  where
    canonical15PressureToQcoreMismatch :
      (+ (AIE.deltaSum one three))
      ≢
      (QP.Q̂core
        (DQ.canonicalDeltaTransport
          canonical15Theorem
          canonical15Dimension
          (one , three)))
    canonical15PressureToQcoreMismatch ()

canonical15PairPressureTargetToQcoreMismatch :
  DQ.pairCancellationEnergy (one , three)
  ≢
  (QP.Q̂core
    (DQ.canonicalDeltaTransport
      canonical15Theorem
      canonical15Dimension
      (one , three)))
canonical15PairPressureTargetToQcoreMismatch ()

canonical15ExistingPressureWitnessObstruction :
  ExistingCancellationPressureCompatibilityObligation
    canonical15Theorem
    canonical15Dimension →
  ⊥
canonical15ExistingPressureWitnessObstruction obligation =
  canonical15PressureWitnessConcreteMismatch
    (ExistingCancellationPressureCompatibilityObligation.pressureWitness
      obligation
      (one , three))

data W9MissingIngredient : Set where
  missingPressureWitness : W9MissingIngredient
  missingCancellationToWeightedQuadraticIdentification : W9MissingIngredient
  missingWeightedTransportCompatibility : W9MissingIngredient
  missingRetargetAfterDualObstruction : W9MissingIngredient

data W9CurrentRouteClass : Set where
  existingPressureWitnessRoute : W9CurrentRouteClass
  weightedUniformReplacementRoute : W9CurrentRouteClass

data W9NextTypedRoute : Set where
  narrowTheoremFamilyWithExplicitPressureWitness : W9NextTypedRoute
  supplyPressureCompatibleTargetWithQcoreBoundary : W9NextTypedRoute

data W9RouteSelectionBoundary : Set where
  canonical15PressureDiffersFromQcore : W9RouteSelectionBoundary
  weightedUniformIdentificationDiffersFromPressure : W9RouteSelectionBoundary
  retargetMustNotClaimCanonicalQcore : W9RouteSelectionBoundary

record W9CurrentRouteClassExhaustion : Setω where
  field
    existingRouteCounterexample : DQ.DeltaPair
    weightedRouteCounterexample : DQ.WeightedInput

    existingRouteObstructed :
      ExistingCancellationPressureCompatibilityObligation
        canonical15Theorem
        canonical15Dimension →
      ⊥

    weightedUniformRouteObstructed :
      (∀ input →
        + (AIE.deltaSum (WVE.left input) (WVE.right input))
        ≡
        + (WVE.weightedQuadraticEnergy (WVE.left input))) →
      ⊥

canonical15CurrentRouteClassExhaustion :
  W9CurrentRouteClassExhaustion
canonical15CurrentRouteClassExhaustion =
  record
    { existingRouteCounterexample = one , three
    ; weightedRouteCounterexample = one , one
    ; existingRouteObstructed =
        canonical15ExistingPressureWitnessObstruction
    ; weightedUniformRouteObstructed =
        CancellationToWeightedQuadraticIdentificationObstruction.noUniformIdentification
          canonicalCancellationToWeightedQuadraticIdentificationObstruction
    }

record PressureCompatibleRetargetBoundary : Setω where
  field
    pressureTarget : DQ.DeltaPair → ℤ

    pressureTargetMatchesBridge :
      ∀ s →
        pressureTarget s
        ≡
        + (AIEB.embed-scalarCancellationPressure
            DQ.pairIntegerPressureBridge
            s)

    pressureTargetDiffersFromCanonicalQcoreAtBoundary :
      pressureTarget (one , three)
      ≢
      DQ.contractionEnergy
        canonical15Theorem
        (DQ.canonicalDeltaTransport
          canonical15Theorem
          canonical15Dimension
          (one , three))

    boundary : W9RouteSelectionBoundary

canonicalPairPressureRetargetBoundary :
  PressureCompatibleRetargetBoundary
canonicalPairPressureRetargetBoundary =
  record
    { pressureTarget = DQ.pairCancellationEnergy
    ; pressureTargetMatchesBridge = λ _ → refl
    ; pressureTargetDiffersFromCanonicalQcoreAtBoundary =
        canonical15PressureWitnessConcreteMismatch
    ; boundary = retargetMustNotClaimCanonicalQcore
    }

record PressureCompatibleTargetWithQcoreBoundaryReceipt : Setω where
  field
    selectedNextRoute : W9NextTypedRoute
    pressureCompatibleBoundary : PressureCompatibleRetargetBoundary
    boundaryInput : DQ.DeltaPair

    pressureTargetMatchesBridgeAtBoundary :
      PressureCompatibleRetargetBoundary.pressureTarget
        pressureCompatibleBoundary
        boundaryInput
      ≡
      + (AIEB.embed-scalarCancellationPressure
          DQ.pairIntegerPressureBridge
          boundaryInput)

    pressureTargetDiffersFromCanonicalQcoreAtBoundary :
      PressureCompatibleRetargetBoundary.pressureTarget
        pressureCompatibleBoundary
        boundaryInput
      ≢
      (QP.Q̂core
        (DQ.canonicalDeltaTransport
          canonical15Theorem
          canonical15Dimension
          boundaryInput))

    nonPromotionBoundary : W9RouteSelectionBoundary

canonicalPairPressureRetargetReceipt :
  PressureCompatibleTargetWithQcoreBoundaryReceipt
canonicalPairPressureRetargetReceipt =
  record
    { selectedNextRoute =
        supplyPressureCompatibleTargetWithQcoreBoundary
    ; pressureCompatibleBoundary =
        canonicalPairPressureRetargetBoundary
    ; boundaryInput = one , three
    ; pressureTargetMatchesBridgeAtBoundary = refl
    ; pressureTargetDiffersFromCanonicalQcoreAtBoundary =
        canonical15PairPressureTargetToQcoreMismatch
    ; nonPromotionBoundary =
        retargetMustNotClaimCanonicalQcore
    }

record W9RouteSelectionDiagnostic : Setω where
  field
    exhaustedRouteClasses : W9CurrentRouteClassExhaustion
    selectedNextRoute : W9NextTypedRoute
    pressureCompatibleBoundary : PressureCompatibleRetargetBoundary

    existingRouteBoundary :
      W9RouteSelectionBoundary

    weightedRouteBoundary :
      W9RouteSelectionBoundary

canonical15RouteSelectionDiagnostic :
  W9RouteSelectionDiagnostic
canonical15RouteSelectionDiagnostic =
  record
    { exhaustedRouteClasses =
        canonical15CurrentRouteClassExhaustion
    ; selectedNextRoute =
        supplyPressureCompatibleTargetWithQcoreBoundary
    ; pressureCompatibleBoundary =
        canonicalPairPressureRetargetBoundary
    ; existingRouteBoundary =
        canonical15PressureDiffersFromQcore
    ; weightedRouteBoundary =
        weightedUniformIdentificationDiffersFromPressure
    }

record CancellationPressureCompatibilityNextObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    selectedRoute : W9CompatibilityRoute
    missingIngredient : W9MissingIngredient
    existingRoute :
      ExistingCancellationPressureCompatibilityObligation theorem dim≡15 →
      DQ.CancellationPressureCompatibility theorem dim≡15
    weightedReplacementRoute :
      (replacement :
        WeightedValuationReplacementObligation theorem dim≡15) →
      DQ.WeightedValuationTransportCompatibility
        theorem
        dim≡15
        (WVE.left
          (WeightedValuationReplacementObligation.input replacement))

currentMissingIngredientDiagnostic :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  CancellationPressureCompatibilityNextObligation theorem dim≡15
currentMissingIngredientDiagnostic theorem dim≡15 =
  record
    { selectedRoute = diagnosticOnly
    ; missingIngredient = missingRetargetAfterDualObstruction
    ; existingRoute =
        ExistingCancellationPressureCompatibilityObligation.dischargesExisting
    ; weightedReplacementRoute =
        WeightedValuationReplacementObligation.weightedTransportCompatibility
    }

weightedReplacementStillNeedsCancellationIdentification :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  Setω
weightedReplacementStillNeedsCancellationIdentification theorem dim≡15 =
  WeightedValuationReplacementObligation theorem dim≡15

existingRouteStillNeedsPressureWitness :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  Setω
existingRouteStillNeedsPressureWitness theorem dim≡15 =
  ExistingCancellationPressureCompatibilityObligation theorem dim≡15
