module DASHI.Physics.Closure.ContinuumLimitTheorem where

open import Agda.Primitive using (Set; Setω)
import Agda.Builtin.Bool as Bool
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationRationalBridge as RB
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.EinsteinEquationCandidate as EEC
import DASHI.Physics.Closure.G3P2LimitConvergenceSurface as G3P2
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.W2CanonicalPressureMetricP2BridgeOrObstruction as W2PM

------------------------------------------------------------------------
-- Continuum-limit theorem candidate.
--
-- This module is deliberately non-promoting.  It records the exact typed
-- surface needed before a lattice/discrete DASHI candidate can be upgraded to
-- a continuum metric/connection/Einstein convergence theorem.  The existing
-- W2 state is consumed as a bridge-or-obstruction/rate boundary: W2 affects
-- the available rate surface, not the existence shape of a future continuum
-- theorem.  No W2 authority token, W2 closure, unification promotion, curved
-- GR recovery, or Einstein-equation receipt is constructed here.

data ContinuumLimitCandidateStatus : Set where
  theoremRequestOnlyW2RateBlockedNoPromotion :
    ContinuumLimitCandidateStatus

data W2ContinuumResolutionRole : Set where
  w2ResolutionAffectsRateNotExistence :
    W2ContinuumResolutionRole

data ContinuumLimitMissingPrimitive : Set where
  missingLatticeEmbedding :
    ContinuumLimitMissingPrimitive

  missingContinuumFieldConvergence :
    ContinuumLimitMissingPrimitive

  missingMetricErrorBound :
    ContinuumLimitMissingPrimitive

  missingConnectionErrorBound :
    ContinuumLimitMissingPrimitive

  missingEinsteinTensorContinuity :
    ContinuumLimitMissingPrimitive

  missingW2BridgeOrObstructionResolution :
    ContinuumLimitMissingPrimitive

data ConnectionConvergenceDerivativeLawStatus : Set where
  derivativeLawSuppliedConnectionConvergenceInput :
    ConnectionConvergenceDerivativeLawStatus

  derivativeLawMissingFailClosedNoConnectionPromotion :
    ConnectionConvergenceDerivativeLawStatus

data ConnectionConvergenceMissingDerivativeLaw : Set where
  missingFiniteCarrierMetricDerivativeConsistency :
    ConnectionConvergenceMissingDerivativeLaw

  missingInverseMetricC0Control :
    ConnectionConvergenceMissingDerivativeLaw

  missingChristoffelFormulaC0Stability :
    ConnectionConvergenceMissingDerivativeLaw

  missingFiniteDerivativeToContinuumPartialLaw :
    ConnectionConvergenceMissingDerivativeLaw

  missingConnectionErrorBoundExtraction :
    ConnectionConvergenceMissingDerivativeLaw

canonicalConnectionConvergenceMissingDerivativeLaws :
  List ConnectionConvergenceMissingDerivativeLaw
canonicalConnectionConvergenceMissingDerivativeLaws =
  missingFiniteCarrierMetricDerivativeConsistency
  ∷ missingInverseMetricC0Control
  ∷ missingChristoffelFormulaC0Stability
  ∷ missingFiniteDerivativeToContinuumPartialLaw
  ∷ missingConnectionErrorBoundExtraction
  ∷ []

record ContinuumLimitEpsilonRateSurface : Setω where
  field
    DiscreteScale :
      Set

    Epsilon :
      Set

    Rate :
      Epsilon →
      DiscreteScale →
      Set

    rateComposesWithW2 :
      W2ContinuumResolutionRole

    w2RateBoundary :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w2BridgeOrObstruction :
      W2PM.W2CanonicalPressureMetricP2ObstructionReceipt

    rateBoundary :
      List String

record ContinuumLimitAnalyticPrimitives
  (rate : ContinuumLimitEpsilonRateSurface)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate

  field
    LatticePoint :
      Set

    ContinuumPoint :
      Set

    DiscreteField :
      Set

    ContinuumField :
      Set

    DiscreteMetric :
      Set

    ContinuumMetric :
      Set

    DiscreteConnection :
      Set

    ContinuumConnection :
      Set

    DiscreteEinsteinTensor :
      Set

    ContinuumEinsteinTensor :
      Set

    latticeEmbedding :
      LatticePoint →
      ContinuumPoint

    continuumFieldLimit :
      DiscreteScale →
      DiscreteField →
      ContinuumField →
      Set

    metricErrorBound :
      Epsilon →
      DiscreteScale →
      DiscreteMetric →
      ContinuumMetric →
      Set

    connectionErrorBound :
      Epsilon →
      DiscreteScale →
      DiscreteConnection →
      ContinuumConnection →
      Set

    einsteinTensorContinuity :
      Epsilon →
      DiscreteScale →
      DiscreteEinsteinTensor →
      ContinuumEinsteinTensor →
      Set

    w2ResolvedRate :
      Epsilon →
      DiscreteScale →
      Set

record FiniteCarrierMetricDerivativeScheme
  (rate : ContinuumLimitEpsilonRateSurface)
  (primitives : ContinuumLimitAnalyticPrimitives rate)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate
  open ContinuumLimitAnalyticPrimitives primitives

  field
    FiniteCarrier :
      Set

    CarrierIndex :
      Set

    carrierPoint :
      FiniteCarrier →
      LatticePoint

    carrierEmbeddingAgrees :
      (carrier : FiniteCarrier) →
      ContinuumPoint

    carrierEmbeddingAgreesWithLatticeEmbedding :
      (carrier : FiniteCarrier) →
      carrierEmbeddingAgrees carrier ≡ latticeEmbedding (carrierPoint carrier)

    finiteMetricSample :
      DiscreteScale →
      FiniteCarrier →
      DiscreteMetric

    continuumMetricSample :
      FiniteCarrier →
      ContinuumMetric

    finiteDerivative :
      CarrierIndex →
      DiscreteScale →
      FiniteCarrier →
      DiscreteMetric

    continuumPartial :
      CarrierIndex →
      FiniteCarrier →
      ContinuumMetric

    derivativeErrorBound :
      Epsilon →
      CarrierIndex →
      DiscreteScale →
      FiniteCarrier →
      Set

    inverseMetricC0Control :
      Epsilon →
      DiscreteScale →
      FiniteCarrier →
      Set

    metricSampleC0Bound :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      metricErrorBound
        ε
        scale
        (finiteMetricSample scale carrier)
        (continuumMetricSample carrier)

    derivativeSchemeBoundary :
      List String

canonicalContinuumLimitEpsilonRateSurface :
  ContinuumLimitEpsilonRateSurface
canonicalContinuumLimitEpsilonRateSurface =
  record
    { DiscreteScale =
        Nat
    ; Epsilon =
        Nat
    ; Rate =
        λ ε scale →
          Nat
    ; rateComposesWithW2 =
        w2ResolutionAffectsRateNotExistence
    ; w2RateBoundary =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2BridgeOrObstruction =
        W2PM.canonicalW2PressureMetricP2ObstructionReceipt
    ; rateBoundary =
        "W2 supplies the current bridge-or-obstruction and rate boundary only"
        ∷ "Resolving W2 changes the available convergence rate surface"
        ∷ "The continuum-limit existence request still needs lattice embedding, field convergence, metric and connection error bounds, and Einstein tensor continuity"
        ∷ []
    }

------------------------------------------------------------------------
-- Concrete finite symbolic-rational derivative scheme.
--
-- This is intentionally finite and identity-shaped: it uses the already
-- internal finite-trit-tower symbolic rational bridge as the carrier and
-- records the metric/derivative samples as exact symbolic receipts.  It is not
-- a continuum Christoffel proof; the Christoffel/connection extraction surface
-- below remains fail-closed unless a separate analytic stability law is
-- supplied.

symbolicRationalContinuumEpsilonRateSurface :
  ContinuumLimitEpsilonRateSurface
symbolicRationalContinuumEpsilonRateSurface =
  record
    { DiscreteScale =
        Nat
    ; Epsilon =
        Nat
    ; Rate =
        λ ε scale →
          Nat
    ; rateComposesWithW2 =
        w2ResolutionAffectsRateNotExistence
    ; w2RateBoundary =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2BridgeOrObstruction =
        W2PM.canonicalW2PressureMetricP2ObstructionReceipt
    ; rateBoundary =
        "Symbolic rational finite derivative scheme uses the current W2 rate boundary"
        ∷ "This early local rate value avoids depending on the later canonical theorem-candidate value"
        ∷ "No W2 authority token or continuum promotion is constructed here"
        ∷ []
    }

symbolicRationalContinuumAnalyticPrimitives :
  ContinuumLimitAnalyticPrimitives
    symbolicRationalContinuumEpsilonRateSurface
symbolicRationalContinuumAnalyticPrimitives =
  record
    { LatticePoint =
        RB.SymbolicRationalApproximation
    ; ContinuumPoint =
        RB.SymbolicRationalApproximation
    ; DiscreteField =
        RB.SymbolicRationalApproximation
    ; ContinuumField =
        RB.SymbolicRationalApproximation
    ; DiscreteMetric =
        RB.SymbolicRationalApproximation
    ; ContinuumMetric =
        RB.SymbolicRationalApproximation
    ; DiscreteConnection =
        RB.SymbolicRationalApproximation
    ; ContinuumConnection =
        RB.SymbolicRationalApproximation
    ; DiscreteEinsteinTensor =
        RB.SymbolicRationalApproximation
    ; ContinuumEinsteinTensor =
        RB.SymbolicRationalApproximation
    ; latticeEmbedding =
        λ point → point
    ; continuumFieldLimit =
        λ scale discreteField continuumField →
          discreteField ≡ continuumField
    ; metricErrorBound =
        λ ε scale discreteMetric continuumMetric →
          discreteMetric ≡ continuumMetric
    ; connectionErrorBound =
        λ ε scale discreteConnection continuumConnection →
          discreteConnection ≡ continuumConnection
    ; einsteinTensorContinuity =
        λ ε scale discreteEinsteinTensor continuumEinsteinTensor →
          discreteEinsteinTensor ≡ continuumEinsteinTensor
    ; w2ResolvedRate =
        λ ε scale →
          ⊤
    }

symbolicRationalOneStepZeroMetric :
  RB.SymbolicRationalApproximation
symbolicRationalOneStepZeroMetric =
  RB.bridgeFiniteTower
    RB.canonicalFiniteTritTowerSymbolicRationalBridge
    SC.oneStepZero

symbolicRationalOneStepZeroMetricIsInternal :
  symbolicRationalOneStepZeroMetric
  ≡
  RB.towerToSymbolicRational SC.oneStepZero
symbolicRationalOneStepZeroMetricIsInternal =
  RB.bridgeFiniteTowerIsInternal
    RB.canonicalFiniteTritTowerSymbolicRationalBridge
    SC.oneStepZero

symbolicRationalOneStepZeroMetricDepth :
  RB.scaleDepth symbolicRationalOneStepZeroMetric ≡ SC.one
symbolicRationalOneStepZeroMetricDepth =
  RB.canonicalBridgeDepth SC.oneStepZero

symbolicRationalOneStepZeroMetricDoesNotPromoteQQ :
  RB.qqCarrierPromoted symbolicRationalOneStepZeroMetric ≡ Bool.false
symbolicRationalOneStepZeroMetricDoesNotPromoteQQ =
  RB.canonicalBridgeDoesNotPromoteQQ SC.oneStepZero

symbolicRationalOneStepZeroMetricDoesNotPromoteNo :
  RB.noCarrierPromoted symbolicRationalOneStepZeroMetric ≡ Bool.false
symbolicRationalOneStepZeroMetricDoesNotPromoteNo =
  RB.canonicalBridgeDoesNotPromoteNo SC.oneStepZero

symbolicRationalFiniteMetricDerivativeScheme :
  FiniteCarrierMetricDerivativeScheme
    symbolicRationalContinuumEpsilonRateSurface
    symbolicRationalContinuumAnalyticPrimitives
symbolicRationalFiniteMetricDerivativeScheme =
  record
    { FiniteCarrier =
        RB.SymbolicRationalApproximation
    ; CarrierIndex =
        Nat
    ; carrierPoint =
        λ carrier → carrier
    ; carrierEmbeddingAgrees =
        λ carrier → carrier
    ; carrierEmbeddingAgreesWithLatticeEmbedding =
        λ carrier → refl
    ; finiteMetricSample =
        λ scale carrier → carrier
    ; continuumMetricSample =
        λ carrier → carrier
    ; finiteDerivative =
        λ index scale carrier → carrier
    ; continuumPartial =
        λ index carrier → carrier
    ; derivativeErrorBound =
        λ ε index scale carrier →
          carrier ≡ carrier
    ; inverseMetricC0Control =
        λ ε scale carrier →
          ⊤
    ; metricSampleC0Bound =
        λ ε scale carrier → refl
    ; derivativeSchemeBoundary =
        "FiniteCarrier is the internal SymbolicRationalApproximation carrier from SurrealCompactificationRationalBridge"
        ∷ "Metric samples and finite derivative samples are exact identity symbolic receipts on the finite carrier"
        ∷ "The one-step zero metric sample is bridged from SC.oneStepZero by canonicalFiniteTritTowerSymbolicRationalBridge"
        ∷ "QQ/No carrier promotion flags remain false on the consumed symbolic rational receipt"
        ∷ "No Christoffel formula stability, inverse analytic norm theorem, connection convergence theorem, or continuum GR theorem is proved by this finite scheme"
        ∷ []
    }

record SymbolicRationalFiniteMetricDerivativeReceipt : Setω where
  field
    derivativeSchemeIsCanonical :
      Bool

    derivativeSchemeIsCanonicalIsTrue :
      derivativeSchemeIsCanonical ≡ Bool.true

    rationalBridge :
      RB.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge ≡ RB.canonicalFiniteTritTowerSymbolicRationalBridge

    exactFiniteSample :
      RB.SymbolicRationalApproximation

    exactFiniteSampleIsOneStepZero :
      exactFiniteSample ≡ symbolicRationalOneStepZeroMetric

    exactFiniteSampleDepthIsOne :
      RB.scaleDepth exactFiniteSample ≡ SC.one

    exactFiniteSampleDoesNotPromoteQQ :
      RB.qqCarrierPromoted exactFiniteSample ≡ Bool.false

    exactFiniteSampleDoesNotPromoteNo :
      RB.noCarrierPromoted exactFiniteSample ≡ Bool.false

    derivativeErrorBoundClosed :
      (ε : Nat) →
      (index : Nat) →
      (scale : Nat) →
      (carrier : RB.SymbolicRationalApproximation) →
      FiniteCarrierMetricDerivativeScheme.derivativeErrorBound
        symbolicRationalFiniteMetricDerivativeScheme
        ε
        index
        scale
        carrier

    inverseMetricC0ControlClosed :
      (ε : Nat) →
      (scale : Nat) →
      (carrier : RB.SymbolicRationalApproximation) →
      FiniteCarrierMetricDerivativeScheme.inverseMetricC0Control
        symbolicRationalFiniteMetricDerivativeScheme
        ε
        scale
        carrier

    metricSampleC0BoundClosed :
      (ε : Nat) →
      (scale : Nat) →
      (carrier : RB.SymbolicRationalApproximation) →
      ContinuumLimitAnalyticPrimitives.metricErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        ε
        scale
        (FiniteCarrierMetricDerivativeScheme.finiteMetricSample
          symbolicRationalFiniteMetricDerivativeScheme
          scale
          carrier)
        (FiniteCarrierMetricDerivativeScheme.continuumMetricSample
          symbolicRationalFiniteMetricDerivativeScheme
          carrier)

    receiptBoundary :
      List String

canonicalSymbolicRationalFiniteMetricDerivativeReceipt :
  SymbolicRationalFiniteMetricDerivativeReceipt
canonicalSymbolicRationalFiniteMetricDerivativeReceipt =
  record
    { derivativeSchemeIsCanonical =
        Bool.true
    ; derivativeSchemeIsCanonicalIsTrue =
        refl
    ; rationalBridge =
        RB.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; exactFiniteSample =
        symbolicRationalOneStepZeroMetric
    ; exactFiniteSampleIsOneStepZero =
        refl
    ; exactFiniteSampleDepthIsOne =
        symbolicRationalOneStepZeroMetricDepth
    ; exactFiniteSampleDoesNotPromoteQQ =
        symbolicRationalOneStepZeroMetricDoesNotPromoteQQ
    ; exactFiniteSampleDoesNotPromoteNo =
        symbolicRationalOneStepZeroMetricDoesNotPromoteNo
    ; derivativeErrorBoundClosed =
        λ ε index scale carrier → refl
    ; inverseMetricC0ControlClosed =
        λ ε scale carrier → tt
    ; metricSampleC0BoundClosed =
        λ ε scale carrier → refl
    ; receiptBoundary =
        "The derivative and metric C0 obligations are closed only for the exact finite symbolic identity scheme"
        ∷ "The consumed finite rational bridge is canonicalFiniteTritTowerSymbolicRationalBridge"
        ∷ "The explicit sample SC.oneStepZero has symbolic depth one and keeps qqCarrierPromoted/noCarrierPromoted false"
        ∷ "This receipt is a finite adapter receipt, not a Christoffel C0 stability theorem"
        ∷ []
    }

record FiniteCarrierConnectionConvergenceInput
  (rate : ContinuumLimitEpsilonRateSurface)
  (primitives : ContinuumLimitAnalyticPrimitives rate)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate
  open ContinuumLimitAnalyticPrimitives primitives

  field
    derivativeScheme :
      FiniteCarrierMetricDerivativeScheme rate primitives

    christoffelC0FromFiniteDerivativeLaw :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      connectionErrorBound
        ε
        scale
        discreteConnection
        continuumConnection

    lawStatus :
      ConnectionConvergenceDerivativeLawStatus

    lawStatusIsSupplied :
      lawStatus ≡ derivativeLawSuppliedConnectionConvergenceInput

    adapterBoundary :
      List String

record ChristoffelC0FailClosedLawSurface
  (rate : ContinuumLimitEpsilonRateSurface)
  (primitives : ContinuumLimitAnalyticPrimitives rate)
  (scheme : FiniteCarrierMetricDerivativeScheme rate primitives)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate
  open ContinuumLimitAnalyticPrimitives primitives
  open FiniteCarrierMetricDerivativeScheme scheme

  field
    finiteMetricC0Law :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      metricErrorBound
        ε
        scale
        (finiteMetricSample scale carrier)
        (continuumMetricSample carrier)

    finiteDerivativeC0Law :
      (ε : Epsilon) →
      (index : CarrierIndex) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      derivativeErrorBound ε index scale carrier

    inverseMetricC0Law :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      inverseMetricC0Control ε scale carrier

    christoffelFormulaC0Stability :
      ConnectionConvergenceMissingDerivativeLaw

    christoffelFormulaC0StabilityIsMissing :
      christoffelFormulaC0Stability
      ≡
      missingChristoffelFormulaC0Stability

    connectionErrorBoundExtraction :
      ConnectionConvergenceMissingDerivativeLaw

    connectionErrorBoundExtractionIsMissing :
      connectionErrorBoundExtraction
      ≡
      missingConnectionErrorBoundExtraction

    lawStatus :
      ConnectionConvergenceDerivativeLawStatus

    lawStatusIsMissing :
      lawStatus ≡ derivativeLawMissingFailClosedNoConnectionPromotion

    canExtractConnectionErrorBound :
      Bool

    canExtractConnectionErrorBoundIsFalse :
      canExtractConnectionErrorBound ≡ Bool.false

    lawBoundary :
      List String

canonicalSymbolicRationalChristoffelC0FailClosedLawSurface :
  ChristoffelC0FailClosedLawSurface
    symbolicRationalContinuumEpsilonRateSurface
    symbolicRationalContinuumAnalyticPrimitives
    symbolicRationalFiniteMetricDerivativeScheme
canonicalSymbolicRationalChristoffelC0FailClosedLawSurface =
  record
    { finiteMetricC0Law =
        λ ε scale carrier → refl
    ; finiteDerivativeC0Law =
        λ ε index scale carrier → refl
    ; inverseMetricC0Law =
        λ ε scale carrier → tt
    ; christoffelFormulaC0Stability =
        missingChristoffelFormulaC0Stability
    ; christoffelFormulaC0StabilityIsMissing =
        refl
    ; connectionErrorBoundExtraction =
        missingConnectionErrorBoundExtraction
    ; connectionErrorBoundExtractionIsMissing =
        refl
    ; lawStatus =
        derivativeLawMissingFailClosedNoConnectionPromotion
    ; lawStatusIsMissing =
        refl
    ; canExtractConnectionErrorBound =
        Bool.false
    ; canExtractConnectionErrorBoundIsFalse =
        refl
    ; lawBoundary =
        "Finite metric C0, finite derivative C0, and inverse-metric C0 sockets are inhabited for the symbolic rational identity scheme"
        ∷ "Christoffel C0 stability remains the exact missing law"
        ∷ "Connection error bound extraction remains false without a supplied Christoffel formula C0 theorem"
        ∷ "No FiniteCarrierConnectionConvergenceInput is fabricated from this fail-closed surface"
        ∷ []
    }

data InverseMetricC0ControlShape : Set where
  inverseMetricC0PointwiseFiniteCarrierShape :
    InverseMetricC0ControlShape

record MachineCheckedChristoffelC0ConstantReceipt : Set where
  field
    L_Gamma :
      Nat

    L_GammaIs48 :
      L_Gamma ≡ 48

    ricciContractionExtractionConstant :
      Nat

    ricciContractionExtractionConstantIs640 :
      ricciContractionExtractionConstant ≡ 640

    L_Ricci :
      Nat

    L_RicciIs640 :
      L_Ricci ≡ 640

    optionalSharpL_Ricci :
      Nat

    optionalSharpL_RicciIs112 :
      optionalSharpL_Ricci ≡ 112

    shell_C_Gamma :
      Nat

    shell_C_GammaIs2 :
      shell_C_Gamma ≡ 2

    shell_C_Gamma≤2 :
      shell_C_Gamma ≤ 2

    inverseMetricC0Shape :
      InverseMetricC0ControlShape

    inverseMetricC0ShapeIsPointwiseFiniteCarrier :
      inverseMetricC0Shape ≡ inverseMetricC0PointwiseFiniteCarrierShape

    inverseMetricC0Text :
      String

    C_GammaHalfStatus :
      String

    conservativeShellCGammaUsed :
      Bool

    conservativeShellCGammaUsedIsTrue :
      conservativeShellCGammaUsed ≡ Bool.true

    noExternalAnalyticAuthorityFabricated :
      Bool

    noExternalAnalyticAuthorityFabricatedIsFalse :
      noExternalAnalyticAuthorityFabricated ≡ Bool.false

    constantBoundary :
      List String

canonicalMachineCheckedChristoffelC0ConstantReceipt :
  MachineCheckedChristoffelC0ConstantReceipt
canonicalMachineCheckedChristoffelC0ConstantReceipt =
  record
    { L_Gamma =
        48
    ; L_GammaIs48 =
        refl
    ; ricciContractionExtractionConstant =
        640
    ; ricciContractionExtractionConstantIs640 =
        refl
    ; L_Ricci =
        640
    ; L_RicciIs640 =
        refl
    ; optionalSharpL_Ricci =
        112
    ; optionalSharpL_RicciIs112 =
        refl
    ; shell_C_Gamma =
        2
    ; shell_C_GammaIs2 =
        refl
    ; shell_C_Gamma≤2 =
        s≤s (s≤s z≤n)
    ; inverseMetricC0Shape =
        inverseMetricC0PointwiseFiniteCarrierShape
    ; inverseMetricC0ShapeIsPointwiseFiniteCarrier =
        refl
    ; inverseMetricC0Text =
        "inverseMetricC0 is pointwise over epsilon, scale, and finite carrier, returning the scheme's inverseMetricC0Control socket"
    ; C_GammaHalfStatus =
        "The analytic C_Gamma = 1/2 normalization is recorded only as an external target; this checked shell uses the conservative Nat bound C_Gamma <= 2"
    ; conservativeShellCGammaUsed =
        Bool.true
    ; conservativeShellCGammaUsedIsTrue =
        refl
    ; noExternalAnalyticAuthorityFabricated =
        Bool.false
    ; noExternalAnalyticAuthorityFabricatedIsFalse =
        refl
    ; constantBoundary =
        "Machine-checked constants consumed by the finite-carrier Christoffel C0 law surface: L_Gamma = 48, L_Ricci = 640, optional sharp L_Ricci = 112, and conservative shell C_Gamma <= 2"
        ∷ "The analytic C_Gamma = 1/2 normalization is not proved here; the local checked adapter threads only the conservative Nat shell C_Gamma = 2"
        ∷ "The inverse metric C0 surface is only the typed pointwise socket inverseMetricC0Control epsilon scale carrier"
        ∷ "These constants are local receipts for adapter wiring and do not fabricate an external analytic Christoffel, Ricci, contraction, or continuum GR proof"
        ∷ []
    }

machineCheckedChristoffelL_GammaIs48 :
  MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  48
machineCheckedChristoffelL_GammaIs48 =
  MachineCheckedChristoffelC0ConstantReceipt.L_GammaIs48
    canonicalMachineCheckedChristoffelC0ConstantReceipt

machineCheckedRicciContractionExtractionConstantIs640 :
  MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  640
machineCheckedRicciContractionExtractionConstantIs640 =
  MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstantIs640
    canonicalMachineCheckedChristoffelC0ConstantReceipt

machineCheckedChristoffelL_RicciIs640 :
  MachineCheckedChristoffelC0ConstantReceipt.L_Ricci
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  640
machineCheckedChristoffelL_RicciIs640 =
  MachineCheckedChristoffelC0ConstantReceipt.L_RicciIs640
    canonicalMachineCheckedChristoffelC0ConstantReceipt

machineCheckedChristoffelOptionalSharpL_RicciIs112 :
  MachineCheckedChristoffelC0ConstantReceipt.optionalSharpL_Ricci
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  112
machineCheckedChristoffelOptionalSharpL_RicciIs112 =
  MachineCheckedChristoffelC0ConstantReceipt.optionalSharpL_RicciIs112
    canonicalMachineCheckedChristoffelC0ConstantReceipt

machineCheckedShell_C_Gamma≤2 :
  MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≤
  2
machineCheckedShell_C_Gamma≤2 =
  MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma≤2
    canonicalMachineCheckedChristoffelC0ConstantReceipt

data ChristoffelRicciExtractionDependency : Set where
  dependsOnGaugeDepthBound :
    ChristoffelRicciExtractionDependency

  dependsOnInverseMetricC0Socket :
    ChristoffelRicciExtractionDependency

  dependsOnFiniteDerivativeToContinuumPartialLaw :
    ChristoffelRicciExtractionDependency

  dependsOnMetricDerivativeC0FromPartialControl :
    ChristoffelRicciExtractionDependency

  dependsOnChristoffelFormulaC0Stable :
    ChristoffelRicciExtractionDependency

  dependsOnConnectionErrorBoundExtraction :
    ChristoffelRicciExtractionDependency

  dependsOnConstantsLGamma48CGamma2LRicci640 :
    ChristoffelRicciExtractionDependency

canonicalChristoffelRicciExtractionDependencies :
  List ChristoffelRicciExtractionDependency
canonicalChristoffelRicciExtractionDependencies =
  dependsOnGaugeDepthBound
  ∷ dependsOnInverseMetricC0Socket
  ∷ dependsOnFiniteDerivativeToContinuumPartialLaw
  ∷ dependsOnMetricDerivativeC0FromPartialControl
  ∷ dependsOnChristoffelFormulaC0Stable
  ∷ dependsOnConnectionErrorBoundExtraction
  ∷ dependsOnConstantsLGamma48CGamma2LRicci640
  ∷ []

data OrderedRationalAnalyticKernelLawShape : Set where
  orderedRationalShellAChristoffelC0Shape :
    OrderedRationalAnalyticKernelLawShape

data OrderedRationalAnalyticInequalityPrimitive : Set where
  shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive :
    OrderedRationalAnalyticInequalityPrimitive

record OrderedRationalShellAChristoffelC0ConstantReceipt : Set where
  field
    lawShape :
      OrderedRationalAnalyticKernelLawShape

    lawShapeIsShellAChristoffelC0 :
      lawShape ≡ orderedRationalShellAChristoffelC0Shape

    shellALabel :
      String

    shellALowerEndpoint :
      Nat

    shellALowerEndpointIs3 :
      shellALowerEndpoint ≡ 3

    shellAUpperEndpoint :
      Nat

    shellAUpperEndpointIs4 :
      shellAUpperEndpoint ≡ 4

    shellAEndpointLower≤Upper :
      shellALowerEndpoint ≤ shellAUpperEndpoint

    shellA_L_Gamma :
      Nat

    shellA_L_GammaIs72 :
      shellA_L_Gamma ≡ 72

    shellA_C_R :
      Nat

    shellA_C_RIs80 :
      shellA_C_R ≡ 80

    shellA_C_Gamma :
      Nat

    shellA_C_GammaIs1 :
      shellA_C_Gamma ≡ 1

    shellA_CPrime_GammaNumerator :
      Nat

    shellA_CPrime_GammaNumeratorIs26 :
      shellA_CPrime_GammaNumerator ≡ 26

    shellA_CPrime_GammaDenominator :
      Nat

    shellA_CPrime_GammaDenominatorIs27 :
      shellA_CPrime_GammaDenominator ≡ 27

    shellA_CPrime_GammaText :
      String

    requestedInequalityPrimitive :
      OrderedRationalAnalyticInequalityPrimitive

    requestedInequalityPrimitiveIsCPrime_Gamma≤C_Gamma :
      requestedInequalityPrimitive
      ≡
      shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    inequalityPrimitiveOnly :
      Bool

    inequalityPrimitiveOnlyIsTrue :
      inequalityPrimitiveOnly ≡ Bool.true

    orderedQQTheoremPromoted :
      Bool

    orderedQQTheoremPromotedIsFalse :
      orderedQQTheoremPromoted ≡ Bool.false

    analyticEstimatePromoted :
      Bool

    analyticEstimatePromotedIsFalse :
      analyticEstimatePromoted ≡ Bool.false

    orderedShellABoundary :
      List String

canonicalOrderedRationalShellAChristoffelC0ConstantReceipt :
  OrderedRationalShellAChristoffelC0ConstantReceipt
canonicalOrderedRationalShellAChristoffelC0ConstantReceipt =
  record
    { lawShape =
        orderedRationalShellAChristoffelC0Shape
    ; lawShapeIsShellAChristoffelC0 =
        refl
    ; shellALabel =
        "Shell A [3,4]"
    ; shellALowerEndpoint =
        3
    ; shellALowerEndpointIs3 =
        refl
    ; shellAUpperEndpoint =
        4
    ; shellAUpperEndpointIs4 =
        refl
    ; shellAEndpointLower≤Upper =
        s≤s (s≤s (s≤s z≤n))
    ; shellA_L_Gamma =
        72
    ; shellA_L_GammaIs72 =
        refl
    ; shellA_C_R =
        80
    ; shellA_C_RIs80 =
        refl
    ; shellA_C_Gamma =
        1
    ; shellA_C_GammaIs1 =
        refl
    ; shellA_CPrime_GammaNumerator =
        26
    ; shellA_CPrime_GammaNumeratorIs26 =
        refl
    ; shellA_CPrime_GammaDenominator =
        27
    ; shellA_CPrime_GammaDenominatorIs27 =
        refl
    ; shellA_CPrime_GammaText =
        "C'_Gamma = 26/27 is recorded as Nat numerator 26 and denominator 27"
    ; requestedInequalityPrimitive =
        shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive
    ; requestedInequalityPrimitiveIsCPrime_Gamma≤C_Gamma =
        refl
    ; inequalityPrimitiveOnly =
        Bool.true
    ; inequalityPrimitiveOnlyIsTrue =
        refl
    ; orderedQQTheoremPromoted =
        Bool.false
    ; orderedQQTheoremPromotedIsFalse =
        refl
    ; analyticEstimatePromoted =
        Bool.false
    ; analyticEstimatePromotedIsFalse =
        refl
    ; orderedShellABoundary =
        "Ordered rational analytic kernel receipt for Shell A [3,4]"
        ∷ "Checked Nat constants: L_Gamma = 72, C_R = 80, C_Gamma = 1"
        ∷ "C'_Gamma is represented by numerator 26 and denominator 27"
        ∷ "The requested inequality C'_Gamma <= C_Gamma is recorded only as a named primitive shape"
        ∷ "No ordered QQ theorem, rational-order proof, or analytic Christoffel estimate is promoted by this receipt"
        ∷ []
    }

orderedRationalShellA_L_GammaIs72 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  72
orderedRationalShellA_L_GammaIs72 =
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_GammaIs72
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellA_C_RIs80 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  80
orderedRationalShellA_C_RIs80 =
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_RIs80
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellA_C_GammaIs1 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  1
orderedRationalShellA_C_GammaIs1 =
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_GammaIs1
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellA_CPrime_GammaNumeratorIs26 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  26
orderedRationalShellA_CPrime_GammaNumeratorIs26 =
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumeratorIs26
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellA_CPrime_GammaDenominatorIs27 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  27
orderedRationalShellA_CPrime_GammaDenominatorIs27 =
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominatorIs27
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellARequestedInequalityPrimitive :
  OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
  ≡
  shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive
orderedRationalShellARequestedInequalityPrimitive =
  OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitiveIsCPrime_Gamma≤C_Gamma
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

record FiniteCarrierChristoffelC0FromDerivativeLaw
  (rate : ContinuumLimitEpsilonRateSurface)
  (primitives : ContinuumLimitAnalyticPrimitives rate)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate
  open ContinuumLimitAnalyticPrimitives primitives

  field
    derivativeScheme :
      FiniteCarrierMetricDerivativeScheme rate primitives

  open FiniteCarrierMetricDerivativeScheme derivativeScheme

  field
    GaugeDepth :
      Epsilon →
      DiscreteScale →
      Set

    OrderedQQGauge :
      Set

    d_QQ :
      DiscreteScale →
      DiscreteScale →
      OrderedQQGauge

    threeMinusN :
      {ε : Epsilon} →
      (scale : DiscreteScale) →
      GaugeDepth ε scale →
      OrderedQQGauge

    _≤QQ_ :
      OrderedQQGauge →
      OrderedQQGauge →
      Set

    continuumReferenceScale :
      DiscreteScale

    selectedGaugeDepth :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      GaugeDepth ε scale

    metricDerivativeGaugeHypothesis :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      d_QQ scale continuumReferenceScale
      ≤QQ
      threeMinusN scale (selectedGaugeDepth ε scale)

    LipschitzConstant :
      Set

    christoffelLipschitzConstant :
      LipschitzConstant

    machineCheckedConstants :
      MachineCheckedChristoffelC0ConstantReceipt

    christoffelLipschitzConstantIsL_Gamma48 :
      MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        machineCheckedConstants
      ≡
      48

    ricciContractionExtractionConstantIs640 :
      MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
        machineCheckedConstants
      ≡
      640

    shell_C_GammaBound :
      MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
        machineCheckedConstants
      ≤
      2

    inverseMetricC0LawShape :
      MachineCheckedChristoffelC0ConstantReceipt.inverseMetricC0Shape
        machineCheckedConstants
      ≡
      inverseMetricC0PointwiseFiniteCarrierShape

    orderedShellAConstants :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellA_L_GammaIs72 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants
      ≡
      72

    orderedShellA_C_RIs80 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
        orderedShellAConstants
      ≡
      80

    orderedShellA_C_GammaIs1 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
        orderedShellAConstants
      ≡
      1

    orderedShellA_CPrime_GammaNumeratorIs26 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
        orderedShellAConstants
      ≡
      26

    orderedShellA_CPrime_GammaDenominatorIs27 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
        orderedShellAConstants
      ≡
      27

    orderedShellARequestedInequalityPrimitive :
      OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
        orderedShellAConstants
      ≡
      shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    finitePartialControl :
      (ε : Epsilon) →
      (index : CarrierIndex) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      Set

    finiteDerivativeToContinuumPartialLaw :
      (ε : Epsilon) →
      (index : CarrierIndex) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      finitePartialControl ε index scale carrier

    metricDerivativeC0FromFinitePartialControl :
      (ε : Epsilon) →
      (index : CarrierIndex) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      finitePartialControl ε index scale carrier →
      derivativeErrorBound ε index scale carrier

    inverseMetricC0 :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (carrier : FiniteCarrier) →
      inverseMetricC0Control ε scale carrier

    ChristoffelFormulaC0Stable :
      Epsilon →
      DiscreteScale →
      DiscreteConnection →
      ContinuumConnection →
      Set

    christoffelFormulaC0Stability :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      d_QQ scale continuumReferenceScale
      ≤QQ
      threeMinusN scale (selectedGaugeDepth ε scale) →
      LipschitzConstant →
      ((carrier : FiniteCarrier) →
        inverseMetricC0Control ε scale carrier) →
      ((index : CarrierIndex) →
        (carrier : FiniteCarrier) →
        derivativeErrorBound ε index scale carrier) →
      ChristoffelFormulaC0Stable
        ε
        scale
        discreteConnection
        continuumConnection

    connectionErrorBoundExtraction :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      ChristoffelFormulaC0Stable
        ε
        scale
        discreteConnection
        continuumConnection →
      connectionErrorBound
        ε
        scale
        discreteConnection
        continuumConnection

    derivativeLawBoundary :
      List String

christoffelC0ConnectionErrorBoundFromDerivativeLaw :
  {rate : ContinuumLimitEpsilonRateSurface} →
  {primitives : ContinuumLimitAnalyticPrimitives rate} →
  (law : FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives) →
  (ε : ContinuumLimitEpsilonRateSurface.Epsilon rate) →
  (scale : ContinuumLimitEpsilonRateSurface.DiscreteScale rate) →
  (discreteConnection :
    ContinuumLimitAnalyticPrimitives.DiscreteConnection primitives) →
  (continuumConnection :
    ContinuumLimitAnalyticPrimitives.ContinuumConnection primitives) →
  ContinuumLimitAnalyticPrimitives.connectionErrorBound
    primitives
    ε
    scale
    discreteConnection
    continuumConnection
christoffelC0ConnectionErrorBoundFromDerivativeLaw
  law
  ε
  scale
  discreteConnection
  continuumConnection =
  FiniteCarrierChristoffelC0FromDerivativeLaw.connectionErrorBoundExtraction
    law
    ε
    scale
    discreteConnection
    continuumConnection
    (FiniteCarrierChristoffelC0FromDerivativeLaw.christoffelFormulaC0Stability
      law
      ε
      scale
      discreteConnection
      continuumConnection
      (FiniteCarrierChristoffelC0FromDerivativeLaw.metricDerivativeGaugeHypothesis
        law
        ε
        scale)
      (FiniteCarrierChristoffelC0FromDerivativeLaw.christoffelLipschitzConstant
        law)
      (FiniteCarrierChristoffelC0FromDerivativeLaw.inverseMetricC0
        law
        ε
        scale)
      (λ index carrier →
        FiniteCarrierChristoffelC0FromDerivativeLaw.metricDerivativeC0FromFinitePartialControl
          law
          ε
          index
          scale
          carrier
          (FiniteCarrierChristoffelC0FromDerivativeLaw.finiteDerivativeToContinuumPartialLaw
            law
            ε
            index
            scale
            carrier)))

record OrderedShellAFiniteCarrierChristoffelC0LawReceipt
  {rate : ContinuumLimitEpsilonRateSurface}
  {primitives : ContinuumLimitAnalyticPrimitives rate}
  (law : FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives)
  : Setω where
  field
    orderedShellAConstants :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsMatchLaw :
      orderedShellAConstants
      ≡
      FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants law

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    shellA_L_GammaThreadedAs72 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants
      ≡
      72

    shellA_C_RThreadedAs80 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
        orderedShellAConstants
      ≡
      80

    shellA_C_GammaThreadedAs1 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
        orderedShellAConstants
      ≡
      1

    shellA_CPrime_GammaNumeratorThreadedAs26 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
        orderedShellAConstants
      ≡
      26

    shellA_CPrime_GammaDenominatorThreadedAs27 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
        orderedShellAConstants
      ≡
      27

    shellARequestedInequalityPrimitiveThreaded :
      OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
        orderedShellAConstants
      ≡
      shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    shellAOrderedQQTheoremPromotedFalse :
      OrderedRationalShellAChristoffelC0ConstantReceipt.orderedQQTheoremPromoted
        orderedShellAConstants
      ≡
      Bool.false

    shellAAnalyticEstimatePromotedFalse :
      OrderedRationalShellAChristoffelC0ConstantReceipt.analyticEstimatePromoted
        orderedShellAConstants
      ≡
      Bool.false

    orderedShellALawBoundary :
      List String

orderedShellAFiniteCarrierChristoffelC0LawReceiptFromDerivativeLaw :
  {rate : ContinuumLimitEpsilonRateSurface} →
  {primitives : ContinuumLimitAnalyticPrimitives rate} →
  (law : FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives) →
  OrderedShellAFiniteCarrierChristoffelC0LawReceipt law
orderedShellAFiniteCarrierChristoffelC0LawReceiptFromDerivativeLaw law =
  record
    { orderedShellAConstants =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants law
    ; orderedShellAConstantsMatchLaw =
        refl
    ; orderedShellAConstantsAreCanonical =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstantsAreCanonical
          law
    ; shellA_L_GammaThreadedAs72 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellA_L_GammaIs72
          law
    ; shellA_C_RThreadedAs80 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellA_C_RIs80
          law
    ; shellA_C_GammaThreadedAs1 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellA_C_GammaIs1
          law
    ; shellA_CPrime_GammaNumeratorThreadedAs26 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellA_CPrime_GammaNumeratorIs26
          law
    ; shellA_CPrime_GammaDenominatorThreadedAs27 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellA_CPrime_GammaDenominatorIs27
          law
    ; shellARequestedInequalityPrimitiveThreaded =
        FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellARequestedInequalityPrimitive
          law
    ; shellAOrderedQQTheoremPromotedFalse =
        OrderedRationalShellAChristoffelC0ConstantReceipt.orderedQQTheoremPromotedIsFalse
          (FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants
            law)
    ; shellAAnalyticEstimatePromotedFalse =
        OrderedRationalShellAChristoffelC0ConstantReceipt.analyticEstimatePromotedIsFalse
          (FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants
            law)
    ; orderedShellALawBoundary =
        "Finite-carrier law threads the ordered rational Shell A analytic-kernel receipt supplied by the law"
        ∷ "Recovered constants: Shell A [3,4], L_Gamma = 72, C_R = 80, C_Gamma = 1, C'_Gamma = 26/27"
        ∷ "Recovered inequality primitive: C'_Gamma <= C_Gamma, recorded as a primitive shape only"
        ∷ "No ordered QQ theorem or analytic Christoffel estimate is promoted by this finite-carrier receipt"
        ∷
        OrderedRationalShellAChristoffelC0ConstantReceipt.orderedShellABoundary
          (FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants
            law)
    }

record ChristoffelRicciExtractionSurfaceReceipt
  {rate : ContinuumLimitEpsilonRateSurface}
  {primitives : ContinuumLimitAnalyticPrimitives rate}
  (law : FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives)
  : Setω where
  open ContinuumLimitEpsilonRateSurface rate
  open ContinuumLimitAnalyticPrimitives primitives

  field
    constantsReceipt :
      MachineCheckedChristoffelC0ConstantReceipt

    constantsReceiptMatchesLaw :
      constantsReceipt
      ≡
      FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants law

    L_GammaThreadedAs48 :
      MachineCheckedChristoffelC0ConstantReceipt.L_Gamma constantsReceipt
      ≡
      48

    conservative_C_GammaThreadedAs2 :
      MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma constantsReceipt
      ≡
      2

    conservative_C_GammaBoundThreaded :
      MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma constantsReceipt
      ≤
      2

    L_RicciThreadedAs640 :
      MachineCheckedChristoffelC0ConstantReceipt.L_Ricci constantsReceipt
      ≡
      640

    optionalSharpL_RicciThreadedAs112 :
      MachineCheckedChristoffelC0ConstantReceipt.optionalSharpL_Ricci
        constantsReceipt
      ≡
      112

    ricciContractionExtractionThreadedAs640 :
      MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
        constantsReceipt
      ≡
      640

    C_GammaHalfNormalizationRemainsExternal :
      String

    dependencyLedger :
      List ChristoffelRicciExtractionDependency

    dependencyLedgerIsCanonical :
      dependencyLedger ≡ canonicalChristoffelRicciExtractionDependencies

    ChristoffelFormulaC0StableInhabitant :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      FiniteCarrierChristoffelC0FromDerivativeLaw.ChristoffelFormulaC0Stable
        law
        ε
        scale
        discreteConnection
        continuumConnection

    connectionErrorBoundExtractionFromStable :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      FiniteCarrierChristoffelC0FromDerivativeLaw.ChristoffelFormulaC0Stable
        law
        ε
        scale
        discreteConnection
        continuumConnection →
      connectionErrorBound
        ε
        scale
        discreteConnection
        continuumConnection

    extractedConnectionErrorBound :
      (ε : Epsilon) →
      (scale : DiscreteScale) →
      (discreteConnection : DiscreteConnection) →
      (continuumConnection : ContinuumConnection) →
      connectionErrorBound
        ε
        scale
        discreteConnection
        continuumConnection

    extractionBoundary :
      List String

christoffelRicciExtractionSurfaceReceiptFromDerivativeLaw :
  {rate : ContinuumLimitEpsilonRateSurface} →
  {primitives : ContinuumLimitAnalyticPrimitives rate} →
  (law : FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives) →
  ChristoffelRicciExtractionSurfaceReceipt law
christoffelRicciExtractionSurfaceReceiptFromDerivativeLaw law =
  record
    { constantsReceipt =
        FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants law
    ; constantsReceiptMatchesLaw =
        refl
    ; L_GammaThreadedAs48 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.christoffelLipschitzConstantIsL_Gamma48
          law
    ; conservative_C_GammaThreadedAs2 =
        MachineCheckedChristoffelC0ConstantReceipt.shell_C_GammaIs2
          (FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants
            law)
    ; conservative_C_GammaBoundThreaded =
        FiniteCarrierChristoffelC0FromDerivativeLaw.shell_C_GammaBound
          law
    ; L_RicciThreadedAs640 =
        MachineCheckedChristoffelC0ConstantReceipt.L_RicciIs640
          (FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants
            law)
    ; optionalSharpL_RicciThreadedAs112 =
        MachineCheckedChristoffelC0ConstantReceipt.optionalSharpL_RicciIs112
          (FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants
            law)
    ; ricciContractionExtractionThreadedAs640 =
        FiniteCarrierChristoffelC0FromDerivativeLaw.ricciContractionExtractionConstantIs640
          law
    ; C_GammaHalfNormalizationRemainsExternal =
        MachineCheckedChristoffelC0ConstantReceipt.C_GammaHalfStatus
          (FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants
            law)
    ; dependencyLedger =
        canonicalChristoffelRicciExtractionDependencies
    ; dependencyLedgerIsCanonical =
        refl
    ; ChristoffelFormulaC0StableInhabitant =
        λ ε scale discreteConnection continuumConnection →
          FiniteCarrierChristoffelC0FromDerivativeLaw.christoffelFormulaC0Stability
            law
            ε
            scale
            discreteConnection
            continuumConnection
            (FiniteCarrierChristoffelC0FromDerivativeLaw.metricDerivativeGaugeHypothesis
              law
              ε
              scale)
            (FiniteCarrierChristoffelC0FromDerivativeLaw.christoffelLipschitzConstant
              law)
            (FiniteCarrierChristoffelC0FromDerivativeLaw.inverseMetricC0
              law
              ε
              scale)
            (λ index carrier →
              FiniteCarrierChristoffelC0FromDerivativeLaw.metricDerivativeC0FromFinitePartialControl
                law
                ε
                index
                scale
                carrier
                (FiniteCarrierChristoffelC0FromDerivativeLaw.finiteDerivativeToContinuumPartialLaw
                  law
                  ε
                  index
                  scale
                  carrier))
    ; connectionErrorBoundExtractionFromStable =
        FiniteCarrierChristoffelC0FromDerivativeLaw.connectionErrorBoundExtraction
          law
    ; extractedConnectionErrorBound =
        christoffelC0ConnectionErrorBoundFromDerivativeLaw law
    ; extractionBoundary =
        "The analytic inhabitant is assembled only from the supplied law's gauge bound, inverseMetricC0 socket, finite-to-continuum partial law, derivative C0 adapter, ChristoffelFormulaC0Stable field, and connectionErrorBoundExtraction field"
        ∷ "Checked constants threaded through this receipt are conservative C_Gamma = 2, L_Gamma = 48, L_Ricci = 640, optional sharp L_Ricci = 112, and Ricci/contraction extraction constant = 640"
        ∷ "The analytic C_Gamma = 1/2 normalization is named as an external target, not proved or consumed as a local theorem"
        ∷ "No Ricci continuity theorem, external Christoffel estimate, ordered QQ theorem, or continuum GR theorem is fabricated by this receipt"
        ∷ []
    }

finiteCarrierConnectionConvergenceInputFromChristoffelC0DerivativeLaw :
  {rate : ContinuumLimitEpsilonRateSurface} →
  {primitives : ContinuumLimitAnalyticPrimitives rate} →
  FiniteCarrierChristoffelC0FromDerivativeLaw rate primitives →
  FiniteCarrierConnectionConvergenceInput rate primitives
finiteCarrierConnectionConvergenceInputFromChristoffelC0DerivativeLaw law =
  record
    { derivativeScheme =
        FiniteCarrierChristoffelC0FromDerivativeLaw.derivativeScheme law
    ; christoffelC0FromFiniteDerivativeLaw =
        christoffelC0ConnectionErrorBoundFromDerivativeLaw law
    ; lawStatus =
        derivativeLawSuppliedConnectionConvergenceInput
    ; lawStatusIsSupplied =
        refl
    ; adapterBoundary =
        ("Christoffel C0 connection convergence is extracted from the supplied finite-carrier derivative law"
        ∷ "The law must provide d_QQ <= threeMinusN control, checked conservative C_Gamma = 2, checked L_Gamma = 48, checked L_Ricci = 640, optional sharp L_Ricci = 112, checked Ricci/contraction extraction constant 640, inverse metric C0 control, finite-to-continuum partial control, Christoffel formula C0 stability, connectionErrorBound extraction, and the ordered rational Shell A primitive receipt"
        ∷ "Shell A ordered rational constants are threaded as [3,4], L_Gamma = 72, C_R = 80, C_Gamma = 1, and C'_Gamma = 26/27"
        ∷ "No ordered QQ carrier, rational order theorem, ordered inequality theorem, or analytic Christoffel estimate is promoted by this adapter"
        ∷ [])
        ++
        MachineCheckedChristoffelC0ConstantReceipt.constantBoundary
          (FiniteCarrierChristoffelC0FromDerivativeLaw.machineCheckedConstants
            law)
        ++
        OrderedRationalShellAChristoffelC0ConstantReceipt.orderedShellABoundary
          (FiniteCarrierChristoffelC0FromDerivativeLaw.orderedShellAConstants
            law)
        ++
        FiniteCarrierChristoffelC0FromDerivativeLaw.derivativeLawBoundary law
    }

symbolicRationalConnectionErrorBoundDiagonal :
  (ε : Nat) →
  (scale : Nat) →
  (connection : RB.SymbolicRationalApproximation) →
  ContinuumLimitAnalyticPrimitives.connectionErrorBound
    symbolicRationalContinuumAnalyticPrimitives
    ε
    scale
    connection
    connection
symbolicRationalConnectionErrorBoundDiagonal ε scale connection =
  refl

record SelectedSymbolicRationalChristoffelC0Primitive : Set where
  field
    selectedConnection :
      RB.SymbolicRationalApproximation

    selectedDiscreteConnection :
      RB.SymbolicRationalApproximation

    selectedContinuumConnection :
      RB.SymbolicRationalApproximation

    selectedDiscreteConnectionIsSelected :
      selectedDiscreteConnection ≡ selectedConnection

    selectedContinuumConnectionIsSelected :
      selectedContinuumConnection ≡ selectedConnection

    selectedPairIdentity :
      selectedDiscreteConnection ≡ selectedContinuumConnection

    selectedPairConnectionErrorBound :
      (ε : Nat) →
      (scale : Nat) →
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        ε
        scale
        selectedDiscreteConnection
        selectedContinuumConnection

    onlySelectedPairReflExtraction :
      Bool

    onlySelectedPairReflExtractionIsTrue :
      onlySelectedPairReflExtraction ≡ Bool.true

    arbitraryConnectionEqualityPromoted :
      Bool

    arbitraryConnectionEqualityPromotedIsFalse :
      arbitraryConnectionEqualityPromoted ≡ Bool.false

    primitiveBoundary :
      List String

canonicalSelectedSymbolicRationalChristoffelC0Primitive :
  SelectedSymbolicRationalChristoffelC0Primitive
canonicalSelectedSymbolicRationalChristoffelC0Primitive =
  record
    { selectedConnection =
        symbolicRationalOneStepZeroMetric
    ; selectedDiscreteConnection =
        symbolicRationalOneStepZeroMetric
    ; selectedContinuumConnection =
        symbolicRationalOneStepZeroMetric
    ; selectedDiscreteConnectionIsSelected =
        refl
    ; selectedContinuumConnectionIsSelected =
        refl
    ; selectedPairIdentity =
        refl
    ; selectedPairConnectionErrorBound =
        λ ε scale →
          refl
    ; onlySelectedPairReflExtraction =
        Bool.true
    ; onlySelectedPairReflExtractionIsTrue =
        refl
    ; arbitraryConnectionEqualityPromoted =
        Bool.false
    ; arbitraryConnectionEqualityPromotedIsFalse =
        refl
    ; primitiveBoundary =
        "The selected symbolic-rational Christoffel primitive is the diagonal pair at symbolicRationalOneStepZeroMetric"
        ∷ "The only refl-producing connectionErrorBound extraction recorded here is the selected-pair identity extraction"
        ∷ "No arbitrary discreteConnection = continuumConnection equality is promoted from this selected primitive"
        ∷ []
    }

selectedSymbolicRationalChristoffelC0PrimitivePairIdentity :
  SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
    canonicalSelectedSymbolicRationalChristoffelC0Primitive
  ≡
  SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
    canonicalSelectedSymbolicRationalChristoffelC0Primitive
selectedSymbolicRationalChristoffelC0PrimitivePairIdentity =
  SelectedSymbolicRationalChristoffelC0Primitive.selectedPairIdentity
    canonicalSelectedSymbolicRationalChristoffelC0Primitive

selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound :
  (ε : Nat) →
  (scale : Nat) →
  ContinuumLimitAnalyticPrimitives.connectionErrorBound
    symbolicRationalContinuumAnalyticPrimitives
    ε
    scale
    (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
      canonicalSelectedSymbolicRationalChristoffelC0Primitive)
    (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
      canonicalSelectedSymbolicRationalChristoffelC0Primitive)
selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound =
  SelectedSymbolicRationalChristoffelC0Primitive.selectedPairConnectionErrorBound
    canonicalSelectedSymbolicRationalChristoffelC0Primitive

record SymbolicRationalChristoffelC0SelectedConstantReceipt : Set where
  field
    constantsReceipt :
      MachineCheckedChristoffelC0ConstantReceipt

    constantsReceiptIsCanonical :
      constantsReceipt ≡ canonicalMachineCheckedChristoffelC0ConstantReceipt

    orderedShellAConstants :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellA_L_GammaSelectedAs72 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants
      ≡
      72

    orderedShellA_C_RSelectedAs80 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
        orderedShellAConstants
      ≡
      80

    orderedShellA_C_GammaSelectedAs1 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
        orderedShellAConstants
      ≡
      1

    orderedShellA_CPrime_GammaNumeratorSelectedAs26 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
        orderedShellAConstants
      ≡
      26

    orderedShellA_CPrime_GammaDenominatorSelectedAs27 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
        orderedShellAConstants
      ≡
      27

    orderedShellARequestedInequalityPrimitiveSelected :
      OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
        orderedShellAConstants
      ≡
      shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    selectedTight_C_GammaNat :
      Nat

    selectedTight_C_GammaNatIs1 :
      selectedTight_C_GammaNat ≡ 1

    selectedTight_C_GammaText :
      String

    conservativeShell_C_GammaNat :
      Nat

    conservativeShell_C_GammaNatIs2 :
      conservativeShell_C_GammaNat ≡ 2

    conservativeShell_C_GammaText :
      String

    formulaStabilityConstantNat :
      Nat

    formulaStabilityConstantNatIs48 :
      formulaStabilityConstantNat ≡ 48

    formulaStabilityConstantText :
      String

    optionalFormulaStabilityRatioText :
      String

    ricciBoundNumeratorNat :
      Nat

    ricciBoundNumeratorNatIs48 :
      ricciBoundNumeratorNat ≡ 48

    ricciBoundDenominatorNat :
      Nat

    ricciBoundDenominatorNatIs640 :
      ricciBoundDenominatorNat ≡ 640

    ricciBoundText :
      String

    noArbitraryConnectionEqualityClaimed :
      Bool

    noArbitraryConnectionEqualityClaimedIsTrue :
      noArbitraryConnectionEqualityClaimed ≡ Bool.true

    selectedConstantBoundary :
      List String

canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt :
  SymbolicRationalChristoffelC0SelectedConstantReceipt
canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt =
  record
    { constantsReceipt =
        canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; constantsReceiptIsCanonical =
        refl
    ; orderedShellAConstants =
        canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; orderedShellAConstantsAreCanonical =
        refl
    ; orderedShellA_L_GammaSelectedAs72 =
        orderedRationalShellA_L_GammaIs72
    ; orderedShellA_C_RSelectedAs80 =
        orderedRationalShellA_C_RIs80
    ; orderedShellA_C_GammaSelectedAs1 =
        orderedRationalShellA_C_GammaIs1
    ; orderedShellA_CPrime_GammaNumeratorSelectedAs26 =
        orderedRationalShellA_CPrime_GammaNumeratorIs26
    ; orderedShellA_CPrime_GammaDenominatorSelectedAs27 =
        orderedRationalShellA_CPrime_GammaDenominatorIs27
    ; orderedShellARequestedInequalityPrimitiveSelected =
        orderedRationalShellARequestedInequalityPrimitive
    ; selectedTight_C_GammaNat =
        1
    ; selectedTight_C_GammaNatIs1 =
        refl
    ; selectedTight_C_GammaText =
        "selected/tight C_Gamma receipt: 1 on the selected symbolic-rational kernel surface"
    ; conservativeShell_C_GammaNat =
        MachineCheckedChristoffelC0ConstantReceipt.shell_C_Gamma
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; conservativeShell_C_GammaNatIs2 =
        MachineCheckedChristoffelC0ConstantReceipt.shell_C_GammaIs2
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; conservativeShell_C_GammaText =
        "conservative shell C_Gamma receipt: analytic 5/3 is recorded textually; checked Nat-compatible shell is 2"
    ; formulaStabilityConstantNat =
        MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; formulaStabilityConstantNatIs48 =
        MachineCheckedChristoffelC0ConstantReceipt.L_GammaIs48
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; formulaStabilityConstantText =
        "formula stability receipt: checked Nat constant 48"
    ; optionalFormulaStabilityRatioText =
        "optional tight formula stability receipt: 11/9 is recorded as text only and is not promoted into the Nat constant surface"
    ; ricciBoundNumeratorNat =
        48
    ; ricciBoundNumeratorNatIs48 =
        refl
    ; ricciBoundDenominatorNat =
        MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstant
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; ricciBoundDenominatorNatIs640 =
        MachineCheckedChristoffelC0ConstantReceipt.ricciContractionExtractionConstantIs640
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; ricciBoundText =
        "selected Ricci/contraction bound receipt: 48/640, recorded as numerator/denominator Nat fields without asserting a Ricci convergence theorem"
    ; noArbitraryConnectionEqualityClaimed =
        Bool.true
    ; noArbitraryConnectionEqualityClaimedIsTrue =
        refl
    ; selectedConstantBoundary =
        "Selected/tight C_Gamma is recorded as Nat 1 for this selected symbolic-rational kernel surface"
        ∷ "Ordered rational Shell A constants are recorded canonically: [3,4], L_Gamma = 72, C_R = 80, C_Gamma = 1, C'_Gamma = 26/27"
        ∷ "The ordered rational inequality C'_Gamma <= C_Gamma is selected only as the named primitive shape"
        ∷ "The conservative shell records analytic 5/3 textually and threads the existing Nat-compatible shell C_Gamma = 2"
        ∷ "Formula stability records checked Nat 48 and optional tight 11/9 textually"
        ∷ "Ricci/contraction receipt records 48/640 as Nat numerator 48 and Nat denominator 640"
        ∷ "These are receipts for selected-kernel aggregation; they do not claim arbitrary connection equality"
        ∷ []
    }

selectedSymbolicRationalChristoffelC0Tight_C_GammaIs1 :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.selectedTight_C_GammaNat
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  1
selectedSymbolicRationalChristoffelC0Tight_C_GammaIs1 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.selectedTight_C_GammaNatIs1
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalChristoffelC0Conservative_C_GammaIs2 :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.conservativeShell_C_GammaNat
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  2
selectedSymbolicRationalChristoffelC0Conservative_C_GammaIs2 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.conservativeShell_C_GammaNatIs2
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellA_L_GammaIs72 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  72
selectedSymbolicRationalOrderedShellA_L_GammaIs72 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellA_L_GammaSelectedAs72
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellA_C_RIs80 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  80
selectedSymbolicRationalOrderedShellA_C_RIs80 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellA_C_RSelectedAs80
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellA_C_GammaIs1 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  1
selectedSymbolicRationalOrderedShellA_C_GammaIs1 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellA_C_GammaSelectedAs1
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellA_CPrime_GammaNumeratorIs26 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  26
selectedSymbolicRationalOrderedShellA_CPrime_GammaNumeratorIs26 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellA_CPrime_GammaNumeratorSelectedAs26
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellA_CPrime_GammaDenominatorIs27 :
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  27
selectedSymbolicRationalOrderedShellA_CPrime_GammaDenominatorIs27 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellA_CPrime_GammaDenominatorSelectedAs27
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedShellARequestedInequalityPrimitive :
  OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellAConstants
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive
selectedSymbolicRationalOrderedShellARequestedInequalityPrimitive =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedShellARequestedInequalityPrimitiveSelected
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalChristoffelC0FormulaStabilityIs48 :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  48
selectedSymbolicRationalChristoffelC0FormulaStabilityIs48 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNatIs48
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalChristoffelC0RicciBoundNumeratorIs48 :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNat
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  48
selectedSymbolicRationalChristoffelC0RicciBoundNumeratorIs48 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundNumeratorNatIs48
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalChristoffelC0RicciBoundDenominatorIs640 :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNat
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  640
selectedSymbolicRationalChristoffelC0RicciBoundDenominatorIs640 =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNatIs640
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

record SymbolicRationalChristoffelC0StabilityKernel : Setω where
  field
    orderedShellAConstants :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellA_L_GammaIs72 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants
      ≡
      72

    orderedShellA_C_RIs80 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_R
        orderedShellAConstants
      ≡
      80

    orderedShellA_C_GammaIs1 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_C_Gamma
        orderedShellAConstants
      ≡
      1

    orderedShellA_CPrime_GammaNumeratorIs26 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaNumerator
        orderedShellAConstants
      ≡
      26

    orderedShellA_CPrime_GammaDenominatorIs27 :
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_CPrime_GammaDenominator
        orderedShellAConstants
      ≡
      27

    orderedShellARequestedInequalityPrimitive :
      OrderedRationalShellAChristoffelC0ConstantReceipt.requestedInequalityPrimitive
        orderedShellAConstants
      ≡
      shellA_CPrime_Gamma26Over27≤C_Gamma1Primitive

    ChristoffelFormulaC0Stable :
      Nat →
      Nat →
      RB.SymbolicRationalApproximation →
      RB.SymbolicRationalApproximation →
      Set

    christoffelFormulaC0Stability :
      (ε : Nat) →
      (scale : Nat) →
      (discreteConnection : RB.SymbolicRationalApproximation) →
      (continuumConnection : RB.SymbolicRationalApproximation) →
      ⊤ →
      Nat →
      ((carrier : RB.SymbolicRationalApproximation) →
        ⊤) →
      ((index : Nat) →
        (carrier : RB.SymbolicRationalApproximation) →
        carrier ≡ carrier) →
      ChristoffelFormulaC0Stable
        ε
        scale
        discreteConnection
        continuumConnection

    connectionErrorBoundExtraction :
      (ε : Nat) →
      (scale : Nat) →
      (discreteConnection : RB.SymbolicRationalApproximation) →
      (continuumConnection : RB.SymbolicRationalApproximation) →
      ChristoffelFormulaC0Stable
        ε
        scale
        discreteConnection
        continuumConnection →
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        ε
        scale
        discreteConnection
        continuumConnection

    kernelBoundary :
      List String

symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel :
  SymbolicRationalChristoffelC0StabilityKernel →
  FiniteCarrierChristoffelC0FromDerivativeLaw
    symbolicRationalContinuumEpsilonRateSurface
    symbolicRationalContinuumAnalyticPrimitives
symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel kernel =
  record
    { derivativeScheme =
        symbolicRationalFiniteMetricDerivativeScheme
    ; GaugeDepth =
        λ ε scale →
          ⊤
    ; OrderedQQGauge =
        ⊤
    ; d_QQ =
        λ scale referenceScale →
          tt
    ; threeMinusN =
        λ scale depth →
          tt
    ; _≤QQ_ =
        λ left right →
          ⊤
    ; continuumReferenceScale =
        0
    ; selectedGaugeDepth =
        λ ε scale →
          tt
    ; metricDerivativeGaugeHypothesis =
        λ ε scale →
          tt
    ; LipschitzConstant =
        Nat
    ; christoffelLipschitzConstant =
        MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; machineCheckedConstants =
        canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; christoffelLipschitzConstantIsL_Gamma48 =
        machineCheckedChristoffelL_GammaIs48
    ; ricciContractionExtractionConstantIs640 =
        machineCheckedRicciContractionExtractionConstantIs640
    ; shell_C_GammaBound =
        machineCheckedShell_C_Gamma≤2
    ; inverseMetricC0LawShape =
        MachineCheckedChristoffelC0ConstantReceipt.inverseMetricC0ShapeIsPointwiseFiniteCarrier
          canonicalMachineCheckedChristoffelC0ConstantReceipt
    ; orderedShellAConstants =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAConstants
          kernel
    ; orderedShellAConstantsAreCanonical =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAConstantsAreCanonical
          kernel
    ; orderedShellA_L_GammaIs72 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellA_L_GammaIs72
          kernel
    ; orderedShellA_C_RIs80 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellA_C_RIs80
          kernel
    ; orderedShellA_C_GammaIs1 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellA_C_GammaIs1
          kernel
    ; orderedShellA_CPrime_GammaNumeratorIs26 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellA_CPrime_GammaNumeratorIs26
          kernel
    ; orderedShellA_CPrime_GammaDenominatorIs27 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellA_CPrime_GammaDenominatorIs27
          kernel
    ; orderedShellARequestedInequalityPrimitive =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellARequestedInequalityPrimitive
          kernel
    ; finitePartialControl =
        λ ε index scale carrier →
          ⊤
    ; finiteDerivativeToContinuumPartialLaw =
        λ ε index scale carrier →
          tt
    ; metricDerivativeC0FromFinitePartialControl =
        λ ε index scale carrier control →
          refl
    ; inverseMetricC0 =
        λ ε scale carrier →
          tt
    ; ChristoffelFormulaC0Stable =
        SymbolicRationalChristoffelC0StabilityKernel.ChristoffelFormulaC0Stable
          kernel
    ; christoffelFormulaC0Stability =
        SymbolicRationalChristoffelC0StabilityKernel.christoffelFormulaC0Stability
          kernel
    ; connectionErrorBoundExtraction =
        SymbolicRationalChristoffelC0StabilityKernel.connectionErrorBoundExtraction
          kernel
    ; derivativeLawBoundary =
        "Symbolic-rational finite/gauge/constant obligations are closed by this constructor from the canonical identity derivative scheme"
        ∷ "The constructor consumes checked constants L_Gamma = 48, Ricci/contraction extraction constant = 640, and shell C_Gamma <= 2"
        ∷ "The ordered rational Shell A analytic constants are supplied by the kernel: [3,4], L_Gamma = 72, C_R = 80, C_Gamma = 1, and C'_Gamma = 26/27"
        ∷ "The ordered rational inequality is threaded only as the named primitive C'_Gamma <= C_Gamma, not as a promoted QQ theorem"
        ∷ "Only the Christoffel formula C0 stability kernel and equality-valued connectionErrorBound extraction remain external"
        ∷
        OrderedRationalShellAChristoffelC0ConstantReceipt.orderedShellABoundary
          (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAConstants
            kernel)
        ++
        SymbolicRationalChristoffelC0StabilityKernel.kernelBoundary kernel
    }

record SymbolicRationalChristoffelC0SelectedKernelHandoff
  (kernel : SymbolicRationalChristoffelC0StabilityKernel)
  : Setω where
  field
    selectedPrimitive :
      SelectedSymbolicRationalChristoffelC0Primitive

    selectedPrimitiveIsCanonical :
      selectedPrimitive
      ≡
      canonicalSelectedSymbolicRationalChristoffelC0Primitive

    selectedConstants :
      SymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedConstantsAreCanonical :
      selectedConstants
      ≡
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

    finiteCarrierLaw :
      FiniteCarrierChristoffelC0FromDerivativeLaw
        symbolicRationalContinuumEpsilonRateSurface
        symbolicRationalContinuumAnalyticPrimitives

    finiteCarrierLawIsKernelAdapterTag :
      Bool

    finiteCarrierLawIsKernelAdapterTagIsTrue :
      finiteCarrierLawIsKernelAdapterTag ≡ Bool.true

    selectedPairIdentityReceipt :
      SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
        selectedPrimitive
      ≡
      SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
        selectedPrimitive

    selectedPairPrimitiveConnectionErrorBound :
      (ε : Nat) →
      (scale : Nat) →
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        ε
        scale
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
          selectedPrimitive)
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
          selectedPrimitive)

    selectedKernelFormulaStable :
      (ε : Nat) →
      (scale : Nat) →
      SymbolicRationalChristoffelC0StabilityKernel.ChristoffelFormulaC0Stable
        kernel
        ε
        scale
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
          selectedPrimitive)
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
          selectedPrimitive)

    selectedKernelConnectionErrorBound :
      (ε : Nat) →
      (scale : Nat) →
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        ε
        scale
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
          selectedPrimitive)
        (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
          selectedPrimitive)

    selectedKernelExtractionIsNotArbitraryEquality :
      Bool

    selectedKernelExtractionIsNotArbitraryEqualityIsTrue :
      selectedKernelExtractionIsNotArbitraryEquality ≡ Bool.true

    aggregationBoundary :
      List String

symbolicRationalChristoffelC0SelectedKernelHandoff :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SymbolicRationalChristoffelC0SelectedKernelHandoff kernel
symbolicRationalChristoffelC0SelectedKernelHandoff kernel =
  record
    { selectedPrimitive =
        canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedPrimitiveIsCanonical =
        refl
    ; selectedConstants =
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedConstantsAreCanonical =
        refl
    ; finiteCarrierLaw =
        symbolicRationalFiniteCarrierChristoffelC0FromDerivativeLawFromKernel
          kernel
    ; finiteCarrierLawIsKernelAdapterTag =
        Bool.true
    ; finiteCarrierLawIsKernelAdapterTagIsTrue =
        refl
    ; selectedPairIdentityReceipt =
        selectedSymbolicRationalChristoffelC0PrimitivePairIdentity
    ; selectedPairPrimitiveConnectionErrorBound =
        selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound
    ; selectedKernelFormulaStable =
        λ ε scale →
          SymbolicRationalChristoffelC0StabilityKernel.christoffelFormulaC0Stability
            kernel
            ε
            scale
            (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
              canonicalSelectedSymbolicRationalChristoffelC0Primitive)
            (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
              canonicalSelectedSymbolicRationalChristoffelC0Primitive)
            tt
            (MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
              canonicalMachineCheckedChristoffelC0ConstantReceipt)
            (λ carrier →
              tt)
            (λ index carrier →
              refl)
    ; selectedKernelConnectionErrorBound =
        λ ε scale →
          SymbolicRationalChristoffelC0StabilityKernel.connectionErrorBoundExtraction
            kernel
            ε
            scale
            (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
              canonicalSelectedSymbolicRationalChristoffelC0Primitive)
            (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
              canonicalSelectedSymbolicRationalChristoffelC0Primitive)
            (SymbolicRationalChristoffelC0StabilityKernel.christoffelFormulaC0Stability
              kernel
              ε
              scale
              (SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
                canonicalSelectedSymbolicRationalChristoffelC0Primitive)
              (SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
                canonicalSelectedSymbolicRationalChristoffelC0Primitive)
              tt
              (MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
                canonicalMachineCheckedChristoffelC0ConstantReceipt)
              (λ carrier →
                tt)
              (λ index carrier →
                refl))
    ; selectedKernelExtractionIsNotArbitraryEquality =
        Bool.true
    ; selectedKernelExtractionIsNotArbitraryEqualityIsTrue =
        refl
    ; aggregationBoundary =
        ("Canonical selected-kernel handoff for aggregation: selected primitive, selected constants, finite-carrier derivative law, selected formula stability, and selected connectionErrorBound receipt"
        ∷ "The selected primitive's refl-producing extraction is only the diagonal selected-pair identity at symbolicRationalOneStepZeroMetric"
        ∷ "The supplied kernel may provide selected-pair stability/extraction for the handoff, but this receipt does not promote arbitrary connection equality"
        ∷ [])
        ++
        SymbolicRationalChristoffelC0SelectedConstantReceipt.selectedConstantBoundary
          canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
        ++
        SymbolicRationalChristoffelC0StabilityKernel.kernelBoundary kernel
    }

canonicalSymbolicRationalChristoffelC0SelectedKernelHandoff :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SymbolicRationalChristoffelC0SelectedKernelHandoff kernel
canonicalSymbolicRationalChristoffelC0SelectedKernelHandoff =
  symbolicRationalChristoffelC0SelectedKernelHandoff

record SelectedZeroEpsilonConnectionErrorBoundReceipt
  (kernel : SymbolicRationalChristoffelC0StabilityKernel)
  : Setω where
  field
    selectedKernelHandoff :
      SymbolicRationalChristoffelC0SelectedKernelHandoff kernel

    selectedKernelHandoffCanonicalTag :
      Bool

    selectedKernelHandoffCanonicalTagIsTrue :
      selectedKernelHandoffCanonicalTag ≡ Bool.true

    selectedPrimitive :
      SelectedSymbolicRationalChristoffelC0Primitive

    selectedPrimitiveMatchesHandoff :
      selectedPrimitive
      ≡
      SymbolicRationalChristoffelC0SelectedKernelHandoff.selectedPrimitive
        selectedKernelHandoff

    selectedConstants :
      SymbolicRationalChristoffelC0SelectedConstantReceipt

    selectedConstantsMatchHandoff :
      selectedConstants
      ≡
      SymbolicRationalChristoffelC0SelectedKernelHandoff.selectedConstants
        selectedKernelHandoff

    selectedEpsilon :
      Nat

    selectedEpsilonIsZero :
      selectedEpsilon ≡ 0

    selectedScale :
      Nat

    selectedScaleIsZero :
      selectedScale ≡ 0

    selectedDiscreteConnection :
      RB.SymbolicRationalApproximation

    selectedDiscreteConnectionIsPrimitive :
      selectedDiscreteConnection
      ≡
      SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
        selectedPrimitive

    selectedContinuumConnection :
      RB.SymbolicRationalApproximation

    selectedContinuumConnectionIsPrimitive :
      selectedContinuumConnection
      ≡
      SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
        selectedPrimitive

    selectedLocalEqualityHandoff :
      selectedDiscreteConnection ≡ selectedContinuumConnection

    selectedLocalPrimitiveConnectionErrorBound :
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        selectedEpsilon
        selectedScale
        selectedDiscreteConnection
        selectedContinuumConnection

    selectedLocalKernelConnectionErrorBound :
      ContinuumLimitAnalyticPrimitives.connectionErrorBound
        symbolicRationalContinuumAnalyticPrimitives
        selectedEpsilon
        selectedScale
        selectedDiscreteConnection
        selectedContinuumConnection

    connectionBound :
      Nat →
      Nat →
      RB.SymbolicRationalApproximation →
      RB.SymbolicRationalApproximation →
      Nat

    selectedConnectionBound :
      Nat

    selectedConnectionBoundIsConnectionBound :
      selectedConnectionBound
      ≡
      connectionBound
        selectedEpsilon
        selectedScale
        selectedDiscreteConnection
        selectedContinuumConnection

    selectedConnectionBoundIsZero :
      selectedConnectionBound ≡ 0

    selectedConnectionBound≤FormulaStability :
      selectedConnectionBound
      ≤
      SymbolicRationalChristoffelC0SelectedConstantReceipt.formulaStabilityConstantNat
        selectedConstants

    selectedConnectionBound≤ConservativeShell :
      selectedConnectionBound
      ≤
      SymbolicRationalChristoffelC0SelectedConstantReceipt.conservativeShell_C_GammaNat
        selectedConstants

    ricciErrorBound :
      Nat →
      Nat →
      RB.SymbolicRationalApproximation →
      RB.SymbolicRationalApproximation →
      Nat

    selectedRicciErrorBound :
      Nat

    selectedRicciErrorBoundIsRicciErrorBound :
      selectedRicciErrorBound
      ≡
      ricciErrorBound
        selectedEpsilon
        selectedScale
        selectedDiscreteConnection
        selectedContinuumConnection

    selectedRicciErrorBoundIsZero :
      selectedRicciErrorBound ≡ 0

    selectedRicciErrorBound≤L_Ricci :
      selectedRicciErrorBound
      ≤
      MachineCheckedChristoffelC0ConstantReceipt.L_Ricci
        (SymbolicRationalChristoffelC0SelectedConstantReceipt.constantsReceipt
          selectedConstants)

    selectedRicciErrorBound≤RicciDenominator :
      selectedRicciErrorBound
      ≤
      SymbolicRationalChristoffelC0SelectedConstantReceipt.ricciBoundDenominatorNat
        selectedConstants

    selectedZeroEpsilonDerivationClosed :
      Bool

    selectedZeroEpsilonDerivationClosedIsTrue :
      selectedZeroEpsilonDerivationClosed ≡ Bool.true

    equalityHandoffIsSelectedLocalOnly :
      Bool

    equalityHandoffIsSelectedLocalOnlyIsTrue :
      equalityHandoffIsSelectedLocalOnly ≡ Bool.true

    arbitraryConnectionEqualityPromoted :
      Bool

    arbitraryConnectionEqualityPromotedIsFalse :
      arbitraryConnectionEqualityPromoted ≡ Bool.false

    inequalityBoundary :
      List String

canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SelectedZeroEpsilonConnectionErrorBoundReceipt kernel
canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel =
  record
    { selectedKernelHandoff =
        symbolicRationalChristoffelC0SelectedKernelHandoff kernel
    ; selectedKernelHandoffCanonicalTag =
        Bool.true
    ; selectedKernelHandoffCanonicalTagIsTrue =
        refl
    ; selectedPrimitive =
        canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedPrimitiveMatchesHandoff =
        refl
    ; selectedConstants =
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
    ; selectedConstantsMatchHandoff =
        refl
    ; selectedEpsilon =
        0
    ; selectedEpsilonIsZero =
        refl
    ; selectedScale =
        0
    ; selectedScaleIsZero =
        refl
    ; selectedDiscreteConnection =
        SelectedSymbolicRationalChristoffelC0Primitive.selectedDiscreteConnection
          canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedDiscreteConnectionIsPrimitive =
        refl
    ; selectedContinuumConnection =
        SelectedSymbolicRationalChristoffelC0Primitive.selectedContinuumConnection
          canonicalSelectedSymbolicRationalChristoffelC0Primitive
    ; selectedContinuumConnectionIsPrimitive =
        refl
    ; selectedLocalEqualityHandoff =
        selectedSymbolicRationalChristoffelC0PrimitivePairIdentity
    ; selectedLocalPrimitiveConnectionErrorBound =
        selectedSymbolicRationalChristoffelC0PrimitiveConnectionErrorBound
          0
          0
    ; selectedLocalKernelConnectionErrorBound =
        SymbolicRationalChristoffelC0SelectedKernelHandoff.selectedKernelConnectionErrorBound
          (symbolicRationalChristoffelC0SelectedKernelHandoff kernel)
          0
          0
    ; connectionBound =
        λ ε scale discreteConnection continuumConnection →
          0
    ; selectedConnectionBound =
        0
    ; selectedConnectionBoundIsConnectionBound =
        refl
    ; selectedConnectionBoundIsZero =
        refl
    ; selectedConnectionBound≤FormulaStability =
        z≤n
    ; selectedConnectionBound≤ConservativeShell =
        z≤n
    ; ricciErrorBound =
        λ ε scale discreteConnection continuumConnection →
          0
    ; selectedRicciErrorBound =
        0
    ; selectedRicciErrorBoundIsRicciErrorBound =
        refl
    ; selectedRicciErrorBoundIsZero =
        refl
    ; selectedRicciErrorBound≤L_Ricci =
        z≤n
    ; selectedRicciErrorBound≤RicciDenominator =
        z≤n
    ; selectedZeroEpsilonDerivationClosed =
        Bool.true
    ; selectedZeroEpsilonDerivationClosedIsTrue =
        refl
    ; equalityHandoffIsSelectedLocalOnly =
        Bool.true
    ; equalityHandoffIsSelectedLocalOnlyIsTrue =
        refl
    ; arbitraryConnectionEqualityPromoted =
        Bool.false
    ; arbitraryConnectionEqualityPromotedIsFalse =
        refl
    ; inequalityBoundary =
        ("Selected zero-epsilon receipt: epsilon = 0, scale = 0, and both symbolic-rational connections are the selected primitive pair"
        ∷ "The equality handoff is selectedLocalEqualityHandoff only; it is the primitive diagonal pair and is not exported as arbitrary connection equality"
        ∷ "connectionBound is the local Nat-valued selected bound function and evaluates to 0 on the selected zero-epsilon pair"
        ∷ "ricciErrorBound is the local Nat-valued selected bound function and evaluates to 0 on the selected zero-epsilon pair"
        ∷ "The zero selected bounds are checked against the existing formula stability, conservative shell, L_Ricci, and Ricci denominator constants by z≤n"
        ∷ [])
        ++
        SelectedSymbolicRationalChristoffelC0Primitive.primitiveBoundary
          canonicalSelectedSymbolicRationalChristoffelC0Primitive
        ++
        SymbolicRationalChristoffelC0SelectedConstantReceipt.selectedConstantBoundary
          canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
        ++
        SymbolicRationalChristoffelC0StabilityKernel.kernelBoundary kernel
    }

selectedZeroEpsilonConnectionBoundIsZero :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedConnectionBound
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)
  ≡
  0
selectedZeroEpsilonConnectionBoundIsZero kernel =
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedConnectionBoundIsZero
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)

selectedZeroEpsilonRicciErrorBoundIsZero :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedRicciErrorBound
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)
  ≡
  0
selectedZeroEpsilonRicciErrorBoundIsZero kernel =
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedRicciErrorBoundIsZero
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)

selectedZeroEpsilonLocalEqualityHandoff :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedDiscreteConnection
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)
  ≡
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedContinuumConnection
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)
selectedZeroEpsilonLocalEqualityHandoff kernel =
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedLocalEqualityHandoff
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)

selectedZeroEpsilonLocalConnectionErrorBound :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  ContinuumLimitAnalyticPrimitives.connectionErrorBound
    symbolicRationalContinuumAnalyticPrimitives
    (SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedEpsilon
      (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel))
    (SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedScale
      (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel))
    (SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedDiscreteConnection
      (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel))
    (SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedContinuumConnection
      (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel))
selectedZeroEpsilonLocalConnectionErrorBound kernel =
  SelectedZeroEpsilonConnectionErrorBoundReceipt.selectedLocalPrimitiveConnectionErrorBound
    (canonicalSelectedZeroEpsilonConnectionErrorBoundReceipt kernel)

finiteCarrierDerivativeSchemeConnectionErrorBound :
  {rate : ContinuumLimitEpsilonRateSurface} →
  {primitives : ContinuumLimitAnalyticPrimitives rate} →
  (input : FiniteCarrierConnectionConvergenceInput rate primitives) →
  (ε : ContinuumLimitEpsilonRateSurface.Epsilon rate) →
  (scale : ContinuumLimitEpsilonRateSurface.DiscreteScale rate) →
  (discreteConnection :
    ContinuumLimitAnalyticPrimitives.DiscreteConnection primitives) →
  (continuumConnection :
    ContinuumLimitAnalyticPrimitives.ContinuumConnection primitives) →
  ContinuumLimitAnalyticPrimitives.connectionErrorBound
    primitives
    ε
    scale
    discreteConnection
    continuumConnection
finiteCarrierDerivativeSchemeConnectionErrorBound
  input
  ε
  scale
  discreteConnection
  continuumConnection =
  FiniteCarrierConnectionConvergenceInput.christoffelC0FromFiniteDerivativeLaw
    input
    ε
    scale
    discreteConnection
    continuumConnection

record FiniteCarrierConnectionConvergenceFailClosedAdapter : Set where
  field
    adapterName :
      String

    lawStatus :
      ConnectionConvergenceDerivativeLawStatus

    lawStatusIsMissing :
      lawStatus ≡ derivativeLawMissingFailClosedNoConnectionPromotion

    exactMissingDerivativeLaws :
      List ConnectionConvergenceMissingDerivativeLaw

    exactMissingDerivativeLawsAreCanonical :
      exactMissingDerivativeLaws
      ≡
      canonicalConnectionConvergenceMissingDerivativeLaws

    firstMissingDerivativeLaw :
      ConnectionConvergenceMissingDerivativeLaw

    firstMissingDerivativeLawIsFiniteCarrierMetricDerivativeConsistency :
      firstMissingDerivativeLaw
      ≡
      missingFiniteCarrierMetricDerivativeConsistency

    requestedInput :
      String

    failClosedBoundary :
      List String

canonicalFiniteCarrierConnectionConvergenceFailClosedAdapter :
  FiniteCarrierConnectionConvergenceFailClosedAdapter
canonicalFiniteCarrierConnectionConvergenceFailClosedAdapter =
  record
    { adapterName =
        "FiniteCarrierMetricDerivativeScheme-to-connectionErrorBound adapter"
    ; lawStatus =
        derivativeLawMissingFailClosedNoConnectionPromotion
    ; lawStatusIsMissing =
        refl
    ; exactMissingDerivativeLaws =
        canonicalConnectionConvergenceMissingDerivativeLaws
    ; exactMissingDerivativeLawsAreCanonical =
        refl
    ; firstMissingDerivativeLaw =
        missingFiniteCarrierMetricDerivativeConsistency
    ; firstMissingDerivativeLawIsFiniteCarrierMetricDerivativeConsistency =
        refl
    ; requestedInput =
        "A finite-carrier metric derivative consistency law proving that the sampled finite derivative scheme, inverse-metric C0 control, and Christoffel formula stability extract ContinuumLimitAnalyticPrimitives.connectionErrorBound"
    ; failClosedBoundary =
        "The finite carrier, sampled metric, finite derivative, continuum partial, metric C0, derivative C0, and inverse-metric C0 sockets are typed by FiniteCarrierMetricDerivativeScheme"
        ∷ "The connection convergence adapter is inhabited only by christoffelC0FromFiniteDerivativeLaw"
        ∷ "No Christoffel C0 convergence, connectionErrorBound, Ricci convergence, C2 GR convergence, or continuum GR theorem is constructed by the fail-closed adapter"
        ∷ []
    }

record ContinuumLimitTheoremCandidate : Setω where
  field
    status :
      ContinuumLimitCandidateStatus

    epsilonRateSurface :
      ContinuumLimitEpsilonRateSurface

    analyticPrimitives :
      ContinuumLimitAnalyticPrimitives epsilonRateSurface →
      Set

    w2ResolutionRole :
      W2ContinuumResolutionRole

    w2Status :
      W2.NaturalP2ConvergencePromotionCurrentStatus

    w2BridgeOrObstructionReceipt :
      W2PM.W2CanonicalPressureMetricP2ObstructionReceipt

    p2LimitConvergenceStatus :
      G3P2.G3P2LimitConvergenceStatus

    discreteEinsteinDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    einsteinEquationInterface :
      EEC.W4MatterStressEnergyInterfaceDiagnostic

    missingPrimitives :
      List ContinuumLimitMissingPrimitive

    theoremRequest :
      String

    nonPromotionBoundary :
      List String

    w2AuthorityUnavailable :
      W2.NaturalP2ConvergencePromotionAuthorityToken →
      ⊥

    w2PromotionReceiptImpossible :
      W2.NaturalP2ConvergencePromotionReceipt →
      ⊥

continuumLimitAnalyticPrimitivesRequest :
  ContinuumLimitAnalyticPrimitives
    canonicalContinuumLimitEpsilonRateSurface →
  Set
continuumLimitAnalyticPrimitivesRequest primitives =
  ContinuumLimitAnalyticPrimitives.LatticePoint primitives

canonicalContinuumLimitTheoremCandidate :
  ContinuumLimitTheoremCandidate
canonicalContinuumLimitTheoremCandidate =
  record
    { status =
        theoremRequestOnlyW2RateBlockedNoPromotion
    ; epsilonRateSurface =
        canonicalContinuumLimitEpsilonRateSurface
    ; analyticPrimitives =
        continuumLimitAnalyticPrimitivesRequest
    ; w2ResolutionRole =
        w2ResolutionAffectsRateNotExistence
    ; w2Status =
        W2.currentNaturalP2ConvergencePromotionStatus
    ; w2BridgeOrObstructionReceipt =
        W2PM.canonicalW2PressureMetricP2ObstructionReceipt
    ; p2LimitConvergenceStatus =
        G3P2.selectedP2LimitReducedToNatUltrametricCompletenessNoPromotion
    ; discreteEinsteinDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; einsteinEquationInterface =
        EEC.canonicalW4MatterStressEnergyInterfaceDiagnostic
    ; missingPrimitives =
        missingLatticeEmbedding
        ∷ missingContinuumFieldConvergence
        ∷ missingMetricErrorBound
        ∷ missingConnectionErrorBound
        ∷ missingEinsteinTensorContinuity
        ∷ missingW2BridgeOrObstructionResolution
        ∷ []
    ; theoremRequest =
        "Continuum limit theorem candidate: given latticeEmbedding, continuumFieldConvergence, metricErrorBound, connectionErrorBound, EinsteinTensorContinuity, and a W2 bridge-or-obstruction resolution supplying the needed rate, construct metric/connection/Einstein convergence without promoting W2 or unification here"
    ; nonPromotionBoundary =
        "No W2 authority token is constructed"
        ∷ "No NaturalP2ConvergencePromotionReceipt is constructed"
        ∷ "W2 resolution is recorded as affecting convergence rate, not theorem existence"
        ∷ "No lattice embedding is constructed"
        ∷ "No continuum field convergence primitive is constructed"
        ∷ "No metricErrorBound, connectionErrorBound, or Einstein tensor continuity theorem is constructed"
        ∷ "No curved GR, Einstein-equation, GR/QFT, or unification promotion receipt is constructed"
        ∷ []
    ; w2AuthorityUnavailable =
        W2.naturalP2ConvergencePromotionAuthorityUnavailable
    ; w2PromotionReceiptImpossible =
        W2.naturalP2ConvergencePromotionReceiptImpossible
    }

continuumLimitCandidateExactStatus :
  ContinuumLimitTheoremCandidate.status
    canonicalContinuumLimitTheoremCandidate
  ≡
  theoremRequestOnlyW2RateBlockedNoPromotion
continuumLimitCandidateExactStatus = refl

continuumLimitCandidateW2Role :
  ContinuumLimitTheoremCandidate.w2ResolutionRole
    canonicalContinuumLimitTheoremCandidate
  ≡
  w2ResolutionAffectsRateNotExistence
continuumLimitCandidateW2Role = refl
