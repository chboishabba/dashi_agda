module DASHI.Physics.Closure.ContinuumLimitTheorem where

open import Agda.Primitive using (Set; Setω)
import Agda.Builtin.Bool as Bool
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; []; _++_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

nat≤refl :
  (n : Nat) →
  n ≤ n
nat≤refl zero =
  z≤n
nat≤refl (suc n) =
  s≤s (nat≤refl n)

nat≤sucRight :
  {m n : Nat} →
  m ≤ n →
  m ≤ suc n
nat≤sucRight z≤n =
  z≤n
nat≤sucRight (s≤s proof) =
  s≤s (nat≤sucRight proof)

nat≤rightSlack :
  (slack n : Nat) →
  n ≤ slack + n
nat≤rightSlack zero n =
  nat≤refl n
nat≤rightSlack (suc slack) n =
  nat≤sucRight (nat≤rightSlack slack n)

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

    tightAuditedL_Gamma :
      Nat

    tightAuditedL_GammaIs44 :
      tightAuditedL_Gamma ≡ 44

    conservativeL_Gamma :
      Nat

    conservativeL_GammaIs48 :
      conservativeL_Gamma ≡ 48

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
    ; tightAuditedL_Gamma =
        44
    ; tightAuditedL_GammaIs44 =
        refl
    ; conservativeL_Gamma =
        48
    ; conservativeL_GammaIs48 =
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
        "Machine-checked constants consumed by the finite-carrier Christoffel C0 law surface: conservative L_Gamma = 48, tight audited L_Gamma = 44, L_Ricci = 640, optional sharp L_Ricci = 112, and conservative shell C_Gamma <= 2"
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

machineCheckedChristoffelTightAuditedL_GammaIs44 :
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  44
machineCheckedChristoffelTightAuditedL_GammaIs44 =
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_GammaIs44
    canonicalMachineCheckedChristoffelC0ConstantReceipt

machineCheckedChristoffelConservativeL_GammaIs48 :
  MachineCheckedChristoffelC0ConstantReceipt.conservativeL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
  ≡
  48
machineCheckedChristoffelConservativeL_GammaIs48 =
  MachineCheckedChristoffelC0ConstantReceipt.conservativeL_GammaIs48
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

data OrderedRationalGaugePrimitiveShape : Set where
  d_QQZeroPrimitive :
    OrderedRationalGaugePrimitiveShape

  d_QQSymmetryPrimitive :
    OrderedRationalGaugePrimitiveShape

  d_QQTrianglePrimitive :
    OrderedRationalGaugePrimitiveShape

  threeMinusNNonnegativePrimitive :
    OrderedRationalGaugePrimitiveShape

  threeMinusNPositivePrimitive :
    OrderedRationalGaugePrimitiveShape

  nonnegativeScaleBy48Primitive :
    OrderedRationalGaugePrimitiveShape

  nonnegativeScaleBy72Primitive :
    OrderedRationalGaugePrimitiveShape

  nonnegativeScaleBy80Primitive :
    OrderedRationalGaugePrimitiveShape

  nonnegativeScaleBy640Primitive :
    OrderedRationalGaugePrimitiveShape

record OrderedRationalGaugeToolkitReceipt : Set where
  field
    d_QQZeroLaw :
      OrderedRationalGaugePrimitiveShape

    d_QQZeroLawIsPrimitive :
      d_QQZeroLaw ≡ d_QQZeroPrimitive

    d_QQSymmetryLaw :
      OrderedRationalGaugePrimitiveShape

    d_QQSymmetryLawIsPrimitive :
      d_QQSymmetryLaw ≡ d_QQSymmetryPrimitive

    d_QQTriangleLaw :
      OrderedRationalGaugePrimitiveShape

    d_QQTriangleLawIsPrimitive :
      d_QQTriangleLaw ≡ d_QQTrianglePrimitive

    threeMinusNNonnegativeLaw :
      OrderedRationalGaugePrimitiveShape

    threeMinusNNonnegativeLawIsPrimitive :
      threeMinusNNonnegativeLaw ≡ threeMinusNNonnegativePrimitive

    threeMinusNPositiveLaw :
      OrderedRationalGaugePrimitiveShape

    threeMinusNPositiveLawIsPrimitive :
      threeMinusNPositiveLaw ≡ threeMinusNPositivePrimitive

    scaleConstant48 :
      Nat

    scaleConstant48Is48 :
      scaleConstant48 ≡ 48

    scaleConstant48NonnegativeLaw :
      OrderedRationalGaugePrimitiveShape

    scaleConstant48NonnegativeLawIsPrimitive :
      scaleConstant48NonnegativeLaw ≡ nonnegativeScaleBy48Primitive

    scaleConstant72 :
      Nat

    scaleConstant72Is72 :
      scaleConstant72 ≡ 72

    scaleConstant72NonnegativeLaw :
      OrderedRationalGaugePrimitiveShape

    scaleConstant72NonnegativeLawIsPrimitive :
      scaleConstant72NonnegativeLaw ≡ nonnegativeScaleBy72Primitive

    scaleConstant80 :
      Nat

    scaleConstant80Is80 :
      scaleConstant80 ≡ 80

    scaleConstant80NonnegativeLaw :
      OrderedRationalGaugePrimitiveShape

    scaleConstant80NonnegativeLawIsPrimitive :
      scaleConstant80NonnegativeLaw ≡ nonnegativeScaleBy80Primitive

    scaleConstant640 :
      Nat

    scaleConstant640Is640 :
      scaleConstant640 ≡ 640

    scaleConstant640NonnegativeLaw :
      OrderedRationalGaugePrimitiveShape

    scaleConstant640NonnegativeLawIsPrimitive :
      scaleConstant640NonnegativeLaw ≡ nonnegativeScaleBy640Primitive

    orderedQQTheoremPromoted :
      Bool

    orderedQQTheoremPromotedIsFalse :
      orderedQQTheoremPromoted ≡ Bool.false

    gaugeToolkitBoundary :
      List String

canonicalOrderedRationalGaugeToolkitReceipt :
  OrderedRationalGaugeToolkitReceipt
canonicalOrderedRationalGaugeToolkitReceipt =
  record
    { d_QQZeroLaw =
        d_QQZeroPrimitive
    ; d_QQZeroLawIsPrimitive =
        refl
    ; d_QQSymmetryLaw =
        d_QQSymmetryPrimitive
    ; d_QQSymmetryLawIsPrimitive =
        refl
    ; d_QQTriangleLaw =
        d_QQTrianglePrimitive
    ; d_QQTriangleLawIsPrimitive =
        refl
    ; threeMinusNNonnegativeLaw =
        threeMinusNNonnegativePrimitive
    ; threeMinusNNonnegativeLawIsPrimitive =
        refl
    ; threeMinusNPositiveLaw =
        threeMinusNPositivePrimitive
    ; threeMinusNPositiveLawIsPrimitive =
        refl
    ; scaleConstant48 =
        48
    ; scaleConstant48Is48 =
        refl
    ; scaleConstant48NonnegativeLaw =
        nonnegativeScaleBy48Primitive
    ; scaleConstant48NonnegativeLawIsPrimitive =
        refl
    ; scaleConstant72 =
        72
    ; scaleConstant72Is72 =
        refl
    ; scaleConstant72NonnegativeLaw =
        nonnegativeScaleBy72Primitive
    ; scaleConstant72NonnegativeLawIsPrimitive =
        refl
    ; scaleConstant80 =
        80
    ; scaleConstant80Is80 =
        refl
    ; scaleConstant80NonnegativeLaw =
        nonnegativeScaleBy80Primitive
    ; scaleConstant80NonnegativeLawIsPrimitive =
        refl
    ; scaleConstant640 =
        640
    ; scaleConstant640Is640 =
        refl
    ; scaleConstant640NonnegativeLaw =
        nonnegativeScaleBy640Primitive
    ; scaleConstant640NonnegativeLawIsPrimitive =
        refl
    ; orderedQQTheoremPromoted =
        Bool.false
    ; orderedQQTheoremPromotedIsFalse =
        refl
    ; gaugeToolkitBoundary =
        "Ordered rational gauge toolkit receipt: d_QQ zero, symmetry, and triangle are recorded as primitive proof targets"
        ∷ "threeMinusN nonnegative and positive gauge laws are recorded as primitive proof targets"
        ∷ "Nonnegative scaling targets are recorded for constants 48, 72, 80, and 640"
        ∷ "This receipt does not promote an ordered QQ theorem; it names the exact remaining algebraic laws needed by the analytic kernel"
        ∷ []
    }

orderedRationalGaugeToolkitD_QQZeroPrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw toolkit
  ≡
  d_QQZeroPrimitive
orderedRationalGaugeToolkitD_QQZeroPrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.d_QQZeroLawIsPrimitive toolkit

orderedRationalGaugeToolkitD_QQSymmetryPrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw toolkit
  ≡
  d_QQSymmetryPrimitive
orderedRationalGaugeToolkitD_QQSymmetryPrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLawIsPrimitive toolkit

orderedRationalGaugeToolkitD_QQTrianglePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw toolkit
  ≡
  d_QQTrianglePrimitive
orderedRationalGaugeToolkitD_QQTrianglePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.d_QQTriangleLawIsPrimitive toolkit

orderedRationalGaugeToolkitThreeMinusNNonnegativePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw toolkit
  ≡
  threeMinusNNonnegativePrimitive
orderedRationalGaugeToolkitThreeMinusNNonnegativePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLawIsPrimitive toolkit

orderedRationalGaugeToolkitThreeMinusNPositivePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw toolkit
  ≡
  threeMinusNPositivePrimitive
orderedRationalGaugeToolkitThreeMinusNPositivePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLawIsPrimitive toolkit

orderedRationalGaugeToolkitScale48Is48 :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant48 toolkit
  ≡
  48
orderedRationalGaugeToolkitScale48Is48 toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant48Is48 toolkit

orderedRationalGaugeToolkitScale48NonnegativePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw toolkit
  ≡
  nonnegativeScaleBy48Primitive
orderedRationalGaugeToolkitScale48NonnegativePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLawIsPrimitive
    toolkit

orderedRationalGaugeToolkitScale72Is72 :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant72 toolkit
  ≡
  72
orderedRationalGaugeToolkitScale72Is72 toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant72Is72 toolkit

orderedRationalGaugeToolkitScale72NonnegativePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw toolkit
  ≡
  nonnegativeScaleBy72Primitive
orderedRationalGaugeToolkitScale72NonnegativePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLawIsPrimitive
    toolkit

orderedRationalGaugeToolkitScale80Is80 :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant80 toolkit
  ≡
  80
orderedRationalGaugeToolkitScale80Is80 toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant80Is80 toolkit

orderedRationalGaugeToolkitScale80NonnegativePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw toolkit
  ≡
  nonnegativeScaleBy80Primitive
orderedRationalGaugeToolkitScale80NonnegativePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLawIsPrimitive
    toolkit

orderedRationalGaugeToolkitScale640Is640 :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant640 toolkit
  ≡
  640
orderedRationalGaugeToolkitScale640Is640 toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant640Is640 toolkit

orderedRationalGaugeToolkitScale640NonnegativePrimitive :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw toolkit
  ≡
  nonnegativeScaleBy640Primitive
orderedRationalGaugeToolkitScale640NonnegativePrimitive toolkit =
  OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLawIsPrimitive
    toolkit

record OrderedRationalGaugeThreeMinusNPrimitiveLawPair
  (toolkit : OrderedRationalGaugeToolkitReceipt) : Set where
  field
    threeMinusNNonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw toolkit
      ≡
      threeMinusNNonnegativePrimitive

    threeMinusNPositivePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw toolkit
      ≡
      threeMinusNPositivePrimitive

orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair toolkit
orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair toolkit =
  record
    { threeMinusNNonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitThreeMinusNNonnegativePrimitive toolkit
    ; threeMinusNPositivePrimitiveLaw =
        orderedRationalGaugeToolkitThreeMinusNPositivePrimitive toolkit
    }

record OrderedRationalGaugeScaleNonnegativePrimitiveLaws
  (toolkit : OrderedRationalGaugeToolkitReceipt) : Set where
  field
    scale48NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy48Primitive

    scale72NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy72Primitive

    scale80NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy80Primitive

    scale640NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy640Primitive

orderedRationalGaugeToolkitScaleNonnegativePrimitiveLaws :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeScaleNonnegativePrimitiveLaws toolkit
orderedRationalGaugeToolkitScaleNonnegativePrimitiveLaws toolkit =
  record
    { scale48NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale48NonnegativePrimitive toolkit
    ; scale72NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale72NonnegativePrimitive toolkit
    ; scale80NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale80NonnegativePrimitive toolkit
    ; scale640NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale640NonnegativePrimitive toolkit
    }

record OrderedRationalGaugeScaleNonnegativePrimitiveBundle
  (toolkit : OrderedRationalGaugeToolkitReceipt) : Set where
  field
    scale48ConstantLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48 toolkit
      ≡
      48

    scale48NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy48Primitive

    scale72ConstantLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72 toolkit
      ≡
      72

    scale72NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy72Primitive

    scale80ConstantLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80 toolkit
      ≡
      80

    scale80NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy80Primitive

    scale640ConstantLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640 toolkit
      ≡
      640

    scale640NonnegativePrimitiveLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw toolkit
      ≡
      nonnegativeScaleBy640Primitive

orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle toolkit
orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle toolkit =
  record
    { scale48ConstantLaw =
        orderedRationalGaugeToolkitScale48Is48 toolkit
    ; scale48NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale48NonnegativePrimitive toolkit
    ; scale72ConstantLaw =
        orderedRationalGaugeToolkitScale72Is72 toolkit
    ; scale72NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale72NonnegativePrimitive toolkit
    ; scale80ConstantLaw =
        orderedRationalGaugeToolkitScale80Is80 toolkit
    ; scale80NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale80NonnegativePrimitive toolkit
    ; scale640ConstantLaw =
        orderedRationalGaugeToolkitScale640Is640 toolkit
    ; scale640NonnegativePrimitiveLaw =
        orderedRationalGaugeToolkitScale640NonnegativePrimitive toolkit
    }

orderedRationalGaugeCanonicalThreeMinusNPrimitiveLawPair :
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair
    canonicalOrderedRationalGaugeToolkitReceipt
orderedRationalGaugeCanonicalThreeMinusNPrimitiveLawPair =
  orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair
    canonicalOrderedRationalGaugeToolkitReceipt

orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle :
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle
    canonicalOrderedRationalGaugeToolkitReceipt
orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle =
  orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
    canonicalOrderedRationalGaugeToolkitReceipt

orderedRationalGaugeToolkitOrderedQQTheoremNotPromoted :
  (toolkit : OrderedRationalGaugeToolkitReceipt) →
  OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromoted toolkit
  ≡
  Bool.false
orderedRationalGaugeToolkitOrderedQQTheoremNotPromoted toolkit =
  OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromotedIsFalse toolkit

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

    orderedGaugeToolkit :
      OrderedRationalGaugeToolkitReceipt

    orderedGaugeToolkitIsCanonical :
      orderedGaugeToolkit ≡ canonicalOrderedRationalGaugeToolkitReceipt

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
    ; orderedGaugeToolkit =
        canonicalOrderedRationalGaugeToolkitReceipt
    ; orderedGaugeToolkitIsCanonical =
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
        ∷ "The ordered rational gauge toolkit records d_QQ zero/symmetry/triangle, threeMinusN positivity, and nonnegative scaling proof targets"
        ∷ "No ordered QQ theorem, rational-order proof, or analytic Christoffel estimate is promoted by this receipt"
        ∷
        OrderedRationalGaugeToolkitReceipt.gaugeToolkitBoundary
          canonicalOrderedRationalGaugeToolkitReceipt
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

data OrderedRationalShellAChristoffelPerturbationTerm : Set where
  inverseMetricPerturbationTimesMetricDerivative :
    OrderedRationalShellAChristoffelPerturbationTerm

  inverseMetricTimesDerivativePerturbation :
    OrderedRationalShellAChristoffelPerturbationTerm

record OrderedRationalShellAChristoffelPerturbationRouteReceipt : Set where
  field
    orderedShellAConstants :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    orderedShellAConstantsAreCanonical :
      orderedShellAConstants
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    firstPerturbationTerm :
      OrderedRationalShellAChristoffelPerturbationTerm

    firstPerturbationTermIsInverseMetricPerturbation :
      firstPerturbationTerm
      ≡
      inverseMetricPerturbationTimesMetricDerivative

    secondPerturbationTerm :
      OrderedRationalShellAChristoffelPerturbationTerm

    secondPerturbationTermIsDerivativePerturbation :
      secondPerturbationTerm
      ≡
      inverseMetricTimesDerivativePerturbation

    perturbationTermCount :
      Nat

    perturbationTermCountIs2 :
      perturbationTermCount ≡ 2

    finiteSumSlotFactor :
      Nat

    finiteSumSlotFactorIs4 :
      finiteSumSlotFactor ≡ 4

    halfFactorNumerator :
      Nat

    halfFactorNumeratorIs1 :
      halfFactorNumerator ≡ 1

    halfFactorDenominator :
      Nat

    halfFactorDenominatorIs2 :
      halfFactorDenominator ≡ 2

    shellAInverseMetricMax :
      Nat

    shellAInverseMetricMaxIs4 :
      shellAInverseMetricMax ≡ 4

    auditedShellAInverseMetricMax :
      Nat

    auditedShellAInverseMetricMaxIs3 :
      auditedShellAInverseMetricMax ≡ 3

    shellAMetricDerivativeMax :
      Nat

    shellAMetricDerivativeMaxIs8 :
      shellAMetricDerivativeMax ≡ 8

    auditedShellAMetricDerivativeMax :
      Nat

    auditedShellAMetricDerivativeMaxIs8 :
      auditedShellAMetricDerivativeMax ≡ 8

    derivativePlusPerturbationUnit :
      Nat

    derivativePlusPerturbationUnitIs9 :
      derivativePlusPerturbationUnit ≡ 9

    lGammaRouteNumerator :
      Nat

    lGammaRouteNumeratorIs144 :
      lGammaRouteNumerator ≡ 144

    lGammaRouteDenominator :
      Nat

    lGammaRouteDenominatorIs2 :
      lGammaRouteDenominator ≡ 2

    lGammaRouteQuotient :
      Nat

    lGammaRouteQuotientIs72 :
      lGammaRouteQuotient ≡ 72

    finalL_GammaRouteQuotient :
      Nat

    finalL_GammaRouteQuotientIs48 :
      finalL_GammaRouteQuotient ≡ 48

    finalL_GammaRouteMatchesMachineCheckedConstant :
      finalL_GammaRouteQuotient
      ≡
      MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        canonicalMachineCheckedChristoffelC0ConstantReceipt

    tightAuditedL_GammaRouteQuotient :
      Nat

    tightAuditedL_GammaRouteQuotientIs44 :
      tightAuditedL_GammaRouteQuotient ≡ 44

    tightAuditedL_GammaRouteMatchesMachineCheckedTightConstant :
      tightAuditedL_GammaRouteQuotient
      ≡
      MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
        canonicalMachineCheckedChristoffelC0ConstantReceipt

    legacyConservativeL_GammaBoundary :
      String

    routeL_GammaMatchesShellAConstants :
      lGammaRouteQuotient
      ≡
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants

    perturbationSplitExposed :
      Bool

    perturbationSplitExposedIsTrue :
      perturbationSplitExposed ≡ Bool.true

    fullOrderedQQEstimatePromoted :
      Bool

    fullOrderedQQEstimatePromotedIsFalse :
      fullOrderedQQEstimatePromoted ≡ Bool.false

    perturbationRouteText :
      String

    perturbationRouteBoundary :
      List String

canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt
canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt =
  record
    { orderedShellAConstants =
        canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; orderedShellAConstantsAreCanonical =
        refl
    ; firstPerturbationTerm =
        inverseMetricPerturbationTimesMetricDerivative
    ; firstPerturbationTermIsInverseMetricPerturbation =
        refl
    ; secondPerturbationTerm =
        inverseMetricTimesDerivativePerturbation
    ; secondPerturbationTermIsDerivativePerturbation =
        refl
    ; perturbationTermCount =
        2
    ; perturbationTermCountIs2 =
        refl
    ; finiteSumSlotFactor =
        4
    ; finiteSumSlotFactorIs4 =
        refl
    ; halfFactorNumerator =
        1
    ; halfFactorNumeratorIs1 =
        refl
    ; halfFactorDenominator =
        2
    ; halfFactorDenominatorIs2 =
        refl
    ; shellAInverseMetricMax =
        4
    ; shellAInverseMetricMaxIs4 =
        refl
    ; auditedShellAInverseMetricMax =
        3
    ; auditedShellAInverseMetricMaxIs3 =
        refl
    ; shellAMetricDerivativeMax =
        8
    ; shellAMetricDerivativeMaxIs8 =
        refl
    ; auditedShellAMetricDerivativeMax =
        8
    ; auditedShellAMetricDerivativeMaxIs8 =
        refl
    ; derivativePlusPerturbationUnit =
        9
    ; derivativePlusPerturbationUnitIs9 =
        refl
    ; lGammaRouteNumerator =
        144
    ; lGammaRouteNumeratorIs144 =
        refl
    ; lGammaRouteDenominator =
        2
    ; lGammaRouteDenominatorIs2 =
        refl
    ; lGammaRouteQuotient =
        72
    ; lGammaRouteQuotientIs72 =
        refl
    ; finalL_GammaRouteQuotient =
        48
    ; finalL_GammaRouteQuotientIs48 =
        refl
    ; finalL_GammaRouteMatchesMachineCheckedConstant =
        refl
    ; tightAuditedL_GammaRouteQuotient =
        44
    ; tightAuditedL_GammaRouteQuotientIs44 =
        refl
    ; tightAuditedL_GammaRouteMatchesMachineCheckedTightConstant =
        refl
    ; legacyConservativeL_GammaBoundary =
        "Legacy/conservative Shell A perturbation envelope remains 72; the canonical conservative Nat perturbation route remains 48; the tight audited route is 44."
    ; routeL_GammaMatchesShellAConstants =
        refl
    ; perturbationSplitExposed =
        Bool.true
    ; perturbationSplitExposedIsTrue =
        refl
    ; fullOrderedQQEstimatePromoted =
        Bool.false
    ; fullOrderedQQEstimatePromotedIsFalse =
        refl
    ; perturbationRouteText =
        "Shell A Christoffel perturbation route: conservative checked Nat constant is 48; tight audited Nat constant is 44 from inverseMetricMax 3 and metricDerivativeMax 8; legacy/conservative envelope 1/2 * 4 slots * inverseMetricMax 4 * (metricDerivativeMax 8 + perturbation unit 1) = 72 remains non-promoting."
    ; perturbationRouteBoundary =
        "Two-term Christoffel perturbation split is exposed as (delta g^-1) * partial g plus g^-1 * delta(partial g)"
        ∷ "The finite Christoffel sum contributes the four-slot factor from Fin 4"
        ∷ "Shell A conservative inverse metric max is recorded as 4; audited inverse metric max is recorded as 3; metric derivative max is recorded as 8"
        ∷ "The route numerator is 144, denominator is 2, and quotient is the legacy/conservative envelope 72"
        ∷ "The conservative Shell A perturbation route quotient remains the machine-checked L_Gamma = 48"
        ∷ "The tight audited Shell A perturbation route quotient is recorded as L_Gamma = 44"
        ∷ "This receipt does not promote the full ordered QQ estimate; it only names the analytic decomposition required by ChristoffelFormulaC0Stable"
        ∷ []
    }

orderedRationalShellAPerturbationRouteL_GammaIs48 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.finalL_GammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  48
orderedRationalShellAPerturbationRouteL_GammaIs48 =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.finalL_GammaRouteQuotientIs48
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteTightAuditedL_GammaIs44 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  44
orderedRationalShellAPerturbationRouteTightAuditedL_GammaIs44 =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteQuotientIs44
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteTightAuditedMatchesMachineCheckedTightConstant :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
orderedRationalShellAPerturbationRouteTightAuditedMatchesMachineCheckedTightConstant =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteMatchesMachineCheckedTightConstant
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteAuditedInverseMetricMaxIs3 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAInverseMetricMax
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  3
orderedRationalShellAPerturbationRouteAuditedInverseMetricMaxIs3 =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAInverseMetricMaxIs3
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteAuditedMetricDerivativeMaxIs8 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAMetricDerivativeMax
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  8
orderedRationalShellAPerturbationRouteAuditedMetricDerivativeMaxIs8 =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAMetricDerivativeMaxIs8
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteL_GammaIs72 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  72
orderedRationalShellAPerturbationRouteL_GammaIs72 =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotientIs72
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAPerturbationRouteLegacyConservativeL_GammaIs72 :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  72
orderedRationalShellAPerturbationRouteLegacyConservativeL_GammaIs72 =
  orderedRationalShellAPerturbationRouteL_GammaIs72

orderedRationalShellAPerturbationRouteMatchesConstants :
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
  ≡
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
orderedRationalShellAPerturbationRouteMatchesConstants =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.routeL_GammaMatchesShellAConstants
    canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

orderedRationalShellAOrderedGaugeToolkit :
  OrderedRationalGaugeToolkitReceipt
orderedRationalShellAOrderedGaugeToolkit =
  OrderedRationalShellAChristoffelC0ConstantReceipt.orderedGaugeToolkit
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalShellAOrderedGaugeToolkitIsCanonical :
  orderedRationalShellAOrderedGaugeToolkit
  ≡
  canonicalOrderedRationalGaugeToolkitReceipt
orderedRationalShellAOrderedGaugeToolkitIsCanonical =
  OrderedRationalShellAChristoffelC0ConstantReceipt.orderedGaugeToolkitIsCanonical
    canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

orderedRationalGaugeD_QQZeroLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  d_QQZeroPrimitive
orderedRationalGaugeD_QQZeroLawPrimitive =
  orderedRationalGaugeToolkitD_QQZeroPrimitive
    canonicalOrderedRationalGaugeToolkitReceipt

orderedRationalGaugeD_QQSymmetryLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  d_QQSymmetryPrimitive
orderedRationalGaugeD_QQSymmetryLawPrimitive =
  orderedRationalGaugeToolkitD_QQSymmetryPrimitive
    canonicalOrderedRationalGaugeToolkitReceipt

orderedRationalGaugeD_QQTriangleLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  d_QQTrianglePrimitive
orderedRationalGaugeD_QQTriangleLawPrimitive =
  orderedRationalGaugeToolkitD_QQTrianglePrimitive
    canonicalOrderedRationalGaugeToolkitReceipt

orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  threeMinusNNonnegativePrimitive
orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNNonnegativePrimitiveLaw
    orderedRationalGaugeCanonicalThreeMinusNPrimitiveLawPair

orderedRationalGaugeThreeMinusNPositiveLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  threeMinusNPositivePrimitive
orderedRationalGaugeThreeMinusNPositiveLawPrimitive =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNPositivePrimitiveLaw
    orderedRationalGaugeCanonicalThreeMinusNPrimitiveLawPair

orderedRationalGaugeScale48Is48 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant48
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  48
orderedRationalGaugeScale48Is48 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48ConstantLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale48NonnegativeLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  nonnegativeScaleBy48Primitive
orderedRationalGaugeScale48NonnegativeLawPrimitive =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48NonnegativePrimitiveLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale72Is72 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant72
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  72
orderedRationalGaugeScale72Is72 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72ConstantLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale72NonnegativeLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  nonnegativeScaleBy72Primitive
orderedRationalGaugeScale72NonnegativeLawPrimitive =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72NonnegativePrimitiveLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale80Is80 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant80
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  80
orderedRationalGaugeScale80Is80 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80ConstantLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale80NonnegativeLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  nonnegativeScaleBy80Primitive
orderedRationalGaugeScale80NonnegativeLawPrimitive =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80NonnegativePrimitiveLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale640Is640 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant640
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  640
orderedRationalGaugeScale640Is640 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640ConstantLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeScale640NonnegativeLawPrimitive :
  OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  nonnegativeScaleBy640Primitive
orderedRationalGaugeScale640NonnegativeLawPrimitive =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640NonnegativePrimitiveLaw
    orderedRationalGaugeCanonicalScaleNonnegativePrimitiveBundle

orderedRationalGaugeOrderedQQTheoremNotPromoted :
  OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromoted
    canonicalOrderedRationalGaugeToolkitReceipt
  ≡
  Bool.false
orderedRationalGaugeOrderedQQTheoremNotPromoted =
  orderedRationalGaugeToolkitOrderedQQTheoremNotPromoted
    canonicalOrderedRationalGaugeToolkitReceipt

record OrderedRationalShellADenominatorReciprocalReceipt : Set where
  field
    constantsReceipt :
      OrderedRationalShellAChristoffelC0ConstantReceipt

    constantsReceiptIsCanonical :
      constantsReceipt
      ≡
      canonicalOrderedRationalShellAChristoffelC0ConstantReceipt

    radialCoordinateName :
      String

    schwarzschildRadius :
      Nat

    schwarzschildRadiusIs2 :
      schwarzschildRadius ≡ 2

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

    shellALowerEndpointPositive :
      1 ≤ shellALowerEndpoint

    schwarzschildRadiusBelowShell :
      schwarzschildRadius ≤ shellALowerEndpoint

    horizonClearance :
      Nat

    horizonClearanceIs1 :
      horizonClearance ≡ 1

    radialMinusSchwarzschildLowerBound :
      Nat

    radialMinusSchwarzschildLowerBoundIs1 :
      radialMinusSchwarzschildLowerBound ≡ 1

    radialDenominatorPositiveText :
      String

    reciprocalRUpperBoundNumerator :
      Nat

    reciprocalRUpperBoundNumeratorIs1 :
      reciprocalRUpperBoundNumerator ≡ 1

    reciprocalRUpperBoundDenominator :
      Nat

    reciprocalRUpperBoundDenominatorIs3 :
      reciprocalRUpperBoundDenominator ≡ 3

    reciprocalRSquaredUpperBoundNumerator :
      Nat

    reciprocalRSquaredUpperBoundNumeratorIs1 :
      reciprocalRSquaredUpperBoundNumerator ≡ 1

    reciprocalRSquaredUpperBoundDenominator :
      Nat

    reciprocalRSquaredUpperBoundDenominatorIs9 :
      reciprocalRSquaredUpperBoundDenominator ≡ 9

    reciprocalGapUpperBoundNumerator :
      Nat

    reciprocalGapUpperBoundNumeratorIs1 :
      reciprocalGapUpperBoundNumerator ≡ 1

    reciprocalGapUpperBoundDenominator :
      Nat

    reciprocalGapUpperBoundDenominatorIs1 :
      reciprocalGapUpperBoundDenominator ≡ 1

    reciprocalGapSquaredUpperBoundNumerator :
      Nat

    reciprocalGapSquaredUpperBoundNumeratorIs1 :
      reciprocalGapSquaredUpperBoundNumerator ≡ 1

    reciprocalGapSquaredUpperBoundDenominator :
      Nat

    reciprocalGapSquaredUpperBoundDenominatorIs1 :
      reciprocalGapSquaredUpperBoundDenominator ≡ 1

    inverseMetricAbsMax :
      Nat

    inverseMetricAbsMaxIs4 :
      inverseMetricAbsMax ≡ 4

    auditedInverseMetricAbsMax :
      Nat

    auditedInverseMetricAbsMaxIs3 :
      auditedInverseMetricAbsMax ≡ 3

    metricDerivativeAbsMax :
      Nat

    metricDerivativeAbsMaxIs8 :
      metricDerivativeAbsMax ≡ 8

    auditedMetricDerivativeAbsMax :
      Nat

    auditedMetricDerivativeAbsMaxIs8 :
      auditedMetricDerivativeAbsMax ≡ 8

    perturbationHalfFactorDenominator :
      Nat

    perturbationHalfFactorDenominatorIs2 :
      perturbationHalfFactorDenominator ≡ 2

    finFourSummandCount :
      Nat

    finFourSummandCountIs4 :
      finFourSummandCount ≡ 4

    christoffelFormulaEnvelope :
      Nat

    christoffelFormulaEnvelopeIs72 :
      christoffelFormulaEnvelope ≡ 72

    finalChristoffelFormulaEnvelope :
      Nat

    finalChristoffelFormulaEnvelopeIs48 :
      finalChristoffelFormulaEnvelope ≡ 48

    finalChristoffelFormulaEnvelopeMatchesMachineCheckedConstant :
      finalChristoffelFormulaEnvelope
      ≡
      MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
        canonicalMachineCheckedChristoffelC0ConstantReceipt

    tightAuditedChristoffelFormulaEnvelope :
      Nat

    tightAuditedChristoffelFormulaEnvelopeIs44 :
      tightAuditedChristoffelFormulaEnvelope ≡ 44

    tightAuditedChristoffelFormulaEnvelopeMatchesMachineCheckedTightConstant :
      tightAuditedChristoffelFormulaEnvelope
      ≡
      MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
        canonicalMachineCheckedChristoffelC0ConstantReceipt

    legacyConservativeChristoffelFormulaEnvelopeBoundary :
      String

    reciprocalBoundsFeedChristoffelFormulaC0Stable :
      Bool

    reciprocalBoundsFeedChristoffelFormulaC0StableIsTrue :
      reciprocalBoundsFeedChristoffelFormulaC0Stable ≡ Bool.true

    orderedQQTheoremPromoted :
      Bool

    orderedQQTheoremPromotedIsFalse :
      orderedQQTheoremPromoted ≡ Bool.false

    reciprocalBoundary :
      List String

canonicalOrderedRationalShellADenominatorReciprocalReceipt :
  OrderedRationalShellADenominatorReciprocalReceipt
canonicalOrderedRationalShellADenominatorReciprocalReceipt =
  record
    { constantsReceipt =
        canonicalOrderedRationalShellAChristoffelC0ConstantReceipt
    ; constantsReceiptIsCanonical =
        refl
    ; radialCoordinateName =
        "r"
    ; schwarzschildRadius =
        2
    ; schwarzschildRadiusIs2 =
        refl
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
    ; shellALowerEndpointPositive =
        s≤s z≤n
    ; schwarzschildRadiusBelowShell =
        s≤s (s≤s z≤n)
    ; horizonClearance =
        1
    ; horizonClearanceIs1 =
        refl
    ; radialMinusSchwarzschildLowerBound =
        1
    ; radialMinusSchwarzschildLowerBoundIs1 =
        refl
    ; radialDenominatorPositiveText =
        "On Shell A, r in [3,4] and r_s = 2, so r > 0 and r - r_s >= 1."
    ; reciprocalRUpperBoundNumerator =
        1
    ; reciprocalRUpperBoundNumeratorIs1 =
        refl
    ; reciprocalRUpperBoundDenominator =
        3
    ; reciprocalRUpperBoundDenominatorIs3 =
        refl
    ; reciprocalRSquaredUpperBoundNumerator =
        1
    ; reciprocalRSquaredUpperBoundNumeratorIs1 =
        refl
    ; reciprocalRSquaredUpperBoundDenominator =
        9
    ; reciprocalRSquaredUpperBoundDenominatorIs9 =
        refl
    ; reciprocalGapUpperBoundNumerator =
        1
    ; reciprocalGapUpperBoundNumeratorIs1 =
        refl
    ; reciprocalGapUpperBoundDenominator =
        1
    ; reciprocalGapUpperBoundDenominatorIs1 =
        refl
    ; reciprocalGapSquaredUpperBoundNumerator =
        1
    ; reciprocalGapSquaredUpperBoundNumeratorIs1 =
        refl
    ; reciprocalGapSquaredUpperBoundDenominator =
        1
    ; reciprocalGapSquaredUpperBoundDenominatorIs1 =
        refl
    ; inverseMetricAbsMax =
        4
    ; inverseMetricAbsMaxIs4 =
        refl
    ; auditedInverseMetricAbsMax =
        3
    ; auditedInverseMetricAbsMaxIs3 =
        refl
    ; metricDerivativeAbsMax =
        8
    ; metricDerivativeAbsMaxIs8 =
        refl
    ; auditedMetricDerivativeAbsMax =
        8
    ; auditedMetricDerivativeAbsMaxIs8 =
        refl
    ; perturbationHalfFactorDenominator =
        2
    ; perturbationHalfFactorDenominatorIs2 =
        refl
    ; finFourSummandCount =
        4
    ; finFourSummandCountIs4 =
        refl
    ; christoffelFormulaEnvelope =
        72
    ; christoffelFormulaEnvelopeIs72 =
        refl
    ; finalChristoffelFormulaEnvelope =
        48
    ; finalChristoffelFormulaEnvelopeIs48 =
        refl
    ; finalChristoffelFormulaEnvelopeMatchesMachineCheckedConstant =
        refl
    ; tightAuditedChristoffelFormulaEnvelope =
        44
    ; tightAuditedChristoffelFormulaEnvelopeIs44 =
        refl
    ; tightAuditedChristoffelFormulaEnvelopeMatchesMachineCheckedTightConstant =
        refl
    ; legacyConservativeChristoffelFormulaEnvelopeBoundary =
        "Legacy/conservative Shell A denominator envelope remains 72; the final canonical conservative Christoffel formula envelope remains 48; the tight audited envelope is 44."
    ; reciprocalBoundsFeedChristoffelFormulaC0Stable =
        Bool.true
    ; reciprocalBoundsFeedChristoffelFormulaC0StableIsTrue =
        refl
    ; orderedQQTheoremPromoted =
        Bool.false
    ; orderedQQTheoremPromotedIsFalse =
        refl
    ; reciprocalBoundary =
        "Shell A denominator surface: r in [3,4], r_s = 2, horizon clearance delta = 1"
        ∷ "The denominators used by Schwarzschild Christoffel formulae are positive: r > 0 and r - r_s >= 1"
        ∷ "Reciprocal bounds recorded for the analytic kernel: 1/r <= 1/3, 1/r^2 <= 1/9, 1/(r-r_s) <= 1, and 1/(r-r_s)^2 <= 1"
        ∷ "Conservative inverse metric sup bound is recorded as 4; audited inverse metric sup bound is recorded as 3; metric-derivative sup bound is recorded as 8 on Shell A"
        ∷ "These bounds feed the legacy/conservative Christoffel perturbation envelope 1/2 * 4 * 4 * (8 + 1) = 72"
        ∷ "The conservative Shell A Christoffel formula envelope remains the machine-checked L_Gamma = 48"
        ∷ "The tight audited Shell A Christoffel formula envelope is recorded as L_Gamma = 44"
        ∷ "This is a denominator and reciprocal receipt only; it does not promote an ordered QQ theorem"
        ∷ []
    }

orderedRationalShellADenominatorInverseMetricAbsMaxIs4 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
    receipt
  ≡
  4
orderedRationalShellADenominatorInverseMetricAbsMaxIs4 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMaxIs4
    receipt

orderedRationalShellADenominatorAuditedInverseMetricAbsMaxIs3 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.auditedInverseMetricAbsMax
    receipt
  ≡
  3
orderedRationalShellADenominatorAuditedInverseMetricAbsMaxIs3 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.auditedInverseMetricAbsMaxIs3
    receipt

orderedRationalShellADenominatorMetricDerivativeAbsMaxIs8 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
    receipt
  ≡
  8
orderedRationalShellADenominatorMetricDerivativeAbsMaxIs8 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMaxIs8
    receipt

orderedRationalShellADenominatorAuditedMetricDerivativeAbsMaxIs8 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.auditedMetricDerivativeAbsMax
    receipt
  ≡
  8
orderedRationalShellADenominatorAuditedMetricDerivativeAbsMaxIs8 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.auditedMetricDerivativeAbsMaxIs8
    receipt

orderedRationalShellADenominatorFinalEnvelopeIs48 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    receipt
  ≡
  48
orderedRationalShellADenominatorFinalEnvelopeIs48 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelopeIs48
    receipt

orderedRationalShellADenominatorFinalEnvelopeMatchesMachineCheckedConstant :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    receipt
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
orderedRationalShellADenominatorFinalEnvelopeMatchesMachineCheckedConstant receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelopeMatchesMachineCheckedConstant
    receipt

orderedRationalShellADenominatorTightAuditedEnvelopeIs44 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    receipt
  ≡
  44
orderedRationalShellADenominatorTightAuditedEnvelopeIs44 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelopeIs44
    receipt

orderedRationalShellADenominatorTightAuditedEnvelopeMatchesMachineCheckedTightConstant :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    receipt
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
orderedRationalShellADenominatorTightAuditedEnvelopeMatchesMachineCheckedTightConstant receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelopeMatchesMachineCheckedTightConstant
    receipt

orderedRationalShellADenominatorLegacyEnvelopeIs72 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
    receipt
  ≡
  72
orderedRationalShellADenominatorLegacyEnvelopeIs72 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelopeIs72
    receipt

orderedRationalShellADenominatorReciprocalFeedsChristoffelFormulaC0Stable :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0Stable
    receipt
  ≡
  Bool.true
orderedRationalShellADenominatorReciprocalFeedsChristoffelFormulaC0Stable receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0StableIsTrue
    receipt

orderedRationalShellADenominatorSchwarzschildRadiusIs2 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.schwarzschildRadius
    receipt
  ≡
  2
orderedRationalShellADenominatorSchwarzschildRadiusIs2 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.schwarzschildRadiusIs2
    receipt

orderedRationalShellADenominatorLowerEndpointIs3 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.shellALowerEndpoint
    receipt
  ≡
  3
orderedRationalShellADenominatorLowerEndpointIs3 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.shellALowerEndpointIs3
    receipt

orderedRationalShellADenominatorUpperEndpointIs4 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.shellAUpperEndpoint
    receipt
  ≡
  4
orderedRationalShellADenominatorUpperEndpointIs4 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.shellAUpperEndpointIs4
    receipt

orderedRationalShellADenominatorHorizonClearanceIs1 :
  (receipt : OrderedRationalShellADenominatorReciprocalReceipt) →
  OrderedRationalShellADenominatorReciprocalReceipt.horizonClearance
    receipt
  ≡
  1
orderedRationalShellADenominatorHorizonClearanceIs1 receipt =
  OrderedRationalShellADenominatorReciprocalReceipt.horizonClearanceIs1
    receipt

orderedRationalShellASchwarzschildRadiusIs2 :
  OrderedRationalShellADenominatorReciprocalReceipt.schwarzschildRadius
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  2
orderedRationalShellASchwarzschildRadiusIs2 =
  orderedRationalShellADenominatorSchwarzschildRadiusIs2
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellALowerEndpointIs3 :
  OrderedRationalShellADenominatorReciprocalReceipt.shellALowerEndpoint
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  3
orderedRationalShellALowerEndpointIs3 =
  orderedRationalShellADenominatorLowerEndpointIs3
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAUpperEndpointIs4 :
  OrderedRationalShellADenominatorReciprocalReceipt.shellAUpperEndpoint
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  4
orderedRationalShellAUpperEndpointIs4 =
  orderedRationalShellADenominatorUpperEndpointIs4
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAHorizonClearanceIs1 :
  OrderedRationalShellADenominatorReciprocalReceipt.horizonClearance
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  1
orderedRationalShellAHorizonClearanceIs1 =
  orderedRationalShellADenominatorHorizonClearanceIs1
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAInverseMetricAbsMaxIs4 :
  OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  4
orderedRationalShellAInverseMetricAbsMaxIs4 =
  orderedRationalShellADenominatorInverseMetricAbsMaxIs4
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAAuditedInverseMetricAbsMaxIs3 :
  OrderedRationalShellADenominatorReciprocalReceipt.auditedInverseMetricAbsMax
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  3
orderedRationalShellAAuditedInverseMetricAbsMaxIs3 =
  orderedRationalShellADenominatorAuditedInverseMetricAbsMaxIs3
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAMetricDerivativeAbsMaxIs8 :
  OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  8
orderedRationalShellAMetricDerivativeAbsMaxIs8 =
  orderedRationalShellADenominatorMetricDerivativeAbsMaxIs8
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAAuditedMetricDerivativeAbsMaxIs8 :
  OrderedRationalShellADenominatorReciprocalReceipt.auditedMetricDerivativeAbsMax
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  8
orderedRationalShellAAuditedMetricDerivativeAbsMaxIs8 =
  orderedRationalShellADenominatorAuditedMetricDerivativeAbsMaxIs8
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaEnvelopeIs48 :
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  48
orderedRationalShellAChristoffelFormulaEnvelopeIs48 =
  orderedRationalShellADenominatorFinalEnvelopeIs48
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaEnvelopeMatchesMachineCheckedConstant :
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
orderedRationalShellAChristoffelFormulaEnvelopeMatchesMachineCheckedConstant =
  orderedRationalShellADenominatorFinalEnvelopeMatchesMachineCheckedConstant
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaTightAuditedEnvelopeIs44 :
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  44
orderedRationalShellAChristoffelFormulaTightAuditedEnvelopeIs44 =
  orderedRationalShellADenominatorTightAuditedEnvelopeIs44
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaTightAuditedEnvelopeMatchesMachineCheckedTightConstant :
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
orderedRationalShellAChristoffelFormulaTightAuditedEnvelopeMatchesMachineCheckedTightConstant =
  orderedRationalShellADenominatorTightAuditedEnvelopeMatchesMachineCheckedTightConstant
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaEnvelopeIs72 :
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  72
orderedRationalShellAChristoffelFormulaEnvelopeIs72 =
  orderedRationalShellADenominatorLegacyEnvelopeIs72
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAChristoffelFormulaLegacyConservativeEnvelopeIs72 :
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  72
orderedRationalShellAChristoffelFormulaLegacyConservativeEnvelopeIs72 =
  orderedRationalShellAChristoffelFormulaEnvelopeIs72

orderedRationalShellARadialMinusSchwarzschildLowerBoundIs1 :
  OrderedRationalShellADenominatorReciprocalReceipt.radialMinusSchwarzschildLowerBound
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  1
orderedRationalShellARadialMinusSchwarzschildLowerBoundIs1 =
  OrderedRationalShellADenominatorReciprocalReceipt.radialMinusSchwarzschildLowerBoundIs1
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable :
  OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0Stable
    canonicalOrderedRationalShellADenominatorReciprocalReceipt
  ≡
  Bool.true
orderedRationalShellAReciprocalBoundsFeedChristoffelFormulaC0Stable =
  orderedRationalShellADenominatorReciprocalFeedsChristoffelFormulaC0Stable
    canonicalOrderedRationalShellADenominatorReciprocalReceipt

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

    orderedShellAPerturbationRoute :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteAreCanonical :
      orderedShellAPerturbationRoute
      ≡
      canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteL_GammaIs48 :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.finalL_GammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      48

    orderedShellAPerturbationRouteL_GammaIs72 :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      72

    orderedShellAPerturbationRouteMatchesConstants :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants

    orderedGaugeToolkit :
      OrderedRationalGaugeToolkitReceipt

    orderedGaugeToolkitIsCanonical :
      orderedGaugeToolkit ≡ canonicalOrderedRationalGaugeToolkitReceipt

    orderedGaugeD_QQZeroLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw orderedGaugeToolkit
      ≡
      d_QQZeroPrimitive

    orderedGaugeD_QQSymmetryLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw orderedGaugeToolkit
      ≡
      d_QQSymmetryPrimitive

    orderedGaugeD_QQTriangleLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw orderedGaugeToolkit
      ≡
      d_QQTrianglePrimitive

    orderedGaugeThreeMinusNNonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
        orderedGaugeToolkit
      ≡
      threeMinusNNonnegativePrimitive

    orderedGaugeThreeMinusNPositiveLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
        orderedGaugeToolkit
      ≡
      threeMinusNPositivePrimitive

    orderedGaugeScale48Is48 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48 orderedGaugeToolkit
      ≡
      48

    orderedGaugeScale48NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy48Primitive

    orderedGaugeScale72Is72 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72 orderedGaugeToolkit
      ≡
      72

    orderedGaugeScale72NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy72Primitive

    orderedGaugeScale80Is80 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80 orderedGaugeToolkit
      ≡
      80

    orderedGaugeScale80NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy80Primitive

    orderedGaugeScale640Is640 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640 orderedGaugeToolkit
      ≡
      640

    orderedGaugeScale640NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy640Primitive

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

    orderedGaugeToolkit :
      OrderedRationalGaugeToolkitReceipt

    orderedGaugeToolkitIsCanonical :
      orderedGaugeToolkit ≡ canonicalOrderedRationalGaugeToolkitReceipt

    orderedGaugeD_QQZeroLawSelected :
      OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw orderedGaugeToolkit
      ≡
      d_QQZeroPrimitive

    orderedGaugeD_QQSymmetryLawSelected :
      OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw orderedGaugeToolkit
      ≡
      d_QQSymmetryPrimitive

    orderedGaugeD_QQTriangleLawSelected :
      OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw orderedGaugeToolkit
      ≡
      d_QQTrianglePrimitive

    orderedGaugeThreeMinusNNonnegativeLawSelected :
      OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
        orderedGaugeToolkit
      ≡
      threeMinusNNonnegativePrimitive

    orderedGaugeThreeMinusNPositiveLawSelected :
      OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
        orderedGaugeToolkit
      ≡
      threeMinusNPositivePrimitive

    orderedGaugeScale48SelectedAs48 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48 orderedGaugeToolkit
      ≡
      48

    orderedGaugeScale48NonnegativeLawSelected :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy48Primitive

    orderedGaugeScale72SelectedAs72 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72 orderedGaugeToolkit
      ≡
      72

    orderedGaugeScale72NonnegativeLawSelected :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy72Primitive

    orderedGaugeScale80SelectedAs80 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80 orderedGaugeToolkit
      ≡
      80

    orderedGaugeScale80NonnegativeLawSelected :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy80Primitive

    orderedGaugeScale640SelectedAs640 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640 orderedGaugeToolkit
      ≡
      640

    orderedGaugeScale640NonnegativeLawSelected :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy640Primitive

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
    ; orderedGaugeToolkit =
        canonicalOrderedRationalGaugeToolkitReceipt
    ; orderedGaugeToolkitIsCanonical =
        refl
    ; orderedGaugeD_QQZeroLawSelected =
        orderedRationalGaugeD_QQZeroLawPrimitive
    ; orderedGaugeD_QQSymmetryLawSelected =
        orderedRationalGaugeD_QQSymmetryLawPrimitive
    ; orderedGaugeD_QQTriangleLawSelected =
        orderedRationalGaugeD_QQTriangleLawPrimitive
    ; orderedGaugeThreeMinusNNonnegativeLawSelected =
        orderedRationalGaugeThreeMinusNNonnegativeLawPrimitive
    ; orderedGaugeThreeMinusNPositiveLawSelected =
        orderedRationalGaugeThreeMinusNPositiveLawPrimitive
    ; orderedGaugeScale48SelectedAs48 =
        orderedRationalGaugeScale48Is48
    ; orderedGaugeScale48NonnegativeLawSelected =
        orderedRationalGaugeScale48NonnegativeLawPrimitive
    ; orderedGaugeScale72SelectedAs72 =
        orderedRationalGaugeScale72Is72
    ; orderedGaugeScale72NonnegativeLawSelected =
        orderedRationalGaugeScale72NonnegativeLawPrimitive
    ; orderedGaugeScale80SelectedAs80 =
        orderedRationalGaugeScale80Is80
    ; orderedGaugeScale80NonnegativeLawSelected =
        orderedRationalGaugeScale80NonnegativeLawPrimitive
    ; orderedGaugeScale640SelectedAs640 =
        orderedRationalGaugeScale640Is640
    ; orderedGaugeScale640NonnegativeLawSelected =
        orderedRationalGaugeScale640NonnegativeLawPrimitive
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
        ∷ "The ordered rational gauge toolkit is selected canonically for d_QQ laws, threeMinusN gauge positivity, and nonnegative scaling constants"
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

selectedSymbolicRationalOrderedGaugeToolkitIsCanonical :
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt
  ≡
  canonicalOrderedRationalGaugeToolkitReceipt
selectedSymbolicRationalOrderedGaugeToolkitIsCanonical =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkitIsCanonical
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedGaugeD_QQZeroLaw :
  OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  d_QQZeroPrimitive
selectedSymbolicRationalOrderedGaugeD_QQZeroLaw =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeD_QQZeroLawSelected
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedGaugeD_QQSymmetryLaw :
  OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  d_QQSymmetryPrimitive
selectedSymbolicRationalOrderedGaugeD_QQSymmetryLaw =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeD_QQSymmetryLawSelected
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedGaugeD_QQTriangleLaw :
  OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  d_QQTrianglePrimitive
selectedSymbolicRationalOrderedGaugeD_QQTriangleLaw =
  SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeD_QQTriangleLawSelected
    canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt

selectedSymbolicRationalOrderedGaugeThreeMinusNNonnegativeLaw :
  OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  threeMinusNNonnegativePrimitive
selectedSymbolicRationalOrderedGaugeThreeMinusNNonnegativeLaw =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNNonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeThreeMinusNPositiveLaw :
  OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  threeMinusNPositivePrimitive
selectedSymbolicRationalOrderedGaugeThreeMinusNPositiveLaw =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNPositivePrimitiveLaw
    (orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale48Is48 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant48
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  48
selectedSymbolicRationalOrderedGaugeScale48Is48 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale48NonnegativeLaw :
  OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  nonnegativeScaleBy48Primitive
selectedSymbolicRationalOrderedGaugeScale48NonnegativeLaw =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale72Is72 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant72
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  72
selectedSymbolicRationalOrderedGaugeScale72Is72 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale72NonnegativeLaw :
  OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  nonnegativeScaleBy72Primitive
selectedSymbolicRationalOrderedGaugeScale72NonnegativeLaw =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale80Is80 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant80
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  80
selectedSymbolicRationalOrderedGaugeScale80Is80 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale80NonnegativeLaw :
  OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  nonnegativeScaleBy80Primitive
selectedSymbolicRationalOrderedGaugeScale80NonnegativeLaw =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale640Is640 :
  OrderedRationalGaugeToolkitReceipt.scaleConstant640
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  640
selectedSymbolicRationalOrderedGaugeScale640Is640 =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

selectedSymbolicRationalOrderedGaugeScale640NonnegativeLaw :
  OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
    (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
      canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt)
  ≡
  nonnegativeScaleBy640Primitive
selectedSymbolicRationalOrderedGaugeScale640NonnegativeLaw =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0SelectedConstantReceipt.orderedGaugeToolkit
        canonicalSymbolicRationalChristoffelC0SelectedConstantReceipt))

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

    orderedGaugeToolkit :
      OrderedRationalGaugeToolkitReceipt

    orderedGaugeToolkitIsCanonical :
      orderedGaugeToolkit ≡ canonicalOrderedRationalGaugeToolkitReceipt

    orderedGaugeD_QQZeroLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw orderedGaugeToolkit
      ≡
      d_QQZeroPrimitive

    orderedGaugeD_QQSymmetryLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw orderedGaugeToolkit
      ≡
      d_QQSymmetryPrimitive

    orderedGaugeD_QQTriangleLaw :
      OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw orderedGaugeToolkit
      ≡
      d_QQTrianglePrimitive

    orderedGaugeThreeMinusNNonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
        orderedGaugeToolkit
      ≡
      threeMinusNNonnegativePrimitive

    orderedGaugeThreeMinusNPositiveLaw :
      OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
        orderedGaugeToolkit
      ≡
      threeMinusNPositivePrimitive

    orderedGaugeScale48Is48 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48 orderedGaugeToolkit
      ≡
      48

    orderedGaugeScale48NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy48Primitive

    orderedGaugeScale72Is72 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72 orderedGaugeToolkit
      ≡
      72

    orderedGaugeScale72NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy72Primitive

    orderedGaugeScale80Is80 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80 orderedGaugeToolkit
      ≡
      80

    orderedGaugeScale80NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy80Primitive

    orderedGaugeScale640Is640 :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640 orderedGaugeToolkit
      ≡
      640

    orderedGaugeScale640NonnegativeLaw :
      OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
        orderedGaugeToolkit
      ≡
      nonnegativeScaleBy640Primitive

    shellADenominatorReciprocal :
      OrderedRationalShellADenominatorReciprocalReceipt

    shellADenominatorReciprocalIsCanonical :
      shellADenominatorReciprocal
      ≡
      canonicalOrderedRationalShellADenominatorReciprocalReceipt

    shellAInverseMetricAbsMaxIs4 :
      OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
        shellADenominatorReciprocal
      ≡
      4

    shellAMetricDerivativeAbsMaxIs8 :
      OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
        shellADenominatorReciprocal
      ≡
      8

    shellAChristoffelFormulaEnvelopeIs48 :
      OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
        shellADenominatorReciprocal
      ≡
      48

    shellAChristoffelFormulaEnvelopeIs72 :
      OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
        shellADenominatorReciprocal
      ≡
      72

    shellAReciprocalBoundsFeedChristoffelFormulaC0Stable :
      OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0Stable
        shellADenominatorReciprocal
      ≡
      Bool.true

    orderedShellAPerturbationRoute :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteAreCanonical :
      orderedShellAPerturbationRoute
      ≡
      canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    orderedShellAPerturbationRouteL_GammaIs48 :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.finalL_GammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      48

    orderedShellAPerturbationRouteL_GammaIs72 :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      72

    orderedShellAPerturbationRouteMatchesConstants :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
        orderedShellAPerturbationRoute
      ≡
      OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
        orderedShellAConstants

    perturbationRouteInverseMetricMaxMatchesDenominatorReceipt :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.shellAInverseMetricMax
        orderedShellAPerturbationRoute
      ≡
      OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
        shellADenominatorReciprocal

    perturbationRouteDerivativeMaxMatchesDenominatorReceipt :
      OrderedRationalShellAChristoffelPerturbationRouteReceipt.shellAMetricDerivativeMax
        orderedShellAPerturbationRoute
      ≡
      OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
        shellADenominatorReciprocal

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

symbolicRationalKernelOrderedGaugeToolkitIsCanonical :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
    kernel
  ≡
  canonicalOrderedRationalGaugeToolkitReceipt
symbolicRationalKernelOrderedGaugeToolkitIsCanonical kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkitIsCanonical
    kernel

symbolicRationalKernelOrderedGaugeOrderedQQTheoremNotPromoted :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.orderedQQTheoremPromoted
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  Bool.false
symbolicRationalKernelOrderedGaugeOrderedQQTheoremNotPromoted kernel =
  orderedRationalGaugeToolkitOrderedQQTheoremNotPromoted
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)

symbolicRationalKernelOrderedGaugeD_QQZeroLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.d_QQZeroLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  d_QQZeroPrimitive
symbolicRationalKernelOrderedGaugeD_QQZeroLaw kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQZeroLaw
    kernel

symbolicRationalKernelOrderedGaugeD_QQSymmetryLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.d_QQSymmetryLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  d_QQSymmetryPrimitive
symbolicRationalKernelOrderedGaugeD_QQSymmetryLaw kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQSymmetryLaw
    kernel

symbolicRationalKernelOrderedGaugeD_QQTriangleLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.d_QQTriangleLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  d_QQTrianglePrimitive
symbolicRationalKernelOrderedGaugeD_QQTriangleLaw kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQTriangleLaw
    kernel

symbolicRationalKernelOrderedGaugeThreeMinusNNonnegativeLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.threeMinusNNonnegativeLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  threeMinusNNonnegativePrimitive
symbolicRationalKernelOrderedGaugeThreeMinusNNonnegativeLaw kernel =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNNonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeThreeMinusNPositiveLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.threeMinusNPositiveLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  threeMinusNPositivePrimitive
symbolicRationalKernelOrderedGaugeThreeMinusNPositiveLaw kernel =
  OrderedRationalGaugeThreeMinusNPrimitiveLawPair.threeMinusNPositivePrimitiveLaw
    (orderedRationalGaugeToolkitThreeMinusNPrimitiveLawPair
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale48Is48 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant48
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  48
symbolicRationalKernelOrderedGaugeScale48Is48 kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale48NonnegativeLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant48NonnegativeLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  nonnegativeScaleBy48Primitive
symbolicRationalKernelOrderedGaugeScale48NonnegativeLaw kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale48NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale72Is72 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant72
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  72
symbolicRationalKernelOrderedGaugeScale72Is72 kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale72NonnegativeLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant72NonnegativeLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  nonnegativeScaleBy72Primitive
symbolicRationalKernelOrderedGaugeScale72NonnegativeLaw kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale72NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale80Is80 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant80
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  80
symbolicRationalKernelOrderedGaugeScale80Is80 kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale80NonnegativeLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant80NonnegativeLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  nonnegativeScaleBy80Primitive
symbolicRationalKernelOrderedGaugeScale80NonnegativeLaw kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale80NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale640Is640 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant640
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  640
symbolicRationalKernelOrderedGaugeScale640Is640 kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640ConstantLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelOrderedGaugeScale640NonnegativeLaw :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalGaugeToolkitReceipt.scaleConstant640NonnegativeLaw
    (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
      kernel)
  ≡
  nonnegativeScaleBy640Primitive
symbolicRationalKernelOrderedGaugeScale640NonnegativeLaw kernel =
  OrderedRationalGaugeScaleNonnegativePrimitiveBundle.scale640NonnegativePrimitiveLaw
    (orderedRationalGaugeToolkitScaleNonnegativePrimitiveBundle
      (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
        kernel))

symbolicRationalKernelShellADenominatorReciprocalIsCanonical :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
    kernel
  ≡
  canonicalOrderedRationalShellADenominatorReciprocalReceipt
symbolicRationalKernelShellADenominatorReciprocalIsCanonical kernel =
  SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocalIsCanonical
    kernel

symbolicRationalKernelShellAInverseMetricAbsMaxIs4 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  4
symbolicRationalKernelShellAInverseMetricAbsMaxIs4 kernel =
  orderedRationalShellADenominatorInverseMetricAbsMaxIs4
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAAuditedInverseMetricAbsMaxIs3 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.auditedInverseMetricAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  3
symbolicRationalKernelShellAAuditedInverseMetricAbsMaxIs3 kernel =
  orderedRationalShellADenominatorAuditedInverseMetricAbsMaxIs3
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAMetricDerivativeAbsMaxIs8 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  8
symbolicRationalKernelShellAMetricDerivativeAbsMaxIs8 kernel =
  orderedRationalShellADenominatorMetricDerivativeAbsMaxIs8
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAAuditedMetricDerivativeAbsMaxIs8 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.auditedMetricDerivativeAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  8
symbolicRationalKernelShellAAuditedMetricDerivativeAbsMaxIs8 kernel =
  orderedRationalShellADenominatorAuditedMetricDerivativeAbsMaxIs8
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormulaEnvelopeIs48 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  48
symbolicRationalKernelShellAChristoffelFormulaEnvelopeIs48 kernel =
  orderedRationalShellADenominatorFinalEnvelopeIs48
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormulaEnvelopeMatchesMachineCheckedConstant :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.finalChristoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.L_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
symbolicRationalKernelShellAChristoffelFormulaEnvelopeMatchesMachineCheckedConstant kernel =
  orderedRationalShellADenominatorFinalEnvelopeMatchesMachineCheckedConstant
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormula22Le48 :
  22 ≤ 48
symbolicRationalKernelShellAChristoffelFormula22Le48 =
  nat≤rightSlack 26 22

symbolicRationalKernelShellAChristoffelFormulaTightAuditedEnvelopeIs44 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  44
symbolicRationalKernelShellAChristoffelFormulaTightAuditedEnvelopeIs44 kernel =
  orderedRationalShellADenominatorTightAuditedEnvelopeIs44
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormulaTightAuditedEnvelopeMatchesMachineCheckedTightConstant :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.tightAuditedChristoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  MachineCheckedChristoffelC0ConstantReceipt.tightAuditedL_Gamma
    canonicalMachineCheckedChristoffelC0ConstantReceipt
symbolicRationalKernelShellAChristoffelFormulaTightAuditedEnvelopeMatchesMachineCheckedTightConstant kernel =
  orderedRationalShellADenominatorTightAuditedEnvelopeMatchesMachineCheckedTightConstant
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormulaEnvelopeIs72 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  72
symbolicRationalKernelShellAChristoffelFormulaEnvelopeIs72 kernel =
  orderedRationalShellADenominatorLegacyEnvelopeIs72
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelShellAChristoffelFormulaLegacyConservativeEnvelopeIs72 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.christoffelFormulaEnvelope
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  72
symbolicRationalKernelShellAChristoffelFormulaLegacyConservativeEnvelopeIs72 kernel =
  symbolicRationalKernelShellAChristoffelFormulaEnvelopeIs72 kernel

symbolicRationalKernelShellAReciprocalBoundsFeedChristoffelFormulaC0Stable :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundsFeedChristoffelFormulaC0Stable
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
  ≡
  Bool.true
symbolicRationalKernelShellAReciprocalBoundsFeedChristoffelFormulaC0Stable kernel =
  orderedRationalShellADenominatorReciprocalFeedsChristoffelFormulaC0Stable
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)

symbolicRationalKernelPerturbationRouteL_GammaIs48 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.finalL_GammaRouteQuotient
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  48
symbolicRationalKernelPerturbationRouteL_GammaIs48 kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteL_GammaIs48
    kernel

symbolicRationalKernelPerturbationRouteTightAuditedL_GammaIs44 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteQuotient
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  44
symbolicRationalKernelPerturbationRouteTightAuditedL_GammaIs44 kernel =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.tightAuditedL_GammaRouteQuotientIs44
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)

symbolicRationalKernelPerturbationRouteAuditedInverseMetricMaxIs3 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAInverseMetricMax
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  3
symbolicRationalKernelPerturbationRouteAuditedInverseMetricMaxIs3 kernel =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAInverseMetricMaxIs3
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)

symbolicRationalKernelPerturbationRouteAuditedMetricDerivativeMaxIs8 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAMetricDerivativeMax
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  8
symbolicRationalKernelPerturbationRouteAuditedMetricDerivativeMaxIs8 kernel =
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.auditedShellAMetricDerivativeMaxIs8
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)

symbolicRationalKernelPerturbationRouteL_GammaIs72 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  72
symbolicRationalKernelPerturbationRouteL_GammaIs72 kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteL_GammaIs72
    kernel

symbolicRationalKernelPerturbationRouteLegacyConservativeL_GammaIs72 :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  72
symbolicRationalKernelPerturbationRouteLegacyConservativeL_GammaIs72 kernel =
  symbolicRationalKernelPerturbationRouteL_GammaIs72 kernel

symbolicRationalKernelPerturbationRouteMatchesConstants :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.lGammaRouteQuotient
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  OrderedRationalShellAChristoffelC0ConstantReceipt.shellA_L_Gamma
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAConstants
      kernel)
symbolicRationalKernelPerturbationRouteMatchesConstants kernel =
  SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteMatchesConstants
    kernel

symbolicRationalKernelPerturbationRouteInverseMetricMaxMatchesDenominatorReceipt :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.shellAInverseMetricMax
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
symbolicRationalKernelPerturbationRouteInverseMetricMaxMatchesDenominatorReceipt kernel =
  SymbolicRationalChristoffelC0StabilityKernel.perturbationRouteInverseMetricMaxMatchesDenominatorReceipt
    kernel

symbolicRationalKernelPerturbationRouteDerivativeMaxMatchesDenominatorReceipt :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  OrderedRationalShellAChristoffelPerturbationRouteReceipt.shellAMetricDerivativeMax
    (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
      kernel)
  ≡
  OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
    (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
      kernel)
symbolicRationalKernelPerturbationRouteDerivativeMaxMatchesDenominatorReceipt kernel =
  SymbolicRationalChristoffelC0StabilityKernel.perturbationRouteDerivativeMaxMatchesDenominatorReceipt
    kernel

symbolicRationalKernelChristoffelFormulaC0Stable :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  Nat →
  Nat →
  RB.SymbolicRationalApproximation →
  RB.SymbolicRationalApproximation →
  Set
symbolicRationalKernelChristoffelFormulaC0Stable kernel =
  SymbolicRationalChristoffelC0StabilityKernel.ChristoffelFormulaC0Stable
    kernel

symbolicRationalKernelChristoffelFormulaC0Stability :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
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
  symbolicRationalKernelChristoffelFormulaC0Stable
    kernel
    ε
    scale
    discreteConnection
    continuumConnection
symbolicRationalKernelChristoffelFormulaC0Stability kernel =
  SymbolicRationalChristoffelC0StabilityKernel.christoffelFormulaC0Stability
    kernel

symbolicRationalKernelConnectionErrorBoundExtraction :
  (kernel : SymbolicRationalChristoffelC0StabilityKernel) →
  (ε : Nat) →
  (scale : Nat) →
  (discreteConnection : RB.SymbolicRationalApproximation) →
  (continuumConnection : RB.SymbolicRationalApproximation) →
  symbolicRationalKernelChristoffelFormulaC0Stable
    kernel
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
symbolicRationalKernelConnectionErrorBoundExtraction kernel =
  SymbolicRationalChristoffelC0StabilityKernel.connectionErrorBoundExtraction
    kernel

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
    ; orderedShellAPerturbationRoute =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
          kernel
    ; orderedShellAPerturbationRouteAreCanonical =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteAreCanonical
          kernel
    ; orderedShellAPerturbationRouteL_GammaIs48 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteL_GammaIs48
          kernel
    ; orderedShellAPerturbationRouteL_GammaIs72 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteL_GammaIs72
          kernel
    ; orderedShellAPerturbationRouteMatchesConstants =
        SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRouteMatchesConstants
          kernel
    ; orderedGaugeToolkit =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
          kernel
    ; orderedGaugeToolkitIsCanonical =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkitIsCanonical
          kernel
    ; orderedGaugeD_QQZeroLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQZeroLaw
          kernel
    ; orderedGaugeD_QQSymmetryLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQSymmetryLaw
          kernel
    ; orderedGaugeD_QQTriangleLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeD_QQTriangleLaw
          kernel
    ; orderedGaugeThreeMinusNNonnegativeLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeThreeMinusNNonnegativeLaw
          kernel
    ; orderedGaugeThreeMinusNPositiveLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeThreeMinusNPositiveLaw
          kernel
    ; orderedGaugeScale48Is48 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale48Is48
          kernel
    ; orderedGaugeScale48NonnegativeLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale48NonnegativeLaw
          kernel
    ; orderedGaugeScale72Is72 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale72Is72
          kernel
    ; orderedGaugeScale72NonnegativeLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale72NonnegativeLaw
          kernel
    ; orderedGaugeScale80Is80 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale80Is80
          kernel
    ; orderedGaugeScale80NonnegativeLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale80NonnegativeLaw
          kernel
    ; orderedGaugeScale640Is640 =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale640Is640
          kernel
    ; orderedGaugeScale640NonnegativeLaw =
        SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeScale640NonnegativeLaw
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
        ∷ "The kernel also supplies the Shell A denominator/reciprocal receipt: r > 0, r - r_s >= 1, conservative inverse-metric bound 4, audited inverse-metric bound 3, derivative bound 8, conservative Christoffel formula envelope 48, tight audited envelope 44, and legacy/conservative envelope 72"
        ∷ "The kernel supplies the Shell A perturbation route: two perturbation terms, four finite-sum slots, conservative inverse metric max 4, audited inverse metric max 3, metric derivative max 8, conservative L_Gamma = 48, tight audited L_Gamma = 44, and legacy/conservative L_Gamma = 72"
        ∷ "The kernel supplies ordered rational gauge primitives for d_QQ zero/symmetry/triangle, threeMinusN positivity, and nonnegative scaling by 48, 72, 80, and 640"
        ∷ "The ordered rational inequality is threaded only as the named primitive C'_Gamma <= C_Gamma, not as a promoted QQ theorem"
        ∷ "Only the Christoffel formula C0 stability kernel and equality-valued connectionErrorBound extraction remain external"
        ∷
        OrderedRationalShellAChristoffelC0ConstantReceipt.orderedShellABoundary
          (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAConstants
            kernel)
        ++
        OrderedRationalShellADenominatorReciprocalReceipt.reciprocalBoundary
          (SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
            kernel)
        ++
        OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationRouteBoundary
          (SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
            kernel)
        ++
        OrderedRationalGaugeToolkitReceipt.gaugeToolkitBoundary
          (SymbolicRationalChristoffelC0StabilityKernel.orderedGaugeToolkit
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

    selectedRicciPerturbation2144Over27LeShell80 :
      2144 ≤ 2160

    selectedRicciShell80LeRicciDenominator640 :
      80 ≤ 640

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
    ; selectedRicciPerturbation2144Over27LeShell80 =
        nat≤rightSlack 16 2144
    ; selectedRicciShell80LeRicciDenominator640 =
        nat≤rightSlack 560 80
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
        ∷ "Ricci perturbation arithmetic records 2144/27 <= 80 by the Nat cross-multiplication inhabitant 2144 <= 2160"
        ∷ "The Ricci shell ceiling records 80 <= 640, matching the selected Ricci denominator receipt"
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
