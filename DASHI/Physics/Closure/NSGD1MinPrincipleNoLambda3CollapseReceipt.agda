module DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed GD1 two-regime minimum-principle receipt (strengthened).
--
-- This receipt records the conditional GD1 no-collapse lane on the Kato
-- carrier, including:
--   * one-sided minimum-principle inequality
--   * two-regime split (critical supercritical/subcritical)
--   * explicit candidate/route visibility on h_delta1 and TheoremG/Q2
--   * explicit dependency on exact constants, LayerCZ term, and GD1 proof terms
--   * explicit Q2 uniform bound gate from GD1 for the contradiction route
--
-- It is intentionally fail-closed:
--   * h_delta1 is not discharged
--   * uniform Q2 bound via GD1 is not discharged
--   * collapseImpossible is false
--   * Clay Navier-Stokes promotion is false
--   * no promotion constructor is inhabited

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSGD1MinPrincipleNoLambda3CollapseStatus : Set where
  gd1MinimumPrincipleReceiptRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStatus

data NSGD1MinPrincipleNoLambda3CollapseStage : Set where
  gd1InequalityRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  criticalGapRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  lambda2ZeroBoundaryCarrierRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  g12OnBiaxialCarrierRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  rellichStrainEvolutionRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  restoringG12SquareRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  pressureCzIntegratedLInfShapeRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  viscousKatoGapCostRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  twoRegimeGronwallShapeRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  twoRegimeMinimumPrincipleRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  twoRegimeConditionallyGatedRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  supercriticalRestoringRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  subcriticalExponentialLowerBoundRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  lambda3EqualsG12OnBiaxialCarrierRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  hDelta1CandidateRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  hDelta1RouteVisibilityRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  theoremGRouteVisibilityRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  q2RouteVisibilityRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  theoremGQ2GD1ContradictionRouteRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  q2UniformBoundFromGD1RoleRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  exactConstantsAndCZAndGD1ProofTermsRequiredRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  clayPromotionBlockedRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  failClosedRouteRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage

canonicalNSGD1MinPrincipleNoLambda3CollapseStages :
  List NSGD1MinPrincipleNoLambda3CollapseStage
canonicalNSGD1MinPrincipleNoLambda3CollapseStages =
  gd1InequalityRecorded
  ∷ criticalGapRecorded
  ∷ lambda2ZeroBoundaryCarrierRecorded
  ∷ g12OnBiaxialCarrierRecorded
  ∷ rellichStrainEvolutionRecorded
  ∷ restoringG12SquareRecorded
  ∷ pressureCzIntegratedLInfShapeRecorded
  ∷ viscousKatoGapCostRecorded
  ∷ twoRegimeGronwallShapeRecorded
  ∷ twoRegimeMinimumPrincipleRecorded
  ∷ twoRegimeConditionallyGatedRecorded
  ∷ supercriticalRestoringRecorded
  ∷ subcriticalExponentialLowerBoundRecorded
  ∷ lambda3EqualsG12OnBiaxialCarrierRecorded
  ∷ hDelta1CandidateRecorded
  ∷ hDelta1RouteVisibilityRecorded
  ∷ theoremGRouteVisibilityRecorded
  ∷ q2RouteVisibilityRecorded
  ∷ theoremGQ2GD1ContradictionRouteRecorded
  ∷ q2UniformBoundFromGD1RoleRecorded
  ∷ exactConstantsAndCZAndGD1ProofTermsRequiredRecorded
  ∷ clayPromotionBlockedRecorded
  ∷ failClosedRouteRecorded
  ∷ []

data NSGD1MinPrincipleNoLambda3CollapseBlocker : Set where
  NoLambda3CollapseOnKatoCarrier :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  LayerKornInequality :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  Lambda2ZeroBoundaryShapeOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  G12IdentityOnBiaxialCarrierOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  RellichStrainEvolutionOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  RellichKatoCommutatorProofTerm :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  LayerCZ :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  PressureCZIntegratedNotLInf :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  ViscousKatoGapCostNotDischarged :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  TwoRegimeLowerBoundShapePending :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  exactConstantsStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  GD1ProofTermsStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  hDelta1DischargeStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  q2UniformBoundFromGD1DischargeStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker

canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers :
  List NSGD1MinPrincipleNoLambda3CollapseBlocker
canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers =
  NoLambda3CollapseOnKatoCarrier
  ∷ LayerKornInequality
  ∷ Lambda2ZeroBoundaryShapeOpen
  ∷ G12IdentityOnBiaxialCarrierOpen
  ∷ RellichStrainEvolutionOpen
  ∷ RellichKatoCommutatorProofTerm
  ∷ LayerCZ
  ∷ PressureCZIntegratedNotLInf
  ∷ ViscousKatoGapCostNotDischarged
  ∷ TwoRegimeLowerBoundShapePending
  ∷ exactConstantsStillOpen
  ∷ GD1ProofTermsStillOpen
  ∷ hDelta1DischargeStillOpen
  ∷ q2UniformBoundFromGD1DischargeStillOpen
  ∷ []

canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames :
  List String
canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames =
  "D_t g12 >= g12^2(1-CCZ) - Cnu*g12"
  ∷ "gcrit = Cnu/(1-CCZ)"
  ∷ "surface shape: λ2=0 moving boundary"
  ∷ "on that boundary, λ3 = g12"
  ∷ "Rellich-Kato / strain evolution identity feed-through"
  ∷ "restoring g12^2 term retained in GD1 kernel"
  ∷ "pressure/CZ control entered as boundary integrated term, not pointwise L∞"
  ∷ "viscous Kato gap cost: Cnu * g12"
  ∷ "two-regime (supercritical/subcritical) Gronwall lower-bound shape"
  ∷ "LayerCZ exact-term shape and sign split are required"
  ∷ "supercritical restoring / subcritical exponential lower bound split"
  ∷ "lambda3 = g12 on biaxial carrier"
  ∷ "h_delta1 candidate route"
  ∷ "conditional TheoremG route"
  ∷ "Q2 route and denominator conversion lane"
  ∷ "Q2 uniform upper bound from GD1 (undischarged)"
  ∷ "exact constants"
  ∷ "CZ proof term"
  ∷ "GD1 proof terms"
  ∷ []

gd1MinimumPrincipleTextValue : String
gd1MinimumPrincipleTextValue =
  "D_t g12 >= g12^2(1-CCZ) - Cnu*g12"

criticalGapTextValue : String
criticalGapTextValue =
  "gcrit = Cnu/(1-CCZ)"

twoRegimeMinimumPrincipleTextValue : String
twoRegimeMinimumPrincipleTextValue =
  "two-regime minimum principle is conditional on exact constants, LayerCZ term, and GD1 proof terms"

lambda2BoundaryShapeTextValue : String
lambda2BoundaryShapeTextValue =
  "boundary shape: the Kato carrier is tracked on dOmega_K = {lambda2 = 0}, with biaxial reduction to the λ3-axis."

g12BoundaryIdentityTextValue : String
g12BoundaryIdentityTextValue =
  "on the biaxial carrier for the no-collapse argument, lambda3 is identified with g12 and denominator singularity is rewritten in g12."

rellichStrainEvolutionTextValue : String
rellichStrainEvolutionTextValue =
  "the GD1 numerator shape includes Rellich-Kato eigenframe evolution and strain transport terms, recorded as the explicit split source in the quotient derivative."

restoringG12SquareTextValue : String
restoringG12SquareTextValue =
  "restoring term keeps the g12^2 contribution with coefficient (1 - CCZ), not a pure linear Gronwall closure."

pressureCzIntegratedTextValue : String
pressureCzIntegratedTextValue =
  "pressure/CZ control is restricted to an integrated carrier boundary estimate, not a pointwise L∞_{x,t} assumption."

viscousKatoGapCostTextValue : String
viscousKatoGapCostTextValue =
  "viscous Kato gap cost is carried explicitly as a Cnu * g12 loss term in the GD1 lower-bound kernel."

twoRegimeLowerBoundTextValue : String
twoRegimeLowerBoundTextValue =
  "two-regime Gronwall lower-bound split: supercritical restoring versus subcritical exponential decay at rate Cnu."

supercriticalRestoringTextValue : String
supercriticalRestoringTextValue =
  "supercritical regime: restoring"

subcriticalExponentialLowerBoundTextValue : String
subcriticalExponentialLowerBoundTextValue =
  "subcritical regime: exponential lower bound"

lambda3OnBiaxialCarrierTextValue : String
lambda3OnBiaxialCarrierTextValue =
  "lambda3 = g12 on biaxial carrier"

hDelta1CandidateTextValue : String
hDelta1CandidateTextValue =
  "h_delta1 candidate is recorded and marked route-visible"

hDelta1RouteVisibilityTextValue : String
hDelta1RouteVisibilityTextValue =
  "h_delta1 route visibility is recorded as an explicit checked true gate"

theoremGRouteVisibilityTextValue : String
theoremGRouteVisibilityTextValue =
  "TheoremG route is recorded as conditional and route-visible"

q2RouteVisibilityTextValue : String
q2RouteVisibilityTextValue =
  "Q2 route is recorded as conditional and route-visible"

q2UniformBoundFromGD1TextValue : String
q2UniformBoundFromGD1TextValue =
  "GD1 is the intended route to the Q2 uniform upper bound from conditional TheoremG, but that gate is not discharged"

exactConstantsCZGD1RequiredTextValue : String
exactConstantsCZGD1RequiredTextValue =
  "exact constants, CZ term, and GD1 proof terms are still open; they are required before collapseImpossible, hDelta1, and Q2-uniform routes can be promoted"

contradictionRouteTextValue : String
contradictionRouteTextValue =
  "TheoremG + Q2 + GD1 lane is recorded to convert conditional estimates into a uniform Q2 upper bound; full discharge is explicit and currently absent"

failClosedRouteTextValue : String
failClosedRouteTextValue =
  "fail-closed route only: h_delta1, Q2-uniform-from-GD1, collapseImpossible, and Clay are all explicitly not discharged/promotion false"

kernelBoundaryPressureProfileTextValue : String
kernelBoundaryPressureProfileTextValue =
  "kernel-profile: λ2=0 carrier + λ3=g12, Rellich/strain evolution, restoring g12^2, and integrated pressure-CZ + viscous Kato shaping"

kernelGateTextValue : String
kernelGateTextValue =
  "gates: surface reduction and identity, Rellich+strain recording, two-regime lower-bound shape, and integrated (not pointwise) pressure-CZ channel are all visible"

receiptBoundaryText : List String
receiptBoundaryText =
  "GD1 two-regime minimum principle on Kato carrier is recorded"
  ∷ "exact constants / LayerCZ / GD1 proof terms are open blockers"
  ∷ "h_delta1 candidate and route visibility are recorded as true"
  ∷ "TheoremG route visibility is recorded as conditional"
  ∷ "Q2 route visibility is recorded as conditional"
  ∷ "uniform Q2 upper bound from GD1 remains undischarged"
  ∷ "the conditional contradiction channel needs that Q2-discharge to move from conditional to unconditional"
  ∷ "collapseImpossible is false on this receipt"
  ∷ "Clay Navier-Stokes promotion is false on this receipt"
  ∷ "surface dOmega_K = {lambda2 = 0}, g12=lambda3, Rellich/strain evolution, and pressure-CZ integrated shape are explicitly included in the kernel"
  ∷ "two-regime Gronwall lower-bound shape is split and the viscous Kato gap cost is explicit"
  ∷ []

record NSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger : Set where
  field
    lambda2BoundaryShapeText :
      String
    lambda2BoundaryShapeTextIsCanonical :
      lambda2BoundaryShapeText ≡ lambda2BoundaryShapeTextValue

    g12BoundaryIdentityText :
      String
    g12BoundaryIdentityTextIsCanonical :
      g12BoundaryIdentityText ≡ g12BoundaryIdentityTextValue

    rellichStrainEvolutionText :
      String
    rellichStrainEvolutionTextIsCanonical :
      rellichStrainEvolutionText ≡ rellichStrainEvolutionTextValue

    restoringG12SquareText :
      String
    restoringG12SquareTextIsCanonical :
      restoringG12SquareText ≡ restoringG12SquareTextValue

    pressureCZIntegratedText :
      String
    pressureCZIntegratedTextIsCanonical :
      pressureCZIntegratedText ≡ pressureCzIntegratedTextValue

    viscousKatoGapCostText :
      String
    viscousKatoGapCostTextIsCanonical :
      viscousKatoGapCostText ≡ viscousKatoGapCostTextValue

    twoRegimeLowerBoundText :
      String
    twoRegimeLowerBoundTextIsCanonical :
      twoRegimeLowerBoundText ≡ twoRegimeLowerBoundTextValue

    kernelBoundaryPressureProfileText :
      String
    kernelBoundaryPressureProfileTextIsCanonical :
      kernelBoundaryPressureProfileText ≡ kernelBoundaryPressureProfileTextValue

    kernelGateText :
      String
    kernelGateTextIsCanonical :
      kernelGateText ≡ kernelGateTextValue

canonicalNSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger :
  NSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger
canonicalNSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger =
  record
    { lambda2BoundaryShapeText =
        lambda2BoundaryShapeTextValue
    ; lambda2BoundaryShapeTextIsCanonical =
        refl
    ; g12BoundaryIdentityText =
        g12BoundaryIdentityTextValue
    ; g12BoundaryIdentityTextIsCanonical =
        refl
    ; rellichStrainEvolutionText =
        rellichStrainEvolutionTextValue
    ; rellichStrainEvolutionTextIsCanonical =
        refl
    ; restoringG12SquareText =
        restoringG12SquareTextValue
    ; restoringG12SquareTextIsCanonical =
        refl
    ; pressureCZIntegratedText =
        pressureCzIntegratedTextValue
    ; pressureCZIntegratedTextIsCanonical =
        refl
    ; viscousKatoGapCostText =
        viscousKatoGapCostTextValue
    ; viscousKatoGapCostTextIsCanonical =
        refl
    ; twoRegimeLowerBoundText =
        twoRegimeLowerBoundTextValue
    ; twoRegimeLowerBoundTextIsCanonical =
        refl
    ; kernelBoundaryPressureProfileText =
        kernelBoundaryPressureProfileTextValue
    ; kernelBoundaryPressureProfileTextIsCanonical =
        refl
    ; kernelGateText =
        kernelGateTextValue
    ; kernelGateTextIsCanonical =
        refl
    }

record NSGD1MinPrincipleNoLambda3CollapseKernelGateLedger : Set where
  field
    lambda2BoundaryShapeRecorded :
      Bool
    lambda2BoundaryShapeRecordedIsTrue :
      lambda2BoundaryShapeRecorded ≡ true

    g12OnBiaxialCarrierGateRecorded :
      Bool
    g12OnBiaxialCarrierGateRecordedIsTrue :
      g12OnBiaxialCarrierGateRecorded ≡ true

    rellichStrainEvolutionGateRecorded :
      Bool
    rellichStrainEvolutionGateRecordedIsTrue :
      rellichStrainEvolutionGateRecorded ≡ true

    restoringG12SquareGateRecorded :
      Bool
    restoringG12SquareGateRecordedIsTrue :
      restoringG12SquareGateRecorded ≡ true

    pressureCZIntegratedChannelRecorded :
      Bool
    pressureCZIntegratedChannelRecordedIsTrue :
      pressureCZIntegratedChannelRecorded ≡ true

    pressureCzLInfNotAssumed :
      Bool
    pressureCzLInfNotAssumedIsFalse :
      pressureCzLInfNotAssumed ≡ false

    viscousKatoGapCostGateRecorded :
      Bool
    viscousKatoGapCostGateRecordedIsTrue :
      viscousKatoGapCostGateRecorded ≡ true

    twoRegimeLowerBoundSplitRecorded :
      Bool
    twoRegimeLowerBoundSplitRecordedIsTrue :
      twoRegimeLowerBoundSplitRecorded ≡ true

canonicalNSGD1MinPrincipleNoLambda3CollapseKernelGateLedger :
  NSGD1MinPrincipleNoLambda3CollapseKernelGateLedger
canonicalNSGD1MinPrincipleNoLambda3CollapseKernelGateLedger =
  record
    { lambda2BoundaryShapeRecorded =
        true
    ; lambda2BoundaryShapeRecordedIsTrue =
        refl
    ; g12OnBiaxialCarrierGateRecorded =
        true
    ; g12OnBiaxialCarrierGateRecordedIsTrue =
        refl
    ; rellichStrainEvolutionGateRecorded =
        true
    ; rellichStrainEvolutionGateRecordedIsTrue =
        refl
    ; restoringG12SquareGateRecorded =
        true
    ; restoringG12SquareGateRecordedIsTrue =
        refl
    ; pressureCZIntegratedChannelRecorded =
        true
    ; pressureCZIntegratedChannelRecordedIsTrue =
        refl
    ; pressureCzLInfNotAssumed =
        false
    ; pressureCzLInfNotAssumedIsFalse =
        refl
    ; viscousKatoGapCostGateRecorded =
        true
    ; viscousKatoGapCostGateRecordedIsTrue =
        refl
    ; twoRegimeLowerBoundSplitRecorded =
        true
    ; twoRegimeLowerBoundSplitRecordedIsTrue =
        refl
    }

data NSGD1MinPrincipleNoLambda3CollapsePromotion : Set where

promotionEmptyTypeWitness : NSGD1MinPrincipleNoLambda3CollapsePromotion → ⊥
promotionEmptyTypeWitness ()

record NSGD1MinPrincipleNoLambda3CollapseReceipt : Setω where
  field
    status :
      NSGD1MinPrincipleNoLambda3CollapseStatus
    statusIsCanonical :
      status ≡ gd1MinimumPrincipleReceiptRecorded

    stageLedger :
      List NSGD1MinPrincipleNoLambda3CollapseStage
    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseStages

    kernelShapeProofLedger :
      NSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger
    kernelShapeProofLedgerIsCanonical :
      kernelShapeProofLedger ≡
      canonicalNSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger

    kernelGateLedger :
      NSGD1MinPrincipleNoLambda3CollapseKernelGateLedger
    kernelGateLedgerIsCanonical :
      kernelGateLedger ≡
      canonicalNSGD1MinPrincipleNoLambda3CollapseKernelGateLedger

    dependencyNames :
      List String
    dependencyNamesIsCanonical :
      dependencyNames
      ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames

    dependencyNameCount :
      Nat
    dependencyNameCountIsCanonical :
      dependencyNameCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames

    blockerLedger :
      List NSGD1MinPrincipleNoLambda3CollapseBlocker
    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers

    gd1MinimumPrincipleText :
      String
    gd1MinimumPrincipleTextIsCanonical :
      gd1MinimumPrincipleText ≡ gd1MinimumPrincipleTextValue

    criticalGapText :
      String
    criticalGapTextIsCanonical :
      criticalGapText ≡ criticalGapTextValue

    twoRegimeMinimumPrincipleText :
      String
    twoRegimeMinimumPrincipleTextIsCanonical :
      twoRegimeMinimumPrincipleText ≡ twoRegimeMinimumPrincipleTextValue

    supercriticalRestoringText :
      String
    supercriticalRestoringTextIsCanonical :
      supercriticalRestoringText ≡ supercriticalRestoringTextValue

    subcriticalExponentialLowerBoundText :
      String
    subcriticalExponentialLowerBoundTextIsCanonical :
      subcriticalExponentialLowerBoundText
      ≡ subcriticalExponentialLowerBoundTextValue

    lambda3OnBiaxialCarrierText :
      String
    lambda3OnBiaxialCarrierTextIsCanonical :
      lambda3OnBiaxialCarrierText ≡ lambda3OnBiaxialCarrierTextValue

    hDelta1CandidateText :
      String
    hDelta1CandidateTextIsCanonical :
      hDelta1CandidateText ≡ hDelta1CandidateTextValue

    hDelta1RouteVisibilityText :
      String
    hDelta1RouteVisibilityTextIsCanonical :
      hDelta1RouteVisibilityText ≡ hDelta1RouteVisibilityTextValue

    theoremGRouteVisibilityText :
      String
    theoremGRouteVisibilityTextIsCanonical :
      theoremGRouteVisibilityText ≡ theoremGRouteVisibilityTextValue

    q2RouteVisibilityText :
      String
    q2RouteVisibilityTextIsCanonical :
      q2RouteVisibilityText ≡ q2RouteVisibilityTextValue

    theoremGQ2GD1ContradictionRouteText :
      String
    theoremGQ2GD1ContradictionRouteTextIsCanonical :
      theoremGQ2GD1ContradictionRouteText ≡ contradictionRouteTextValue

    q2UniformBoundFromGD1Text :
      String
    q2UniformBoundFromGD1TextIsCanonical :
      q2UniformBoundFromGD1Text ≡ q2UniformBoundFromGD1TextValue

    exactConstantsCZGD1RequiredText :
      String
    exactConstantsCZGD1RequiredTextIsCanonical :
      exactConstantsCZGD1RequiredText
      ≡ exactConstantsCZGD1RequiredTextValue

    hDelta1Candidate :
      Bool
    hDelta1CandidateIsTrue :
      hDelta1Candidate ≡ true

    hDelta1RouteVisible :
      Bool
    hDelta1RouteVisibleIsTrue :
      hDelta1RouteVisible ≡ true

    theoremGRouteVisible :
      Bool
    theoremGRouteVisibleIsTrue :
      theoremGRouteVisible ≡ true

    q2RouteVisible :
      Bool
    q2RouteVisibleIsTrue :
      q2RouteVisible ≡ true

    exactConstantsDischarged :
      Bool
    exactConstantsDischargedIsFalse :
      exactConstantsDischarged ≡ false

    layerCZDischarged :
      Bool
    layerCZDischargedIsFalse :
      layerCZDischarged ≡ false

    gd1ProofTermsDischarged :
      Bool
    gd1ProofTermsDischargedIsFalse :
      gd1ProofTermsDischarged ≡ false

    hDelta1Discharged :
      Bool
    hDelta1DischargedIsFalse :
      hDelta1Discharged ≡ false

    q2UniformBoundFromGD1Discharged :
      Bool
    q2UniformBoundFromGD1DischargedIsFalse :
      q2UniformBoundFromGD1Discharged ≡ false

    collapseImpossible :
      Bool
    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionType :
      NSGD1MinPrincipleNoLambda3CollapsePromotion → ⊥
    promotionTypeIsCanonical :
      promotionType ≡ promotionEmptyTypeWitness

    failClosedRouteText :
      String
    failClosedRouteTextIsCanonical :
      failClosedRouteText ≡ failClosedRouteTextValue

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open NSGD1MinPrincipleNoLambda3CollapseReceipt public

canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt :
  NSGD1MinPrincipleNoLambda3CollapseReceipt
canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt =
  record
    { status =
        gd1MinimumPrincipleReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseStages
    ; stageLedgerIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseStages
    ; stageCountIsCanonical =
        refl
    ; dependencyNames =
        canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames
    ; dependencyNamesIsCanonical =
        refl
    ; dependencyNameCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames
    ; dependencyNameCountIsCanonical =
        refl
    ; blockerLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers
    ; blockerCountIsCanonical =
        refl
    ; kernelShapeProofLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseKernelShapeProofLedger
    ; kernelShapeProofLedgerIsCanonical =
        refl
    ; kernelGateLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseKernelGateLedger
    ; kernelGateLedgerIsCanonical =
        refl
    ; gd1MinimumPrincipleText =
        gd1MinimumPrincipleTextValue
    ; gd1MinimumPrincipleTextIsCanonical =
        refl
    ; criticalGapText =
        criticalGapTextValue
    ; criticalGapTextIsCanonical =
        refl
    ; twoRegimeMinimumPrincipleText =
        twoRegimeMinimumPrincipleTextValue
    ; twoRegimeMinimumPrincipleTextIsCanonical =
        refl
    ; supercriticalRestoringText =
        supercriticalRestoringTextValue
    ; supercriticalRestoringTextIsCanonical =
        refl
    ; subcriticalExponentialLowerBoundText =
        subcriticalExponentialLowerBoundTextValue
    ; subcriticalExponentialLowerBoundTextIsCanonical =
        refl
    ; lambda3OnBiaxialCarrierText =
        lambda3OnBiaxialCarrierTextValue
    ; lambda3OnBiaxialCarrierTextIsCanonical =
        refl
    ; hDelta1CandidateText =
        hDelta1CandidateTextValue
    ; hDelta1CandidateTextIsCanonical =
        refl
    ; hDelta1RouteVisibilityText =
        hDelta1RouteVisibilityTextValue
    ; hDelta1RouteVisibilityTextIsCanonical =
        refl
    ; theoremGRouteVisibilityText =
        theoremGRouteVisibilityTextValue
    ; theoremGRouteVisibilityTextIsCanonical =
        refl
    ; q2RouteVisibilityText =
        q2RouteVisibilityTextValue
    ; q2RouteVisibilityTextIsCanonical =
        refl
    ; theoremGQ2GD1ContradictionRouteText =
        contradictionRouteTextValue
    ; theoremGQ2GD1ContradictionRouteTextIsCanonical =
        refl
    ; q2UniformBoundFromGD1Text =
        q2UniformBoundFromGD1TextValue
    ; q2UniformBoundFromGD1TextIsCanonical =
        refl
    ; exactConstantsCZGD1RequiredText =
        exactConstantsCZGD1RequiredTextValue
    ; exactConstantsCZGD1RequiredTextIsCanonical =
        refl
    ; hDelta1Candidate =
        true
    ; hDelta1CandidateIsTrue =
        refl
    ; hDelta1RouteVisible =
        true
    ; hDelta1RouteVisibleIsTrue =
        refl
    ; theoremGRouteVisible =
        true
    ; theoremGRouteVisibleIsTrue =
        refl
    ; q2RouteVisible =
        true
    ; q2RouteVisibleIsTrue =
        refl
    ; exactConstantsDischarged =
        false
    ; exactConstantsDischargedIsFalse =
        refl
    ; layerCZDischarged =
        false
    ; layerCZDischargedIsFalse =
        refl
    ; gd1ProofTermsDischarged =
        false
    ; gd1ProofTermsDischargedIsFalse =
        refl
    ; hDelta1Discharged =
        false
    ; hDelta1DischargedIsFalse =
        refl
    ; q2UniformBoundFromGD1Discharged =
        false
    ; q2UniformBoundFromGD1DischargedIsFalse =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionType =
        promotionEmptyTypeWitness
    ; promotionTypeIsCanonical =
        refl
    ; failClosedRouteText =
        failClosedRouteTextValue
    ; failClosedRouteTextIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

gd1RouteKeepsCollapseImpossibleFalse :
  collapseImpossible canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsCollapseImpossibleFalse =
  refl

gd1RouteKeepsHDelta1DischargedFalse :
  hDelta1Discharged canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsHDelta1DischargedFalse =
  refl

gd1RouteKeepsQ2UniformBoundFromGD1DischargedFalse :
  q2UniformBoundFromGD1Discharged
    canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsQ2UniformBoundFromGD1DischargedFalse =
  refl

gd1RouteKeepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsClayNavierStokesPromotedFalse =
  refl
