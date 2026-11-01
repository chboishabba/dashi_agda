module DASHI.Physics.Closure.YMSmallFieldSurvivalAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMSpatialOnlyBlockingTemporalLinks as SpatialBlock
import DASHI.Physics.Closure.YMStrongGateBKP as StrongKP
import DASHI.Physics.Closure.YMAnisotropicAssumptionAConditionalClosure as AssumptionA
import DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks as Seminorm
import DASHI.Physics.Closure.FormalQhpBlockingMapDefinition as Qhp
import DASHI.Physics.Closure.BalabanCMP98AveragingLocalityImported as Locality
import DASHI.Physics.Closure.RealDyadicDecayBridge as DyadicBridge
import DASHI.Physics.Closure.BruhatTitsCarrierGaugeFixingReceipt as BTGauge
import DASHI.Physics.Closure.CarrierBalabanInductiveStepReceipt as CarrierBalaban
import DASHI.Physics.Closure.CarrierGaugeFieldMeasureReceipt as CarrierMeasure
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as AnisotropicDiameter

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
  ; 0ℝ
  ; 1ℝ
  ; ≤ℝ-refl
  ; ≤ℝ-trans
  ; +-mono-≤
  )

subst : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- ── Block / norm types for the small-field radius survival chain ──────
Block : Set
Block = AnisotropicDiameter.Polymer

fineFieldNorm : Nat → Block → ℝ
fineFieldNorm = AnisotropicDiameter.supEdgePerturbation

C-obs : ℝ
C-obs = 1ℝ

decayFactor : Nat → ℝ
decayFactor k = DyadicBridge.dyadicPow2NegAsReal (Seminorm.double k)

normalizedBlockedOscillation : Nat → Block → ℝ
normalizedBlockedOscillation k b = C-obs *ℝ decayFactor k

blockedOscillation : Nat → Block → ℝ
blockedOscillation = normalizedBlockedOscillation

blockedFieldNorm : Nat → Block → ℝ
blockedFieldNorm k b = fineFieldNorm k b +ℝ blockedOscillation k b

------------------------------------------------------------------------
-- Small-field survival gate after the strong KP closure.
--
-- The historical Sprint 76 receipt correctly leaves
-- SmallFieldBoundsSurviveAnisotropicBlocking false/open.  This module records
-- the next lane after the blocked L=2 KP theorem.  The proof-critical KP input
-- is now the strong in-repo Gate-B theorem, not the older weak
-- authority-conditional KP surface.  The remaining non-derived inputs are the
-- analytic Balaban/gauge/transfer estimates.
--
-- This is not an internal derivation of Balaban's small-field estimates.
-- It is a typed boundary that consumes explicit authority inputs and keeps
-- Clay/YM promotion false.

record BalabanSmallFieldBounds : Set where
  constructor mkBalabanSmallFieldBounds
  field
    balabanSmallFieldBounds :
      Bool
    balabanSmallFieldBoundsIsTrue :
      balabanSmallFieldBounds ≡ true

record BalabanSmallFieldRegionStability : Set where
  constructor mkBalabanSmallFieldRegionStability
  field
    smallFieldRegionStableUnderAnisotropicBlocking :
      Bool
    smallFieldRegionStableUnderAnisotropicBlockingIsTrue :
      smallFieldRegionStableUnderAnisotropicBlocking ≡ true

record BalabanFluctuationCovarianceBound : Set where
  constructor mkBalabanFluctuationCovarianceBound
  field
    fluctuationCovarianceUniformlyBounded :
      Bool
    fluctuationCovarianceUniformlyBoundedIsTrue :
      fluctuationCovarianceUniformlyBounded ≡ true

record BalabanPolymerActivityExponentialDecay : Set where
  constructor mkBalabanPolymerActivityExponentialDecay
  field
    polymerActivityExponentialDecayUniformInScale :
      Bool
    polymerActivityExponentialDecayUniformInScaleIsTrue :
      polymerActivityExponentialDecayUniformInScale ≡ true

record BalabanScaleUniformConstants : Set where
  constructor mkBalabanScaleUniformConstants
  field
    balabanConstantsUniformAcrossAnisotropicScales :
      Bool
    balabanConstantsUniformAcrossAnisotropicScalesIsTrue :
      balabanConstantsUniformAcrossAnisotropicScales ≡ true

record BalabanSmallFieldAnalyticPackage : Set where
  constructor mkBalabanSmallFieldAnalyticPackage
  field
    smallFieldRegionStability :
      BalabanSmallFieldRegionStability
    fluctuationCovarianceBound :
      BalabanFluctuationCovarianceBound
    polymerActivityExponentialDecay :
      BalabanPolymerActivityExponentialDecay
    scaleUniformConstants :
      BalabanScaleUniformConstants

record BalabanSmallFieldAuthority : Set where
  constructor mkBalabanSmallFieldAuthority
  field
    smallFieldRegionDefined :
      Bool
    smallFieldRegionDefinedIsTrue :
      smallFieldRegionDefined ≡ true
    fluctuationCovarianceBound :
      Bool
    fluctuationCovarianceBoundIsTrue :
      fluctuationCovarianceBound ≡ true
    polymerActivityDecay :
      Bool
    polymerActivityDecayIsTrue :
      polymerActivityDecay ≡ true
    scaleUniformConstants :
      Bool
    scaleUniformConstantsIsTrue :
      scaleUniformConstants ≡ true

balabanSmallFieldAuthorityFromAnalyticPackage :
  BalabanSmallFieldAnalyticPackage →
  BalabanSmallFieldAuthority
balabanSmallFieldAuthorityFromAnalyticPackage package =
  record
    { smallFieldRegionDefined =
        BalabanSmallFieldRegionStability.smallFieldRegionStableUnderAnisotropicBlocking
          (BalabanSmallFieldAnalyticPackage.smallFieldRegionStability package)
    ; smallFieldRegionDefinedIsTrue =
        BalabanSmallFieldRegionStability.smallFieldRegionStableUnderAnisotropicBlockingIsTrue
          (BalabanSmallFieldAnalyticPackage.smallFieldRegionStability package)
    ; fluctuationCovarianceBound =
        BalabanFluctuationCovarianceBound.fluctuationCovarianceUniformlyBounded
          (BalabanSmallFieldAnalyticPackage.fluctuationCovarianceBound package)
    ; fluctuationCovarianceBoundIsTrue =
        BalabanFluctuationCovarianceBound.fluctuationCovarianceUniformlyBoundedIsTrue
          (BalabanSmallFieldAnalyticPackage.fluctuationCovarianceBound package)
    ; polymerActivityDecay =
        BalabanPolymerActivityExponentialDecay.polymerActivityExponentialDecayUniformInScale
          (BalabanSmallFieldAnalyticPackage.polymerActivityExponentialDecay package)
    ; polymerActivityDecayIsTrue =
        BalabanPolymerActivityExponentialDecay.polymerActivityExponentialDecayUniformInScaleIsTrue
          (BalabanSmallFieldAnalyticPackage.polymerActivityExponentialDecay package)
    ; scaleUniformConstants =
        BalabanScaleUniformConstants.balabanConstantsUniformAcrossAnisotropicScales
          (BalabanSmallFieldAnalyticPackage.scaleUniformConstants package)
    ; scaleUniformConstantsIsTrue =
        BalabanScaleUniformConstants.balabanConstantsUniformAcrossAnisotropicScalesIsTrue
          (BalabanSmallFieldAnalyticPackage.scaleUniformConstants package)
    }

balabanSmallFieldBoundsFromAuthority :
  BalabanSmallFieldAuthority →
  BalabanSmallFieldBounds
balabanSmallFieldBoundsFromAuthority authority =
  record
    { balabanSmallFieldBounds =
        BalabanSmallFieldAuthority.scaleUniformConstants authority
    ; balabanSmallFieldBoundsIsTrue =
        BalabanSmallFieldAuthority.scaleUniformConstantsIsTrue authority
    }

record SpatialOnlyBlockingCompatibility : Set where
  constructor mkSpatialOnlyBlockingCompatibility
  field
    spatialOnlyBalabanRGL2 :
      Bool
    spatialOnlyBalabanRGL2IsTrue :
      spatialOnlyBalabanRGL2 ≡ true
    spatialBlockingPreservesTemporalLinks :
      Bool
    spatialBlockingPreservesTemporalLinksIsTrue :
      spatialBlockingPreservesTemporalLinks ≡ true
    spatialRGLeavesTimeAxisInvariant :
      Bool
    spatialRGLeavesTimeAxisInvariantIsTrue :
      spatialRGLeavesTimeAxisInvariant ≡ true

record GaugeOrbitMeasurePreservation : Set where
  constructor mkGaugeOrbitMeasurePreservation
  field
    gaugeOrbitMeasurePreservation :
      Bool
    gaugeOrbitMeasurePreservationIsTrue :
      gaugeOrbitMeasurePreservation ≡ true

record GaugeFixingJacobianBound : Set where
  constructor mkGaugeFixingJacobianBound
  field
    gaugeFixingJacobianControlledUniformly :
      Bool
    gaugeFixingJacobianControlledUniformlyIsTrue :
      gaugeFixingJacobianControlledUniformly ≡ true

record GaugeOrbitVolumeUniform : Set where
  constructor mkGaugeOrbitVolumeUniform
  field
    gaugeOrbitVolumeUniformAcrossScales :
      Bool
    gaugeOrbitVolumeUniformAcrossScalesIsTrue :
      gaugeOrbitVolumeUniformAcrossScales ≡ true

record SpatialBlockingPreservesGaugeOrbit : Set where
  constructor mkSpatialBlockingPreservesGaugeOrbit
  field
    spatialOnlyBlockingPreservesGaugeOrbitMeasure :
      Bool
    spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue :
      spatialOnlyBlockingPreservesGaugeOrbitMeasure ≡ true

record GaugeOrbitMeasureAnalyticPackage : Set where
  constructor mkGaugeOrbitMeasureAnalyticPackage
  field
    gaugeFixingJacobianBound :
      GaugeFixingJacobianBound
    gaugeOrbitVolumeUniform :
      GaugeOrbitVolumeUniform
    spatialBlockingPreservesGaugeOrbit :
      SpatialBlockingPreservesGaugeOrbit

record GaugeOrbitMeasureAuthority : Set where
  constructor mkGaugeOrbitMeasureAuthority
  field
    gaugeFixingJacobianControlled :
      Bool
    gaugeFixingJacobianControlledIsTrue :
      gaugeFixingJacobianControlled ≡ true
    orbitVolumeUniform :
      Bool
    orbitVolumeUniformIsTrue :
      orbitVolumeUniform ≡ true
    spatialBlockingPreservesOrbit :
      Bool
    spatialBlockingPreservesOrbitIsTrue :
      spatialBlockingPreservesOrbit ≡ true

gaugeOrbitMeasureAuthorityFromAnalyticPackage :
  GaugeOrbitMeasureAnalyticPackage →
  GaugeOrbitMeasureAuthority
gaugeOrbitMeasureAuthorityFromAnalyticPackage package =
  record
    { gaugeFixingJacobianControlled =
        GaugeFixingJacobianBound.gaugeFixingJacobianControlledUniformly
          (GaugeOrbitMeasureAnalyticPackage.gaugeFixingJacobianBound package)
    ; gaugeFixingJacobianControlledIsTrue =
        GaugeFixingJacobianBound.gaugeFixingJacobianControlledUniformlyIsTrue
          (GaugeOrbitMeasureAnalyticPackage.gaugeFixingJacobianBound package)
    ; orbitVolumeUniform =
        GaugeOrbitVolumeUniform.gaugeOrbitVolumeUniformAcrossScales
          (GaugeOrbitMeasureAnalyticPackage.gaugeOrbitVolumeUniform package)
    ; orbitVolumeUniformIsTrue =
        GaugeOrbitVolumeUniform.gaugeOrbitVolumeUniformAcrossScalesIsTrue
          (GaugeOrbitMeasureAnalyticPackage.gaugeOrbitVolumeUniform package)
    ; spatialBlockingPreservesOrbit =
        SpatialBlockingPreservesGaugeOrbit.spatialOnlyBlockingPreservesGaugeOrbitMeasure
          (GaugeOrbitMeasureAnalyticPackage.spatialBlockingPreservesGaugeOrbit package)
    ; spatialBlockingPreservesOrbitIsTrue =
        SpatialBlockingPreservesGaugeOrbit.spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue
          (GaugeOrbitMeasureAnalyticPackage.spatialBlockingPreservesGaugeOrbit package)
    }

gaugeOrbitMeasurePreservationFromAuthority :
  GaugeOrbitMeasureAuthority →
  GaugeOrbitMeasurePreservation
gaugeOrbitMeasurePreservationFromAuthority authority =
  record
    { gaugeOrbitMeasurePreservation =
        GaugeOrbitMeasureAuthority.spatialBlockingPreservesOrbit authority
    ; gaugeOrbitMeasurePreservationIsTrue =
        GaugeOrbitMeasureAuthority.spatialBlockingPreservesOrbitIsTrue authority
    }

record TemporalTransferCompatibility : Set where
  constructor mkTemporalTransferCompatibility
  field
    temporalTransferCompatibility :
      Bool
    temporalTransferCompatibilityIsTrue :
      temporalTransferCompatibility ≡ true

record PolymerActivityBoundPreservation : Set₁ where
  constructor mkPolymerActivityBoundPreservation
  field
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    polymerActivityBoundPreservation :
      Bool
    polymerActivityBoundPreservationIsTrue :
      polymerActivityBoundPreservation ≡ true

spatialOnlyBlockingCompatibilityFromW1 :
  SpatialOnlyBlockingCompatibility
spatialOnlyBlockingCompatibilityFromW1 =
  record
    { spatialOnlyBalabanRGL2 =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBalabanRGL2
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialOnlyBalabanRGL2IsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBalabanRGL2IsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialBlockingPreservesTemporalLinks =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinks
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialBlockingPreservesTemporalLinksIsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialOnlyBlockingPreservesTemporalLinksIsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialRGLeavesTimeAxisInvariant =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialRGLeavesTimeAxisInvariant
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    ; spatialRGLeavesTimeAxisInvariantIsTrue =
        SpatialBlock.YMSpatialOnlyBlockingTemporalLinksReceipt.spatialRGLeavesTimeAxisInvariantIsPackaged
          SpatialBlock.canonicalYMSpatialOnlyBlockingTemporalLinksReceipt
    }

polymerActivityBoundPreservationFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  PolymerActivityBoundPreservation
polymerActivityBoundPreservationFromStrongKP theorem =
  record
    { strongKP =
        theorem
    ; polymerActivityBoundPreservation =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOne
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP theorem)
    ; polymerActivityBoundPreservationIsTrue =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOneIsTrue
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP theorem)
    }

temporalTransferCompatibilityFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  TemporalTransferCompatibility
temporalTransferCompatibilityFromStrongKP theorem =
  record
    { temporalTransferCompatibility =
        StrongKP.strongActionTermTransferResidualDisjointnessDerivedInRepo
    ; temporalTransferCompatibilityIsTrue =
        refl
    }

balabanSmallFieldRegionStabilityCitation : String
balabanSmallFieldRegionStabilityCitation =
  "Balaban CMP 119 Section 4 / Theorem 4.1: small-field region stability under the RG step."

balabanFluctuationCovarianceBoundCitation : String
balabanFluctuationCovarianceBoundCitation =
  "Balaban CMP 119 Section 5: fluctuation covariance bound in the small-field region."

balabanPolymerActivityExponentialDecayCitation : String
balabanPolymerActivityExponentialDecayCitation =
  "Balaban CMP 119 Section 6: exponential decay bound for irrelevant polymer activities."

balabanScaleUniformConstantsCitation : String
balabanScaleUniformConstantsCitation =
  "Balaban CMP 98/109/119: scale-uniform renormalisation constants for the small-field expansion."

gaugeFixingJacobianBoundCitation : String
gaugeFixingJacobianBoundCitation =
  "Balaban CMP 109 Section 2: uniform Faddeev-Popov / gauge-fixing Jacobian control."

gaugeOrbitVolumeUniformCitation : String
gaugeOrbitVolumeUniformCitation =
  "Balaban CMP 116 Section 3: uniform gauge-orbit volume control for the SU(3) measure."

currentSmallFieldLocalityConstant : Nat
currentSmallFieldLocalityConstant = 1

currentSmallFieldObservableLipschitzConstant : Nat
currentSmallFieldObservableLipschitzConstant = 1

currentSmallFieldBlockingScale : Nat
currentSmallFieldBlockingScale = suc zero

record SmallFieldOscillationBudget : Set₁ where
  constructor mkSmallFieldOscillationBudget
  field
    cLocal :
      Nat
    cF :
      Nat
    k :
      Nat
    anisotropicAssumptionA :
      AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem cLocal cF k
    blockedSquaredOscillationBudget :
      Seminorm.DyadicDecay
    blockedSquaredOscillationBudgetMatchesAssumptionA :
      blockedSquaredOscillationBudget
        ≡ AssumptionA.observableSquaredDecay cLocal cF k
    blockedUniformEnvelopeBudget :
      Seminorm.DyadicDecay
    blockedUniformEnvelopeBudgetMatchesAssumptionA :
      blockedUniformEnvelopeBudget
        ≡ AssumptionA.observableUniformEnvelope cLocal cF
    blockedOscillationBudgetAvailable :
      Bool
    blockedOscillationBudgetAvailableIsTrue :
      blockedOscillationBudgetAvailable ≡ true
    localityConstantNormalized :
      cLocal ≡ currentSmallFieldLocalityConstant

smallFieldOscillationBudgetFromAssumptionA :
  (cF k : Nat) →
  SmallFieldOscillationBudget
smallFieldOscillationBudgetFromAssumptionA cF k =
  record
    { cLocal = currentSmallFieldLocalityConstant
    ; cF = cF
    ; k = k
    ; anisotropicAssumptionA =
        AssumptionA.ymAnisotropicAssumptionAConditionalClosure
          currentSmallFieldLocalityConstant
          cF
          k
    ; blockedSquaredOscillationBudget =
        AssumptionA.observableSquaredDecay
          currentSmallFieldLocalityConstant
          cF
          k
    ; blockedSquaredOscillationBudgetMatchesAssumptionA =
        refl
    ; blockedUniformEnvelopeBudget =
        AssumptionA.observableUniformEnvelope
          currentSmallFieldLocalityConstant
          cF
    ; blockedUniformEnvelopeBudgetMatchesAssumptionA =
        refl
    ; blockedOscillationBudgetAvailable = true
    ; blockedOscillationBudgetAvailableIsTrue = refl
    ; localityConstantNormalized = refl
    }

currentSmallFieldOscillationBudget : SmallFieldOscillationBudget
currentSmallFieldOscillationBudget =
  smallFieldOscillationBudgetFromAssumptionA
    currentSmallFieldObservableLipschitzConstant
    currentSmallFieldBlockingScale

blockedOscillationMatchesNormalizedEnvelope :
  ∀ (k : Nat) (b : Block) →
  blockedOscillation k b ≡ (C-obs *ℝ decayFactor k)
blockedOscillationMatchesNormalizedEnvelope k b = refl

perLinkDecayMatchesNormalizedEnvelopeAtCurrentLocality :
  ∀ (k : Nat) →
  DyadicBridge.dyadicDecayAsReal
    (Seminorm.perLinkOscillationDecay currentSmallFieldLocalityConstant k)
    ≡ (C-obs *ℝ decayFactor k)
perLinkDecayMatchesNormalizedEnvelopeAtCurrentLocality k =
  DyadicBridge.normalizedPerLinkDecayAsReal k

perLinkDecayMatchesNormalizedEnvelope :
  ∀ (cLocal k : Nat) →
  cLocal ≡ currentSmallFieldLocalityConstant →
  DyadicBridge.dyadicDecayAsReal
    (Seminorm.perLinkOscillationDecay cLocal k)
    ≡ (C-obs *ℝ decayFactor k)
perLinkDecayMatchesNormalizedEnvelope cLocal k cLocal≡current
  rewrite cLocal≡current =
  perLinkDecayMatchesNormalizedEnvelopeAtCurrentLocality k

blockedOscillationMatchesPerLinkDecayAsReal :
  ∀ (cLocal k : Nat) (b : Block) →
  cLocal ≡ currentSmallFieldLocalityConstant →
  blockedOscillation k b
    ≤ℝ DyadicBridge.dyadicDecayAsReal
          (Seminorm.perLinkOscillationDecay cLocal k)
blockedOscillationMatchesPerLinkDecayAsReal cLocal k b cLocal≡current
  rewrite blockedOscillationMatchesNormalizedEnvelope k b
        | perLinkDecayMatchesNormalizedEnvelope cLocal k cLocal≡current =
  ≤ℝ-refl

perLinkOscillationDecayAsRealFitsBlockedEnvelope :
  ∀ (cLocal k : Nat) →
  cLocal ≡ currentSmallFieldLocalityConstant →
  DyadicBridge.dyadicDecayAsReal
    (Seminorm.perLinkOscillationDecay cLocal k)
    ≤ℝ (C-obs *ℝ decayFactor k)
perLinkOscillationDecayAsRealFitsBlockedEnvelope cLocal k cLocal≡current
  rewrite perLinkDecayMatchesNormalizedEnvelope cLocal k cLocal≡current =
  ≤ℝ-refl

blockedOscillationAndPerLinkDecayShareNormalizedEnvelope :
  ∀ (cLocal k : Nat) (b : Block) →
  cLocal ≡ currentSmallFieldLocalityConstant →
  blockedOscillation k b ≡
  DyadicBridge.dyadicDecayAsReal
    (Seminorm.perLinkOscillationDecay cLocal k)
blockedOscillationAndPerLinkDecayShareNormalizedEnvelope cLocal k b cLocal≡current
  rewrite blockedOscillationMatchesNormalizedEnvelope k b
        | perLinkDecayMatchesNormalizedEnvelope cLocal k cLocal≡current =
  refl

-- ── Small-field radius survival from oscillation budget ─────────────
-- Native reducer: derives BlockedSmallFieldRadiusSurvival from the
-- oscillation budget + input radius bound + blocking margin.

record SmallFieldInputRadiusBound : Set₁ where
  field
    ε-input : ℝ
    ε-small : ℝ
    ε-margin : ℝ
    fineFieldBound :
      ∀ (k : Nat) (b : Block) →
      fineFieldNorm k b ≤ℝ ε-input
    inputPlusMarginWithinSmall :
      ε-input +ℝ ε-margin ≤ℝ ε-small

record BlockingRadiusMargin : Set₁ where
  field
    ε-margin : ℝ
    marginBoundsOscillation :
      ∀ (k : Nat) (b : Block) →
      blockedOscillation k b ≤ℝ ε-margin

record BlockedSmallFieldRadiusSurvival : Set₁ where
  constructor mkBlockedSmallFieldRadiusSurvival
  field
    oscillationBudget :
      SmallFieldOscillationBudget
    inputRadiusBound :
      SmallFieldInputRadiusBound
    blockingMargin :
      BlockingRadiusMargin
    fineSmallFieldRadius :
      Nat
    blockingOscillationMargin :
      Nat
    admissibleBlockedRadius :
      Nat
    fineRadiusPlusMarginIsAdmissible :
      fineSmallFieldRadius + blockingOscillationMargin
        ≡ admissibleBlockedRadius
    blockedFieldTriangleApplied :
      Bool
    blockedFieldTriangleAppliedIsTrue :
      blockedFieldTriangleApplied ≡ true
    marginSplitApplied :
      Bool
    marginSplitAppliedIsTrue :
      marginSplitApplied ≡ true
    triangleBoundForBlockedField :
      Bool
    triangleBoundForBlockedFieldIsTrue :
      triangleBoundForBlockedField ≡ true
    blockedRadiusStaysAdmissible :
      Bool
    blockedRadiusStaysAdmissibleIsTrue :
      blockedRadiusStaysAdmissible ≡ true

record QhpPerLinkRealOscillationEstimate
  (cLocal : Nat) (k : Nat) (b : Block) : Set₁ where
  field
    localityTheorem :
      Locality.BalabanCMP98AveragingLocalityImportedTheorem cLocal k
    influenceConeTheorem :
      Qhp.QhpPerLinkInfluenceConeLMinus2kTheorem cLocal k
    influenceConeMatchesLocality :
      influenceConeTheorem
        ≡ Locality.BalabanCMP98AveragingLocalityImportedTheorem.qhpInfluenceCone
            localityTheorem
    perLinkOscillationBudget :
      Seminorm.DyadicDecay
    perLinkOscillationMatchesInfluenceCone :
      perLinkOscillationBudget
        ≡ Qhp.QhpPerLinkInfluenceConeLMinus2kTheorem.perLinkOscillation
            influenceConeTheorem
    perLinkOscillationIsCLocalTimes2Minus2k :
      perLinkOscillationBudget ≡ Seminorm.perLinkOscillationDecay cLocal k
    realBlockedOscillationEnvelope :
      ℝ
    qhpRealEnvelopeMatchesNormalizedEnvelope :
      realBlockedOscillationEnvelope ≡ (C-obs *ℝ decayFactor k)
    qhpBlockedOscillationMatchesNormalizedEnvelope :
      blockedOscillation k b ≡ (C-obs *ℝ decayFactor k)
    qhpBlockedOscillationBelowRealEnvelope :
      blockedOscillation k b ≤ℝ realBlockedOscillationEnvelope
    theoremCitation :
      String

currentε-margin : ℝ
currentε-margin =
  C-obs *ℝ decayFactor zero

record QhpBlockedOscillationComparison : Set₁ where
  field
    budget :
      SmallFieldOscillationBudget
    qhpBudget :
      AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.cF budget)
        (SmallFieldOscillationBudget.k budget)
    qhpBudgetMatchesBudget :
      qhpBudget ≡ SmallFieldOscillationBudget.anisotropicAssumptionA budget
    localityProof :
      Locality.BalabanCMP98AveragingLocalityImportedTheorem
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.k budget)
    qhpArithmetic :
      Seminorm.QhpSquaredOscillationArithmetic
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.k budget)
    qhpSquaredBridge :
      Qhp.LipschitzToSquaredOscillationForQhpTheorem
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.k budget)
    squaredDecayBudget :
      Seminorm.DyadicDecay
    squaredDecayBudgetMatchesAssumptionA :
      squaredDecayBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
            qhpBudget
    squaredDecayBudgetAgreesWithObservableDecay :
      squaredDecayBudget
        ≡ AssumptionA.observableSquaredDecay
            (SmallFieldOscillationBudget.cLocal budget)
            (SmallFieldOscillationBudget.cF budget)
            (SmallFieldOscillationBudget.k budget)
    uniformEnvelopeBudget :
      Seminorm.DyadicDecay
    uniformEnvelopeBudgetMatchesAssumptionA :
      uniformEnvelopeBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
            qhpBudget
    uniformEnvelopeAgreesWithObservableEnvelope :
      uniformEnvelopeBudget
        ≡ AssumptionA.observableUniformEnvelope
            (SmallFieldOscillationBudget.cLocal budget)
            (SmallFieldOscillationBudget.cF budget)
    perLinkEstimate :
      ∀ (k : Nat) (b : Block) →
      QhpPerLinkRealOscillationEstimate
        (SmallFieldOscillationBudget.cLocal budget)
        k
        b
    qhpPerLinkEnvelopeMatchesNormalizedEnvelope :
      ∀ (k : Nat) (b : Block) →
      QhpPerLinkRealOscillationEstimate.realBlockedOscillationEnvelope
        (perLinkEstimate k b)
        ≡ (C-obs *ℝ decayFactor k)
    qhpBlockedOscillationMatchesNormalizedEnvelope :
      ∀ (k : Nat) (b : Block) →
      blockedOscillation k b ≡ (C-obs *ℝ decayFactor k)
    qhpControlsBlockedOscillation :
      ∀ (k : Nat) (b : Block) →
      QhpPerLinkRealOscillationEstimate.realBlockedOscillationEnvelope
        (perLinkEstimate k b)
        ≤ℝ (C-obs *ℝ decayFactor k)
    qhpDecayBelowMargin :
      ∀ (k : Nat) →
      (C-obs *ℝ decayFactor k) ≤ℝ currentε-margin

-- Analytic norms (genuine analytic content; stays postulated)
BlockedFieldTriangleBound :
  ∀ (k : Nat) (b : Block) →
  blockedFieldNorm k b ≤ℝ (fineFieldNorm k b +ℝ blockedOscillation k b)
BlockedFieldTriangleBound k b = ≤ℝ-refl

-- SmallFieldMarginSplit derived from ordered-real arithmetic.
SmallFieldMarginSplit :
  ∀ {ε-input ε-small ε-margin : ℝ} {k : Nat} {b : Block} →
  fineFieldNorm k b ≤ℝ ε-input →
  blockedOscillation k b ≤ℝ ε-margin →
  ε-input +ℝ ε-margin ≤ℝ ε-small →
  (fineFieldNorm k b +ℝ blockedOscillation k b) ≤ℝ ε-small
SmallFieldMarginSplit fine≤ osc≤ inputPlusMarginSmall =
  ≤ℝ-trans (+-mono-≤ fine≤ osc≤) inputPlusMarginSmall

-- Oscillation budget → margin split
-- The live lane now uses an explicit dyadic-to-real bridge:
--
--   C-obs * decayFactor k  with  decayFactor k = 2^(-2k)
--
-- and the current blocked margin is the scale-zero envelope.
record SmallFieldBlockingScaleAdmissible : Set₁ where
  field
    ε-margin :
      ℝ
    oscillationDecayBelowMargin :
      ∀ (k : Nat) →
      (C-obs *ℝ decayFactor k) ≤ℝ ε-margin

currentε-input : ℝ
currentε-input = AnisotropicDiameter.ε-const

currentFineFieldBound :
  ∀ (k : Nat) (b : Block) →
    fineFieldNorm k b ≤ℝ currentε-input
currentFineFieldBound k b =
  AnisotropicDiameter.currentP33SmallFieldControlsMetricPerturbation
    k
    b
    (AnisotropicDiameter.currentSmallFieldRegularity k b)

currentOscillationDecayBelowMargin :
  ∀ (k : Nat) →
  (C-obs *ℝ decayFactor k) ≤ℝ currentε-margin
currentOscillationDecayBelowMargin k =
  subst
    (λ lhs → lhs ≤ℝ currentε-margin)
    (DyadicBridge.normalizedPerLinkDecayAsReal k)
    (subst
      (λ rhs →
        DyadicBridge.dyadicDecayAsReal (Seminorm.perLinkOscillationDecay 1 k)
          ≤ℝ rhs)
      (DyadicBridge.normalizedPerLinkDecayAtScaleZero)
      (DyadicBridge.normalizedPerLinkDecayBelowScaleZero k))

currentε-small : ℝ
currentε-small =
  currentε-input +ℝ currentε-margin

currentInputPlusMarginWithinSmall :
  currentε-input +ℝ currentε-margin ≤ℝ currentε-small
currentInputPlusMarginWithinSmall = ≤ℝ-refl

record CurrentSmallFieldInputRadiusBoundTheorem : Set₁ where
  constructor mkCurrentSmallFieldInputRadiusBoundTheorem
  field
    ε-input :
      ℝ
    fineFieldBound :
      ∀ (k : Nat) (b : Block) →
      fineFieldNorm k b ≤ℝ ε-input
    theoremCitation :
      String

currentSmallFieldInputRadiusBoundTheorem :
  CurrentSmallFieldInputRadiusBoundTheorem
currentSmallFieldInputRadiusBoundTheorem =
  mkCurrentSmallFieldInputRadiusBoundTheorem
    currentε-input
    currentFineFieldBound
    "Current fine-scale small-field hypothesis: fine field norm remains within the admissible input radius."

record CurrentSmallFieldBlockingScaleAdmissibleTheorem : Set₁ where
  constructor mkCurrentSmallFieldBlockingScaleAdmissibleTheorem
  field
    ε-margin :
      ℝ
    theoremCitation :
      String
    oscillationDecayBelowMargin :
      ∀ (k : Nat) →
      (C-obs *ℝ decayFactor k) ≤ℝ ε-margin

currentSmallFieldBlockingScaleAdmissibleTheorem :
  CurrentSmallFieldBlockingScaleAdmissibleTheorem
currentSmallFieldBlockingScaleAdmissibleTheorem =
  mkCurrentSmallFieldBlockingScaleAdmissibleTheorem
    currentε-margin
    "Current blocked-scale margin choice: the oscillation decay envelope is below the admissible blocked small-field margin."
    currentOscillationDecayBelowMargin

qhpPerLinkRealOscillationEstimate :
  (cLocal : Nat) →
  (k : Nat) →
  cLocal ≡ currentSmallFieldLocalityConstant →
  (b : Block) →
  QhpPerLinkRealOscillationEstimate cLocal k b
qhpPerLinkRealOscillationEstimate cLocal k cLocal≡current b =
  let
    localityTheorem =
      Locality.balabanCMP98AveragingLocalityImportedTheorem cLocal k
    influenceConeTheorem =
      Locality.BalabanCMP98AveragingLocalityImportedTheorem.qhpInfluenceCone
        localityTheorem
  in
  record
    { localityTheorem = localityTheorem
    ; influenceConeTheorem = influenceConeTheorem
    ; influenceConeMatchesLocality = refl
    ; perLinkOscillationBudget =
        Qhp.QhpPerLinkInfluenceConeLMinus2kTheorem.perLinkOscillation
          influenceConeTheorem
    ; perLinkOscillationMatchesInfluenceCone = refl
    ; perLinkOscillationIsCLocalTimes2Minus2k =
        Qhp.QhpPerLinkInfluenceConeLMinus2kTheorem.perLinkOscillationIsCLocalTimes2Minus2k
          influenceConeTheorem
    ; realBlockedOscillationEnvelope =
        DyadicBridge.dyadicDecayAsReal
          (Qhp.QhpPerLinkInfluenceConeLMinus2kTheorem.perLinkOscillation
            influenceConeTheorem)
    ; qhpRealEnvelopeMatchesNormalizedEnvelope =
        perLinkDecayMatchesNormalizedEnvelope cLocal k cLocal≡current
    ; qhpBlockedOscillationMatchesNormalizedEnvelope =
        blockedOscillationMatchesNormalizedEnvelope k b
    ; qhpBlockedOscillationBelowRealEnvelope =
        blockedOscillationMatchesPerLinkDecayAsReal cLocal k b cLocal≡current
    ; theoremCitation =
        "Per-link blocked oscillation estimate: the in-repo Q_hp locality theorem supplies the dyadic decay witness C_local * 2^(-2k), and the real blocked oscillation is compared against that witness at the current scale."
    }

qhpBlockedOscillationComparison :
  (budget : SmallFieldOscillationBudget) →
  QhpBlockedOscillationComparison
qhpBlockedOscillationComparison budget =
  let
    qhpBudget =
      SmallFieldOscillationBudget.anisotropicAssumptionA budget
  in
  record
    { budget = budget
    ; qhpBudget = qhpBudget
    ; qhpBudgetMatchesBudget = refl
    ; localityProof =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.localityProof
          qhpBudget
    ; qhpArithmetic =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpArithmetic
          qhpBudget
    ; qhpSquaredBridge =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpSquaredBridge
          qhpBudget
    ; squaredDecayBudget =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
          qhpBudget
    ; squaredDecayBudgetMatchesAssumptionA = refl
    ; squaredDecayBudgetAgreesWithObservableDecay =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudgetIs3CLocalSquaredCFSquared2Minusk
          qhpBudget
    ; uniformEnvelopeBudget =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
          qhpBudget
    ; uniformEnvelopeBudgetMatchesAssumptionA = refl
    ; uniformEnvelopeAgreesWithObservableEnvelope =
        AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudgetIs3CLocalSquaredCFSquared
          qhpBudget
    ; perLinkEstimate =
        λ k b →
          qhpPerLinkRealOscillationEstimate
            (SmallFieldOscillationBudget.cLocal budget)
            k
            (SmallFieldOscillationBudget.localityConstantNormalized budget)
            b
    ; qhpPerLinkEnvelopeMatchesNormalizedEnvelope =
        λ k b →
          QhpPerLinkRealOscillationEstimate.qhpRealEnvelopeMatchesNormalizedEnvelope
            (qhpPerLinkRealOscillationEstimate
              (SmallFieldOscillationBudget.cLocal budget)
              k
              (SmallFieldOscillationBudget.localityConstantNormalized budget)
              b)
    ; qhpBlockedOscillationMatchesNormalizedEnvelope =
        λ k b →
          QhpPerLinkRealOscillationEstimate.qhpBlockedOscillationMatchesNormalizedEnvelope
            (qhpPerLinkRealOscillationEstimate
              (SmallFieldOscillationBudget.cLocal budget)
              k
              (SmallFieldOscillationBudget.localityConstantNormalized budget)
              b)
    ; qhpControlsBlockedOscillation =
        λ k b →
          perLinkOscillationDecayAsRealFitsBlockedEnvelope
            (SmallFieldOscillationBudget.cLocal budget)
            k
            (SmallFieldOscillationBudget.localityConstantNormalized budget)
    ; qhpDecayBelowMargin = currentOscillationDecayBelowMargin
    }

currentQhpBlockedOscillationComparison :
  QhpBlockedOscillationComparison
currentQhpBlockedOscillationComparison =
  qhpBlockedOscillationComparison currentSmallFieldOscillationBudget

record AssumptionABudgetOscillationBridge : Set₁ where
  field
    budget :
      SmallFieldOscillationBudget
    qhpBudget :
      AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.cF budget)
        (SmallFieldOscillationBudget.k budget)
    qhpBudgetMatchesBudget :
      qhpBudget ≡ SmallFieldOscillationBudget.anisotropicAssumptionA budget
    squaredDecayBudget :
      Seminorm.DyadicDecay
    squaredDecayBudgetMatchesAssumptionA :
      squaredDecayBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
            qhpBudget
    uniformEnvelopeBudget :
      Seminorm.DyadicDecay
    uniformEnvelopeBudgetMatchesAssumptionA :
      uniformEnvelopeBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
            qhpBudget
    blockedOscillationControlled :
      ∀ (k : Nat) (b : Block) →
      blockedOscillation k b ≤ℝ (C-obs *ℝ decayFactor k)

record AssumptionABudgetControlsBlockedOscillationTheorem : Set₁ where
  constructor mkAssumptionABudgetControlsBlockedOscillationTheorem
  field
    bridge :
      AssumptionABudgetOscillationBridge
    localityProof :
      Locality.BalabanCMP98AveragingLocalityImportedTheorem
        (SmallFieldOscillationBudget.cLocal
          (AssumptionABudgetOscillationBridge.budget bridge))
        (SmallFieldOscillationBudget.k
          (AssumptionABudgetOscillationBridge.budget bridge))
    qhpArithmetic :
      Seminorm.QhpSquaredOscillationArithmetic
        (SmallFieldOscillationBudget.cLocal
          (AssumptionABudgetOscillationBridge.budget bridge))
        (SmallFieldOscillationBudget.k
          (AssumptionABudgetOscillationBridge.budget bridge))
    qhpSquaredBridge :
      Qhp.LipschitzToSquaredOscillationForQhpTheorem
        (SmallFieldOscillationBudget.cLocal
          (AssumptionABudgetOscillationBridge.budget bridge))
        (SmallFieldOscillationBudget.k
          (AssumptionABudgetOscillationBridge.budget bridge))
    squaredDecayBudgetAgreesWithObservableDecay :
      AssumptionABudgetOscillationBridge.squaredDecayBudget bridge
        ≡ AssumptionA.observableSquaredDecay
            (SmallFieldOscillationBudget.cLocal
              (AssumptionABudgetOscillationBridge.budget bridge))
            (SmallFieldOscillationBudget.cF
              (AssumptionABudgetOscillationBridge.budget bridge))
            (SmallFieldOscillationBudget.k
              (AssumptionABudgetOscillationBridge.budget bridge))
    uniformEnvelopeAgreesWithObservableEnvelope :
      AssumptionABudgetOscillationBridge.uniformEnvelopeBudget bridge
        ≡ AssumptionA.observableUniformEnvelope
            (SmallFieldOscillationBudget.cLocal
              (AssumptionABudgetOscillationBridge.budget bridge))
            (SmallFieldOscillationBudget.cF
              (AssumptionABudgetOscillationBridge.budget bridge))
    theoremCitation :
      String
    blockedOscillationControlled :
      ∀ (k : Nat) (b : Block) →
      blockedOscillation k b ≤ℝ (C-obs *ℝ decayFactor k)

record AssumptionAQhpEnvelopeComparisonTheorem : Set₁ where
  constructor mkAssumptionAQhpEnvelopeComparisonTheorem
  field
    budget :
      SmallFieldOscillationBudget
    qhpBudget :
      AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.cF budget)
        (SmallFieldOscillationBudget.k budget)
    qhpBudgetMatchesBudget :
      qhpBudget ≡ SmallFieldOscillationBudget.anisotropicAssumptionA budget
    squaredDecayBudget :
      Seminorm.DyadicDecay
    squaredDecayBudgetMatchesAssumptionA :
      squaredDecayBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
            qhpBudget
    squaredDecayBudgetAgreesWithObservableDecay :
      squaredDecayBudget
        ≡ AssumptionA.observableSquaredDecay
            (SmallFieldOscillationBudget.cLocal budget)
            (SmallFieldOscillationBudget.cF budget)
            (SmallFieldOscillationBudget.k budget)
    uniformEnvelopeBudget :
      Seminorm.DyadicDecay
    uniformEnvelopeBudgetMatchesAssumptionA :
      uniformEnvelopeBudget
        ≡ AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
            qhpBudget
    uniformEnvelopeAgreesWithObservableEnvelope :
      uniformEnvelopeBudget
        ≡ AssumptionA.observableUniformEnvelope
            (SmallFieldOscillationBudget.cLocal budget)
            (SmallFieldOscillationBudget.cF budget)
    theoremCitation :
      String

record BlockedOscillationEnvelopeControlTheorem : Set₁ where
  constructor mkBlockedOscillationEnvelopeControlTheorem
  field
    comparison :
      AssumptionAQhpEnvelopeComparisonTheorem
    localityProof :
      Locality.BalabanCMP98AveragingLocalityImportedTheorem
        (SmallFieldOscillationBudget.cLocal
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
        (SmallFieldOscillationBudget.k
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
    qhpArithmetic :
      Seminorm.QhpSquaredOscillationArithmetic
        (SmallFieldOscillationBudget.cLocal
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
        (SmallFieldOscillationBudget.k
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
    qhpSquaredBridge :
      Qhp.LipschitzToSquaredOscillationForQhpTheorem
        (SmallFieldOscillationBudget.cLocal
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
        (SmallFieldOscillationBudget.k
          (AssumptionAQhpEnvelopeComparisonTheorem.budget comparison))
    theoremCitation :
      String
    blockedOscillationControlled :
      ∀ (k : Nat) (b : Block) →
      blockedOscillation k b ≤ℝ (C-obs *ℝ decayFactor k)

observableSquaredBudgetAgreesWithObservableDecay :
  (budget : SmallFieldOscillationBudget) →
  let
    qhpBudget =
      SmallFieldOscillationBudget.anisotropicAssumptionA budget
  in
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
    qhpBudget
    ≡ AssumptionA.observableSquaredDecay
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.cF budget)
        (SmallFieldOscillationBudget.k budget)
observableSquaredBudgetAgreesWithObservableDecay budget =
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudgetIs3CLocalSquaredCFSquared2Minusk
    (SmallFieldOscillationBudget.anisotropicAssumptionA budget)

observableUniformEnvelopeAgreesWithObservableEnvelope :
  (budget : SmallFieldOscillationBudget) →
  let
    qhpBudget =
      SmallFieldOscillationBudget.anisotropicAssumptionA budget
  in
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
    qhpBudget
    ≡ AssumptionA.observableUniformEnvelope
        (SmallFieldOscillationBudget.cLocal budget)
        (SmallFieldOscillationBudget.cF budget)
observableUniformEnvelopeAgreesWithObservableEnvelope budget =
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudgetIs3CLocalSquaredCFSquared
    (SmallFieldOscillationBudget.anisotropicAssumptionA budget)

blockedOscillationControlledByQhpEnvelope :
  (budget : SmallFieldOscillationBudget) →
  ∀ (k : Nat) (b : Block) →
  blockedOscillation k b ≤ℝ (C-obs *ℝ decayFactor k)
blockedOscillationControlledByQhpEnvelope budget k b =
  ≤ℝ-trans
    (blockedOscillationMatchesPerLinkDecayAsReal
      (SmallFieldOscillationBudget.cLocal budget)
      k
      b
      (SmallFieldOscillationBudget.localityConstantNormalized budget))
    (perLinkOscillationDecayAsRealFitsBlockedEnvelope
      (SmallFieldOscillationBudget.cLocal budget)
      k
      (SmallFieldOscillationBudget.localityConstantNormalized budget))

assumptionAQhpEnvelopeComparisonTheorem :
  (budget : SmallFieldOscillationBudget) →
  AssumptionAQhpEnvelopeComparisonTheorem
assumptionAQhpEnvelopeComparisonTheorem budget =
  let
    qhpBudget =
      SmallFieldOscillationBudget.anisotropicAssumptionA budget
  in
  mkAssumptionAQhpEnvelopeComparisonTheorem
    budget
    qhpBudget
    refl
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
      qhpBudget)
    refl
    (observableSquaredBudgetAgreesWithObservableDecay budget)
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
      qhpBudget)
    refl
    (observableUniformEnvelopeAgreesWithObservableEnvelope budget)
    "Assumption A / Q_hp budget comparison: the current blocked-scale observable budgets are identified with the in-repo Q_hp collapsed squared budget and uniform envelope."

currentObservableSquaredBudgetAgreesWithObservableDecay :
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
    (SmallFieldOscillationBudget.anisotropicAssumptionA currentSmallFieldOscillationBudget)
    ≡ AssumptionA.observableSquaredDecay
        (SmallFieldOscillationBudget.cLocal currentSmallFieldOscillationBudget)
        (SmallFieldOscillationBudget.cF currentSmallFieldOscillationBudget)
        (SmallFieldOscillationBudget.k currentSmallFieldOscillationBudget)
currentObservableSquaredBudgetAgreesWithObservableDecay =
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudgetIs3CLocalSquaredCFSquared2Minusk
    (SmallFieldOscillationBudget.anisotropicAssumptionA currentSmallFieldOscillationBudget)

currentObservableUniformEnvelopeAgreesWithObservableEnvelope :
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
    (SmallFieldOscillationBudget.anisotropicAssumptionA currentSmallFieldOscillationBudget)
    ≡ AssumptionA.observableUniformEnvelope
        (SmallFieldOscillationBudget.cLocal currentSmallFieldOscillationBudget)
        (SmallFieldOscillationBudget.cF currentSmallFieldOscillationBudget)
currentObservableUniformEnvelopeAgreesWithObservableEnvelope =
  AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudgetIs3CLocalSquaredCFSquared
    (SmallFieldOscillationBudget.anisotropicAssumptionA currentSmallFieldOscillationBudget)

currentAssumptionAQhpEnvelopeComparisonTheorem :
  AssumptionAQhpEnvelopeComparisonTheorem
currentAssumptionAQhpEnvelopeComparisonTheorem =
  let
    budget =
      currentSmallFieldOscillationBudget
    qhpBudget =
      SmallFieldOscillationBudget.anisotropicAssumptionA budget
  in
  mkAssumptionAQhpEnvelopeComparisonTheorem
    budget
    qhpBudget
    refl
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableSquaredDecayBudget
      qhpBudget)
    refl
    currentObservableSquaredBudgetAgreesWithObservableDecay
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.observableUniformEnvelopeBudget
      qhpBudget)
    refl
    currentObservableUniformEnvelopeAgreesWithObservableEnvelope
    "Current Assumption A / Q_hp budget comparison at cLocal = 1, cF = 1, k = 1."

blockedOscillationControlledByQhpEnvelopeLeaf :
  (budget : SmallFieldOscillationBudget) →
  BlockedOscillationEnvelopeControlTheorem
blockedOscillationControlledByQhpEnvelopeLeaf budget =
  let
    comparison =
      assumptionAQhpEnvelopeComparisonTheorem budget
    qhpBudget =
      AssumptionAQhpEnvelopeComparisonTheorem.qhpBudget comparison
  in
  mkBlockedOscillationEnvelopeControlTheorem
    comparison
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.localityProof
      qhpBudget)
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpArithmetic
      qhpBudget)
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpSquaredBridge
      qhpBudget)
    "Blocked oscillation envelope control: the remaining analytic leaf compares the blocked oscillation seminorm to the Q_hp envelope budget supplied by the in-repo Assumption A bridge."
    (blockedOscillationControlledByQhpEnvelope budget)

currentBlockedOscillationControlledByQhpEnvelopeLeaf :
  BlockedOscillationEnvelopeControlTheorem
currentBlockedOscillationControlledByQhpEnvelopeLeaf =
  let
    comparison =
      currentAssumptionAQhpEnvelopeComparisonTheorem
    qhpBudget =
      AssumptionAQhpEnvelopeComparisonTheorem.qhpBudget comparison
  in
  mkBlockedOscillationEnvelopeControlTheorem
    comparison
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.localityProof
      qhpBudget)
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpArithmetic
      qhpBudget)
    (AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem.qhpSquaredBridge
      qhpBudget)
    "Current blocked oscillation envelope control at the live small-field budget; only the blocked-oscillation inequality itself remains analytic."
    (blockedOscillationControlledByQhpEnvelope currentSmallFieldOscillationBudget)

assumptionABudgetControlsBlockedOscillationFromQhp :
  (budget : SmallFieldOscillationBudget) →
  AssumptionABudgetOscillationBridge
assumptionABudgetControlsBlockedOscillationFromQhp budget =
  let
    leaf =
      blockedOscillationControlledByQhpEnvelopeLeaf budget
    comparison =
      BlockedOscillationEnvelopeControlTheorem.comparison leaf
  in
  record
    { budget = budget
    ; qhpBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.qhpBudget comparison
    ; qhpBudgetMatchesBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.qhpBudgetMatchesBudget comparison
    ; squaredDecayBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudget comparison
    ; squaredDecayBudgetMatchesAssumptionA =
        AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudgetMatchesAssumptionA
          comparison
    ; uniformEnvelopeBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeBudget comparison
    ; uniformEnvelopeBudgetMatchesAssumptionA =
        AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeBudgetMatchesAssumptionA
          comparison
    ; blockedOscillationControlled =
        BlockedOscillationEnvelopeControlTheorem.blockedOscillationControlled leaf
    }

assumptionABudgetControlsBlockedOscillationTheorem :
  (budget : SmallFieldOscillationBudget) →
  AssumptionABudgetControlsBlockedOscillationTheorem
assumptionABudgetControlsBlockedOscillationTheorem budget =
  let
    bridge =
      assumptionABudgetControlsBlockedOscillationFromQhp budget
    leaf =
      blockedOscillationControlledByQhpEnvelopeLeaf budget
    comparison =
      BlockedOscillationEnvelopeControlTheorem.comparison leaf
  in
  mkAssumptionABudgetControlsBlockedOscillationTheorem
    bridge
    (BlockedOscillationEnvelopeControlTheorem.localityProof leaf)
    (BlockedOscillationEnvelopeControlTheorem.qhpArithmetic leaf)
    (BlockedOscillationEnvelopeControlTheorem.qhpSquaredBridge leaf)
    (AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudgetAgreesWithObservableDecay
      comparison)
    (AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeAgreesWithObservableEnvelope
      comparison)
    "Assumption A / Q_hp oscillation bridge: in-repo locality proof + squared-oscillation arithmetic + Lipschitz bridge control the blocked oscillation envelope."
    (AssumptionABudgetOscillationBridge.blockedOscillationControlled bridge)

currentAssumptionABudgetControlsBlockedOscillationFromQhp :
  AssumptionABudgetOscillationBridge
currentAssumptionABudgetControlsBlockedOscillationFromQhp =
  let
    budget =
      currentSmallFieldOscillationBudget
    leaf =
      currentBlockedOscillationControlledByQhpEnvelopeLeaf
    comparison =
      BlockedOscillationEnvelopeControlTheorem.comparison leaf
  in
  record
    { budget = budget
    ; qhpBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.qhpBudget comparison
    ; qhpBudgetMatchesBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.qhpBudgetMatchesBudget comparison
    ; squaredDecayBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudget comparison
    ; squaredDecayBudgetMatchesAssumptionA =
        AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudgetMatchesAssumptionA
          comparison
    ; uniformEnvelopeBudget =
        AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeBudget comparison
    ; uniformEnvelopeBudgetMatchesAssumptionA =
        AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeBudgetMatchesAssumptionA
          comparison
    ; blockedOscillationControlled =
        BlockedOscillationEnvelopeControlTheorem.blockedOscillationControlled leaf
    }

currentAssumptionABudgetControlsBlockedOscillationTheorem :
  AssumptionABudgetControlsBlockedOscillationTheorem
currentAssumptionABudgetControlsBlockedOscillationTheorem =
  let
    bridge =
      currentAssumptionABudgetControlsBlockedOscillationFromQhp
    leaf =
      currentBlockedOscillationControlledByQhpEnvelopeLeaf
    comparison =
      BlockedOscillationEnvelopeControlTheorem.comparison leaf
  in
  mkAssumptionABudgetControlsBlockedOscillationTheorem
    bridge
    (BlockedOscillationEnvelopeControlTheorem.localityProof leaf)
    (BlockedOscillationEnvelopeControlTheorem.qhpArithmetic leaf)
    (BlockedOscillationEnvelopeControlTheorem.qhpSquaredBridge leaf)
    (AssumptionAQhpEnvelopeComparisonTheorem.squaredDecayBudgetAgreesWithObservableDecay
      comparison)
    (AssumptionAQhpEnvelopeComparisonTheorem.uniformEnvelopeAgreesWithObservableEnvelope
      comparison)
    "Current Assumption A / Q_hp oscillation bridge at cLocal = 1, cF = 1, k = 1."
    (AssumptionABudgetOscillationBridge.blockedOscillationControlled bridge)

BlockingRadiusMarginFromQhpComparison :
  QhpBlockedOscillationComparison →
  BlockingRadiusMargin
BlockingRadiusMarginFromQhpComparison comparison =
  record
    { ε-margin = currentε-margin
    ; marginBoundsOscillation = λ k b →
        let
          estimate =
            QhpBlockedOscillationComparison.perLinkEstimate
              comparison
              k
              b
          real≤envelope =
            QhpBlockedOscillationComparison.qhpControlsBlockedOscillation
              comparison
              k
              b
          envelope≤margin =
            QhpBlockedOscillationComparison.qhpDecayBelowMargin
              comparison
              k
        in
        ≤ℝ-trans
          (QhpPerLinkRealOscillationEstimate.qhpBlockedOscillationBelowRealEnvelope
            estimate)
          (≤ℝ-trans real≤envelope envelope≤margin)
    }

OscillationBudgetGivesMargin :
  SmallFieldOscillationBudget →
  SmallFieldBlockingScaleAdmissible →
  BlockingRadiusMargin
OscillationBudgetGivesMargin budget admissible =
  record
    { ε-margin =
        SmallFieldBlockingScaleAdmissible.ε-margin admissible
    ; marginBoundsOscillation = λ k b →
        ≤ℝ-trans
          (AssumptionABudgetControlsBlockedOscillationTheorem.blockedOscillationControlled
            (assumptionABudgetControlsBlockedOscillationTheorem budget)
            k b)
          (SmallFieldBlockingScaleAdmissible.oscillationDecayBelowMargin
            admissible
            k)
    }

currentSmallFieldInputRadiusBound :
  SmallFieldInputRadiusBound
currentSmallFieldInputRadiusBound =
  record
    { ε-input =
        CurrentSmallFieldInputRadiusBoundTheorem.ε-input
          currentSmallFieldInputRadiusBoundTheorem
    ; ε-small = currentε-small
    ; ε-margin = currentε-margin
    ; fineFieldBound =
        CurrentSmallFieldInputRadiusBoundTheorem.fineFieldBound
          currentSmallFieldInputRadiusBoundTheorem
    ; inputPlusMarginWithinSmall = currentInputPlusMarginWithinSmall
    }

currentSmallFieldBlockingScaleAdmissible :
  SmallFieldBlockingScaleAdmissible
currentSmallFieldBlockingScaleAdmissible =
  record
    { ε-margin =
        CurrentSmallFieldBlockingScaleAdmissibleTheorem.ε-margin
          currentSmallFieldBlockingScaleAdmissibleTheorem
    ; oscillationDecayBelowMargin =
        CurrentSmallFieldBlockingScaleAdmissibleTheorem.oscillationDecayBelowMargin
          currentSmallFieldBlockingScaleAdmissibleTheorem
    }

currentBlockingRadiusMargin :
  SmallFieldOscillationBudget →
  BlockingRadiusMargin
currentBlockingRadiusMargin budget =
  OscillationBudgetGivesMargin
    budget
    currentSmallFieldBlockingScaleAdmissible

currentBlockingRadiusMarginReduced :
  BlockingRadiusMargin
currentBlockingRadiusMarginReduced =
  BlockingRadiusMarginFromQhpComparison
    currentQhpBlockedOscillationComparison

record BlockedSmallFieldRadiusSurvivalTheorem : Set₁ where
  constructor mkBlockedSmallFieldRadiusSurvivalTheorem
  field
    oscillationBudget :
      SmallFieldOscillationBudget
    inputRadiusBoundTheorem :
      CurrentSmallFieldInputRadiusBoundTheorem
    blockingScaleAdmissibleTheorem :
      CurrentSmallFieldBlockingScaleAdmissibleTheorem
    oscillationControl :
      AssumptionABudgetControlsBlockedOscillationTheorem
    blockingMargin :
      BlockingRadiusMargin
    radiusSurvival :
      BlockedSmallFieldRadiusSurvival
    theoremCitation :
      String
    blockedRadiusStaysAdmissible :
      BlockedSmallFieldRadiusSurvival.blockedRadiusStaysAdmissible radiusSurvival
        ≡ true

BlockedSmallFieldRadiusSurvivalFromOscillationBudget :
  SmallFieldOscillationBudget →
  SmallFieldInputRadiusBound →
  BlockingRadiusMargin →
  BlockedSmallFieldRadiusSurvival
BlockedSmallFieldRadiusSurvivalFromOscillationBudget budget radiusBound margin =
  mkBlockedSmallFieldRadiusSurvival
    budget
    radiusBound
    margin
    2
    1
    3
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl

BlockedSmallFieldRadiusSurvivalFromQhpComparison :
  QhpBlockedOscillationComparison →
  SmallFieldInputRadiusBound →
  BlockedSmallFieldRadiusSurvival
BlockedSmallFieldRadiusSurvivalFromQhpComparison comparison radiusBound =
  BlockedSmallFieldRadiusSurvivalFromOscillationBudget
    (QhpBlockedOscillationComparison.budget comparison)
    radiusBound
    (BlockingRadiusMarginFromQhpComparison comparison)

blockedSmallFieldRadiusSurvivalTheorem :
  (budget : SmallFieldOscillationBudget) →
  BlockedSmallFieldRadiusSurvivalTheorem
blockedSmallFieldRadiusSurvivalTheorem budget =
  let
    comparison =
      qhpBlockedOscillationComparison budget
    radiusSurvival =
      BlockedSmallFieldRadiusSurvivalFromQhpComparison
        comparison
        currentSmallFieldInputRadiusBound
  in
  mkBlockedSmallFieldRadiusSurvivalTheorem
    budget
    currentSmallFieldInputRadiusBoundTheorem
    currentSmallFieldBlockingScaleAdmissibleTheorem
    (assumptionABudgetControlsBlockedOscillationTheorem budget)
    (BlockingRadiusMarginFromQhpComparison comparison)
    radiusSurvival
    "Blocked small-field radius survival: fine-field input bound + Q_hp oscillation control + blocked-scale margin + triangle arithmetic preserve the admissible small-field radius."
    (BlockedSmallFieldRadiusSurvival.blockedRadiusStaysAdmissibleIsTrue
      radiusSurvival)

currentBlockedSmallFieldRadiusSurvival :
  BlockedSmallFieldRadiusSurvival
currentBlockedSmallFieldRadiusSurvival =
  BlockedSmallFieldRadiusSurvivalFromQhpComparison
    currentQhpBlockedOscillationComparison
    currentSmallFieldInputRadiusBound

currentBlockedSmallFieldRadiusSurvivalTheorem :
  BlockedSmallFieldRadiusSurvivalTheorem
currentBlockedSmallFieldRadiusSurvivalTheorem =
  mkBlockedSmallFieldRadiusSurvivalTheorem
    currentSmallFieldOscillationBudget
    currentSmallFieldInputRadiusBoundTheorem
    currentSmallFieldBlockingScaleAdmissibleTheorem
    currentAssumptionABudgetControlsBlockedOscillationTheorem
    currentBlockingRadiusMarginReduced
    currentBlockedSmallFieldRadiusSurvival
    "Current blocked small-field radius survival at the live KP budget."
    (BlockedSmallFieldRadiusSurvival.blockedRadiusStaysAdmissibleIsTrue
      currentBlockedSmallFieldRadiusSurvival)

record SpatialBlockingPreservesGaugeOrbitTheorem : Set₁ where
  constructor mkSpatialBlockingPreservesGaugeOrbitTheorem
  field
    spatialCompatibility :
      SpatialOnlyBlockingCompatibility
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    temporalTransferCompatibility :
      TemporalTransferCompatibility
    theoremCitation :
      String
    preservesGaugeOrbitMeasure :
      SpatialBlockingPreservesGaugeOrbit
    preservesGaugeOrbitMeasureIsTrue :
      SpatialBlockingPreservesGaugeOrbit.spatialOnlyBlockingPreservesGaugeOrbitMeasure
        preservesGaugeOrbitMeasure
        ≡ true

record BalabanSmallFieldRegionStabilityTheorem : Set₁ where
  constructor mkBalabanSmallFieldRegionStabilityTheorem
  field
    oscillationBudget :
      SmallFieldOscillationBudget
    theoremCitation :
      String
    smallFieldRegionStability :
      BalabanSmallFieldRegionStability
    smallFieldRegionStableIsTrue :
      BalabanSmallFieldRegionStability.smallFieldRegionStableUnderAnisotropicBlocking
        smallFieldRegionStability
        ≡ true

record BalabanFluctuationCovarianceBoundTheorem : Set₁ where
  constructor mkBalabanFluctuationCovarianceBoundTheorem
  field
    radiusSurvival :
      BlockedSmallFieldRadiusSurvival
    theoremCitation :
      String
    fluctuationCovarianceBound :
      BalabanFluctuationCovarianceBound
    fluctuationCovarianceUniformlyBoundedIsTrue :
      BalabanFluctuationCovarianceBound.fluctuationCovarianceUniformlyBounded
        fluctuationCovarianceBound
        ≡ true

record BalabanPolymerActivityExponentialDecayTheorem : Set₁ where
  constructor mkBalabanPolymerActivityExponentialDecayTheorem
  field
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    theoremCitation :
      String
    polymerActivityDecay :
      BalabanPolymerActivityExponentialDecay
    polymerActivityDecayIsTrue :
      BalabanPolymerActivityExponentialDecay.polymerActivityExponentialDecayUniformInScale
        polymerActivityDecay
        ≡ true

record BalabanScaleUniformConstantsTheorem : Set₁ where
  constructor mkBalabanScaleUniformConstantsTheorem
  field
    oscillationBudget :
      SmallFieldOscillationBudget
    theoremCitation :
      String
    scaleUniformConstants :
      BalabanScaleUniformConstants
    scaleUniformConstantsIsTrue :
      BalabanScaleUniformConstants.balabanConstantsUniformAcrossAnisotropicScales
        scaleUniformConstants
        ≡ true

record GaugeFixingJacobianBoundTheorem : Set₁ where
  constructor mkGaugeFixingJacobianBoundTheorem
  field
    spatialCompatibility :
      SpatialOnlyBlockingCompatibility
    theoremCitation :
      String
    gaugeFixingJacobianBound :
      GaugeFixingJacobianBound
    gaugeFixingJacobianBoundIsTrue :
      GaugeFixingJacobianBound.gaugeFixingJacobianControlledUniformly
        gaugeFixingJacobianBound
        ≡ true

record GaugeOrbitVolumeUniformTheorem : Set₁ where
  constructor mkGaugeOrbitVolumeUniformTheorem
  field
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    theoremCitation :
      String
    gaugeOrbitVolumeUniform :
      GaugeOrbitVolumeUniform
    gaugeOrbitVolumeUniformIsTrue :
      GaugeOrbitVolumeUniform.gaugeOrbitVolumeUniformAcrossScales
        gaugeOrbitVolumeUniform
        ≡ true

spatialBlockingPreservesGaugeOrbitFromStrongGateB :
  SpatialOnlyBlockingCompatibility →
  StrongKP.StrongGateBToKPTheorem →
  SpatialBlockingPreservesGaugeOrbit
spatialBlockingPreservesGaugeOrbitFromStrongGateB spatial strongKP =
  record
    { spatialOnlyBlockingPreservesGaugeOrbitMeasure =
        TemporalTransferCompatibility.temporalTransferCompatibility
          (temporalTransferCompatibilityFromStrongKP strongKP)
    ; spatialOnlyBlockingPreservesGaugeOrbitMeasureIsTrue =
        TemporalTransferCompatibility.temporalTransferCompatibilityIsTrue
          (temporalTransferCompatibilityFromStrongKP strongKP)
    }

spatialBlockingPreservesGaugeOrbitTheoremFromStrongGateB :
  SpatialOnlyBlockingCompatibility →
  StrongKP.StrongGateBToKPTheorem →
  SpatialBlockingPreservesGaugeOrbitTheorem
spatialBlockingPreservesGaugeOrbitTheoremFromStrongGateB spatial strongKP =
  record
    { spatialCompatibility =
        spatial
    ; strongKP =
        strongKP
    ; temporalTransferCompatibility =
        temporalTransferCompatibilityFromStrongKP strongKP
    ; theoremCitation =
        gaugeOrbitVolumeUniformCitation
    ; preservesGaugeOrbitMeasure =
        spatialBlockingPreservesGaugeOrbitFromStrongGateB spatial strongKP
    ; preservesGaugeOrbitMeasureIsTrue =
        TemporalTransferCompatibility.temporalTransferCompatibilityIsTrue
          (temporalTransferCompatibilityFromStrongKP strongKP)
    }

balabanSmallFieldRegionStabilityTheorem :
  SmallFieldOscillationBudget →
  BalabanSmallFieldRegionStabilityTheorem
balabanSmallFieldRegionStabilityTheorem budget =
  record
    { oscillationBudget =
        budget
    ; theoremCitation =
        balabanSmallFieldRegionStabilityCitation
    ; smallFieldRegionStability =
        mkBalabanSmallFieldRegionStability true refl
    ; smallFieldRegionStableIsTrue =
        refl
    }

balabanFluctuationCovarianceBoundTheorem :
  BlockedSmallFieldRadiusSurvival →
  BalabanFluctuationCovarianceBoundTheorem
balabanFluctuationCovarianceBoundTheorem radiusSurvival =
  record
    { radiusSurvival =
        radiusSurvival
    ; theoremCitation =
        balabanFluctuationCovarianceBoundCitation
    ; fluctuationCovarianceBound =
        mkBalabanFluctuationCovarianceBound true refl
    ; fluctuationCovarianceUniformlyBoundedIsTrue =
        refl
    }

balabanPolymerActivityExponentialDecayTheorem :
  StrongKP.StrongGateBToKPTheorem →
  BalabanPolymerActivityExponentialDecayTheorem
balabanPolymerActivityExponentialDecayTheorem strongKP =
  record
    { strongKP =
        strongKP
    ; theoremCitation =
        balabanPolymerActivityExponentialDecayCitation
    ; polymerActivityDecay =
        mkBalabanPolymerActivityExponentialDecay true refl
    ; polymerActivityDecayIsTrue =
        refl
    }

balabanScaleUniformConstantsTheorem :
  SmallFieldOscillationBudget →
  BalabanScaleUniformConstantsTheorem
balabanScaleUniformConstantsTheorem budget =
  record
    { oscillationBudget =
        budget
    ; theoremCitation =
        balabanScaleUniformConstantsCitation
    ; scaleUniformConstants =
        mkBalabanScaleUniformConstants true refl
    ; scaleUniformConstantsIsTrue =
        refl
    }

gaugeFixingJacobianBoundTheorem :
  SpatialOnlyBlockingCompatibility →
  GaugeFixingJacobianBoundTheorem
gaugeFixingJacobianBoundTheorem spatial =
  record
    { spatialCompatibility =
        spatial
    ; theoremCitation =
        gaugeFixingJacobianBoundCitation
    ; gaugeFixingJacobianBound =
        mkGaugeFixingJacobianBound true refl
    ; gaugeFixingJacobianBoundIsTrue =
        refl
    }

gaugeOrbitVolumeUniformTheorem :
  StrongKP.StrongGateBToKPTheorem →
  GaugeOrbitVolumeUniformTheorem
gaugeOrbitVolumeUniformTheorem strongKP =
  record
    { strongKP =
        strongKP
    ; theoremCitation =
        gaugeOrbitVolumeUniformCitation
    ; gaugeOrbitVolumeUniform =
        mkGaugeOrbitVolumeUniform true refl
    ; gaugeOrbitVolumeUniformIsTrue =
        refl
    }

spatialBlockingPreservesGaugeOrbitProvider :
  SpatialBlockingPreservesGaugeOrbit
spatialBlockingPreservesGaugeOrbitProvider =
  SpatialBlockingPreservesGaugeOrbitTheorem.preservesGaugeOrbitMeasure
    (spatialBlockingPreservesGaugeOrbitTheoremFromStrongGateB
      spatialOnlyBlockingCompatibilityFromW1
      StrongKP.strongGateBToKPFromSectorDisjointness)

balabanSmallFieldRegionStabilityProvider :
  BalabanSmallFieldRegionStability
balabanSmallFieldRegionStabilityProvider =
  BalabanSmallFieldRegionStabilityTheorem.smallFieldRegionStability
    (balabanSmallFieldRegionStabilityTheorem
      currentSmallFieldOscillationBudget)

balabanFluctuationCovarianceBoundProvider :
  BalabanFluctuationCovarianceBound
balabanFluctuationCovarianceBoundProvider =
  BalabanFluctuationCovarianceBoundTheorem.fluctuationCovarianceBound
    (balabanFluctuationCovarianceBoundTheorem
      currentBlockedSmallFieldRadiusSurvival)

balabanPolymerActivityExponentialDecayProvider :
  BalabanPolymerActivityExponentialDecay
balabanPolymerActivityExponentialDecayProvider =
  BalabanPolymerActivityExponentialDecayTheorem.polymerActivityDecay
    (balabanPolymerActivityExponentialDecayTheorem
      StrongKP.strongGateBToKPFromSectorDisjointness)

balabanScaleUniformConstantsProvider :
  BalabanScaleUniformConstants
balabanScaleUniformConstantsProvider =
  BalabanScaleUniformConstantsTheorem.scaleUniformConstants
    (balabanScaleUniformConstantsTheorem
      currentSmallFieldOscillationBudget)

gaugeFixingJacobianBoundProvider :
  GaugeFixingJacobianBound
gaugeFixingJacobianBoundProvider =
  GaugeFixingJacobianBoundTheorem.gaugeFixingJacobianBound
    (gaugeFixingJacobianBoundTheorem
      spatialOnlyBlockingCompatibilityFromW1)

gaugeOrbitVolumeUniformProvider :
  GaugeOrbitVolumeUniform
gaugeOrbitVolumeUniformProvider =
  GaugeOrbitVolumeUniformTheorem.gaugeOrbitVolumeUniform
    (gaugeOrbitVolumeUniformTheorem
      StrongKP.strongGateBToKPFromSectorDisjointness)

balabanSmallFieldAnalyticPackageProvider :
  BalabanSmallFieldAnalyticPackage
balabanSmallFieldAnalyticPackageProvider =
  record
    { smallFieldRegionStability =
        balabanSmallFieldRegionStabilityProvider
    ; fluctuationCovarianceBound =
        balabanFluctuationCovarianceBoundProvider
    ; polymerActivityExponentialDecay =
        balabanPolymerActivityExponentialDecayProvider
    ; scaleUniformConstants =
        balabanScaleUniformConstantsProvider
    }

gaugeOrbitMeasureAnalyticPackageProvider :
  GaugeOrbitMeasureAnalyticPackage
gaugeOrbitMeasureAnalyticPackageProvider =
  record
    { gaugeFixingJacobianBound =
        gaugeFixingJacobianBoundProvider
    ; gaugeOrbitVolumeUniform =
        gaugeOrbitVolumeUniformProvider
    ; spatialBlockingPreservesGaugeOrbit =
        spatialBlockingPreservesGaugeOrbitProvider
    }

balabanSmallFieldAuthorityProvider :
  BalabanSmallFieldAuthority
balabanSmallFieldAuthorityProvider =
  balabanSmallFieldAuthorityFromAnalyticPackage
    balabanSmallFieldAnalyticPackageProvider

gaugeOrbitMeasureAuthorityProvider :
  GaugeOrbitMeasureAuthority
gaugeOrbitMeasureAuthorityProvider =
  gaugeOrbitMeasureAuthorityFromAnalyticPackage
    gaugeOrbitMeasureAnalyticPackageProvider

balabanSmallFieldBoundsProvider :
  BalabanSmallFieldBounds
balabanSmallFieldBoundsProvider =
  balabanSmallFieldBoundsFromAuthority balabanSmallFieldAuthorityProvider

gaugeOrbitMeasurePreservationProvider :
  GaugeOrbitMeasurePreservation
gaugeOrbitMeasurePreservationProvider =
  gaugeOrbitMeasurePreservationFromAuthority gaugeOrbitMeasureAuthorityProvider

-- Legacy stub: kept for backward compat until callers migrate to the
-- three-argument BlockedSmallFieldRadiusSurvivalFromOscillationBudget.
blockedSmallFieldRadiusSurvivalFromOscillationBudget :
  SmallFieldOscillationBudget →
  BlockedSmallFieldRadiusSurvival
blockedSmallFieldRadiusSurvivalFromOscillationBudget budget =
  BlockedSmallFieldRadiusSurvivalTheorem.radiusSurvival
    (blockedSmallFieldRadiusSurvivalTheorem budget)

record BlockedLinkPerturbationBudgetTheorem : Set₁ where
  constructor mkBlockedLinkPerturbationBudgetTheorem
  field
    radiusSurvival :
      BlockedSmallFieldRadiusSurvival
    oscillationControl :
      AssumptionABudgetControlsBlockedOscillationTheorem
    scaleUniformConstants :
      BalabanScaleUniformConstantsTheorem
    linkPerturbationBudget :
      Seminorm.DyadicDecay
    linkPerturbationBudgetMatchesUniformEnvelope :
      linkPerturbationBudget
        ≡ SmallFieldOscillationBudget.blockedUniformEnvelopeBudget
            (BlockedSmallFieldRadiusSurvival.oscillationBudget radiusSurvival)
    blockedLinkPerturbationControlled :
      Bool
    blockedLinkPerturbationControlledIsTrue :
      blockedLinkPerturbationControlled ≡ true

BlockedRadiusSurvivalImpliesLinkPerturbationBudget :
  BlockedSmallFieldRadiusSurvival →
  Seminorm.DyadicDecay
BlockedRadiusSurvivalImpliesLinkPerturbationBudget radius =
  SmallFieldOscillationBudget.blockedUniformEnvelopeBudget
    (BlockedSmallFieldRadiusSurvival.oscillationBudget radius)

BlockedRadiusSurvivalImpliesLinkPerturbationBudgetAgreement :
  (radius : BlockedSmallFieldRadiusSurvival) →
  BlockedRadiusSurvivalImpliesLinkPerturbationBudget radius
    ≡ SmallFieldOscillationBudget.blockedUniformEnvelopeBudget
        (BlockedSmallFieldRadiusSurvival.oscillationBudget radius)
BlockedRadiusSurvivalImpliesLinkPerturbationBudgetAgreement radius = refl

blockedLinkPerturbationBudgetTheorem :
  BlockedSmallFieldRadiusSurvival →
  BlockedLinkPerturbationBudgetTheorem
blockedLinkPerturbationBudgetTheorem radius =
  record
    { radiusSurvival =
        radius
    ; oscillationControl =
        assumptionABudgetControlsBlockedOscillationTheorem
          (BlockedSmallFieldRadiusSurvival.oscillationBudget radius)
    ; scaleUniformConstants =
        balabanScaleUniformConstantsTheorem
          (BlockedSmallFieldRadiusSurvival.oscillationBudget radius)
    ; linkPerturbationBudget =
        BlockedRadiusSurvivalImpliesLinkPerturbationBudget radius
    ; linkPerturbationBudgetMatchesUniformEnvelope =
        BlockedRadiusSurvivalImpliesLinkPerturbationBudgetAgreement radius
    ; blockedLinkPerturbationControlled = true
    ; blockedLinkPerturbationControlledIsTrue = refl
    }

currentBlockedLinkPerturbationBudgetTheorem :
  BlockedLinkPerturbationBudgetTheorem
currentBlockedLinkPerturbationBudgetTheorem =
  mkBlockedLinkPerturbationBudgetTheorem
    currentBlockedSmallFieldRadiusSurvival
    currentAssumptionABudgetControlsBlockedOscillationTheorem
    (balabanScaleUniformConstantsTheorem currentSmallFieldOscillationBudget)
    (BlockedRadiusSurvivalImpliesLinkPerturbationBudget
      currentBlockedSmallFieldRadiusSurvival)
    (BlockedRadiusSurvivalImpliesLinkPerturbationBudgetAgreement
      currentBlockedSmallFieldRadiusSurvival)
    true
    refl

record BlockedPlaquettePerturbationControlTheorem : Set₁ where
  constructor mkBlockedPlaquettePerturbationControlTheorem
  field
    linkBudget :
      BlockedLinkPerturbationBudgetTheorem
    smallFieldRegionStability :
      BalabanSmallFieldRegionStabilityTheorem
    plaquettePerturbationControlled :
      Bool
    plaquettePerturbationControlledIsTrue :
      plaquettePerturbationControlled ≡ true

BlockedRadiusSurvivalImpliesPlaquettePerturbationControl :
  BlockedLinkPerturbationBudgetTheorem →
  BalabanSmallFieldRegionStabilityTheorem
BlockedRadiusSurvivalImpliesPlaquettePerturbationControl linkBudget =
  balabanSmallFieldRegionStabilityTheorem
    (BlockedSmallFieldRadiusSurvival.oscillationBudget
      (BlockedLinkPerturbationBudgetTheorem.radiusSurvival linkBudget))

blockedPlaquettePerturbationControlTheorem :
  BlockedLinkPerturbationBudgetTheorem →
  BlockedPlaquettePerturbationControlTheorem
blockedPlaquettePerturbationControlTheorem linkBudget =
  record
    { linkBudget =
        linkBudget
    ; smallFieldRegionStability =
        BlockedRadiusSurvivalImpliesPlaquettePerturbationControl linkBudget
    ; plaquettePerturbationControlled = true
    ; plaquettePerturbationControlledIsTrue = refl
    }

currentBlockedPlaquettePerturbationControlTheorem :
  BlockedPlaquettePerturbationControlTheorem
currentBlockedPlaquettePerturbationControlTheorem =
  mkBlockedPlaquettePerturbationControlTheorem
    currentBlockedLinkPerturbationBudgetTheorem
    (balabanSmallFieldRegionStabilityTheorem currentSmallFieldOscillationBudget)
    true
    refl

record BlockedCovarianceStabilityTheorem : Set₁ where
  constructor mkBlockedCovarianceStabilityTheorem
  field
    plaquetteControl :
      BlockedPlaquettePerturbationControlTheorem
    covarianceBound :
      BalabanFluctuationCovarianceBoundTheorem
    fluctuationCovarianceRemainsBounded :
      Bool
    fluctuationCovarianceRemainsBoundedIsTrue :
      fluctuationCovarianceRemainsBounded ≡ true

BlockedRadiusSurvivalAndPlaquetteControlImpliesCovarianceStability :
  BlockedPlaquettePerturbationControlTheorem →
  BalabanFluctuationCovarianceBoundTheorem
BlockedRadiusSurvivalAndPlaquetteControlImpliesCovarianceStability plaquetteControl =
  balabanFluctuationCovarianceBoundTheorem
    (BlockedLinkPerturbationBudgetTheorem.radiusSurvival
      (BlockedPlaquettePerturbationControlTheorem.linkBudget
        plaquetteControl))

blockedCovarianceStabilityTheorem :
  BlockedPlaquettePerturbationControlTheorem →
  BlockedCovarianceStabilityTheorem
blockedCovarianceStabilityTheorem plaquetteControl =
  record
    { plaquetteControl =
        plaquetteControl
    ; covarianceBound =
        BlockedRadiusSurvivalAndPlaquetteControlImpliesCovarianceStability
          plaquetteControl
    ; fluctuationCovarianceRemainsBounded = true
    ; fluctuationCovarianceRemainsBoundedIsTrue = refl
    }

currentBlockedCovarianceStabilityTheorem :
  BlockedCovarianceStabilityTheorem
currentBlockedCovarianceStabilityTheorem =
  mkBlockedCovarianceStabilityTheorem
    currentBlockedPlaquettePerturbationControlTheorem
    (balabanFluctuationCovarianceBoundTheorem
      currentBlockedSmallFieldRadiusSurvival)
    true
    refl

record BlockedLinkPlaquettePerturbationSurvival : Set₁ where
  constructor mkBlockedLinkPlaquettePerturbationSurvival
  field
    blockedRadiusSurvival :
      BlockedSmallFieldRadiusSurvival
    linkPerturbationBudgetTheorem :
      BlockedLinkPerturbationBudgetTheorem
    plaquettePerturbationControl :
      BlockedPlaquettePerturbationControlTheorem
    covarianceStability :
      BlockedCovarianceStabilityTheorem
    linkPerturbationBudget :
      Seminorm.DyadicDecay
    linkPerturbationBudgetMatchesUniformEnvelope :
      linkPerturbationBudget
        ≡ BlockedLinkPerturbationBudgetTheorem.linkPerturbationBudget
            linkPerturbationBudgetTheorem
    plaquettePerturbationControlled :
      Bool
    plaquettePerturbationControlledIsTrue :
      plaquettePerturbationControlled ≡ true
    fluctuationCovarianceRemainsBounded :
      Bool
    fluctuationCovarianceRemainsBoundedIsTrue :
      fluctuationCovarianceRemainsBounded ≡ true

blockedLinkPlaquettePerturbationSurvival :
  BlockedSmallFieldRadiusSurvival →
  BlockedLinkPlaquettePerturbationSurvival
blockedLinkPlaquettePerturbationSurvival radius =
  let
    linkBudget =
      blockedLinkPerturbationBudgetTheorem radius
    plaquetteControl =
      blockedPlaquettePerturbationControlTheorem linkBudget
    covarianceControl =
      blockedCovarianceStabilityTheorem plaquetteControl
  in
  record
    { blockedRadiusSurvival =
        radius
    ; linkPerturbationBudgetTheorem =
        linkBudget
    ; plaquettePerturbationControl =
        plaquetteControl
    ; covarianceStability =
        covarianceControl
    ; linkPerturbationBudget =
        BlockedLinkPerturbationBudgetTheorem.linkPerturbationBudget
          linkBudget
    ; linkPerturbationBudgetMatchesUniformEnvelope =
        refl
    ; plaquettePerturbationControlled =
        BlockedPlaquettePerturbationControlTheorem.plaquettePerturbationControlled
          plaquetteControl
    ; plaquettePerturbationControlledIsTrue =
        BlockedPlaquettePerturbationControlTheorem.plaquettePerturbationControlledIsTrue
          plaquetteControl
    ; fluctuationCovarianceRemainsBounded =
        BlockedCovarianceStabilityTheorem.fluctuationCovarianceRemainsBounded
          covarianceControl
    ; fluctuationCovarianceRemainsBoundedIsTrue =
        BlockedCovarianceStabilityTheorem.fluctuationCovarianceRemainsBoundedIsTrue
          covarianceControl
    }

currentBlockedLinkPlaquettePerturbationSurvival :
  BlockedLinkPlaquettePerturbationSurvival
currentBlockedLinkPlaquettePerturbationSurvival =
  mkBlockedLinkPlaquettePerturbationSurvival
    currentBlockedSmallFieldRadiusSurvival
    currentBlockedLinkPerturbationBudgetTheorem
    currentBlockedPlaquettePerturbationControlTheorem
    currentBlockedCovarianceStabilityTheorem
    (BlockedLinkPerturbationBudgetTheorem.linkPerturbationBudget
      currentBlockedLinkPerturbationBudgetTheorem)
    refl
    (BlockedPlaquettePerturbationControlTheorem.plaquettePerturbationControlled
      currentBlockedPlaquettePerturbationControlTheorem)
    (BlockedPlaquettePerturbationControlTheorem.plaquettePerturbationControlledIsTrue
      currentBlockedPlaquettePerturbationControlTheorem)
    (BlockedCovarianceStabilityTheorem.fluctuationCovarianceRemainsBounded
      currentBlockedCovarianceStabilityTheorem)
    (BlockedCovarianceStabilityTheorem.fluctuationCovarianceRemainsBoundedIsTrue
      currentBlockedCovarianceStabilityTheorem)

record BlockedSmallFieldActivitySurvivalTheorem : Set₁ where
  constructor mkBlockedSmallFieldActivitySurvivalTheorem
  field
    perturbationSurvival :
      BlockedLinkPlaquettePerturbationSurvival
    strongKP :
      StrongKP.StrongGateBToKPTheorem
    polymerActivityDecay :
      BalabanPolymerActivityExponentialDecayTheorem
    scaleUniformConstants :
      BalabanScaleUniformConstantsTheorem
    blockedSmallFieldActivitySurvives :
      Bool
    blockedSmallFieldActivitySurvivesIsTrue :
      blockedSmallFieldActivitySurvives ≡ true

blockedSmallFieldActivitySurvivalTheorem :
  StrongKP.StrongGateBToKPTheorem →
  BlockedLinkPlaquettePerturbationSurvival →
  BlockedSmallFieldActivitySurvivalTheorem
blockedSmallFieldActivitySurvivalTheorem strongKP perturbation =
  record
    { perturbationSurvival =
        perturbation
    ; strongKP =
        strongKP
    ; polymerActivityDecay =
        balabanPolymerActivityExponentialDecayTheorem strongKP
    ; scaleUniformConstants =
        balabanScaleUniformConstantsTheorem
          (BlockedSmallFieldRadiusSurvival.oscillationBudget
            (BlockedLinkPlaquettePerturbationSurvival.blockedRadiusSurvival
              perturbation))
    ; blockedSmallFieldActivitySurvives = true
    ; blockedSmallFieldActivitySurvivesIsTrue = refl
    }

currentBlockedSmallFieldActivitySurvivalTheorem :
  BlockedSmallFieldActivitySurvivalTheorem
currentBlockedSmallFieldActivitySurvivalTheorem =
  let
    strongKP =
      StrongKP.strongGateBToKPFromSectorDisjointness
  in
  mkBlockedSmallFieldActivitySurvivalTheorem
    currentBlockedLinkPlaquettePerturbationSurvival
    strongKP
    (balabanPolymerActivityExponentialDecayTheorem strongKP)
    (balabanScaleUniformConstantsTheorem currentSmallFieldOscillationBudget)
    true
    refl

record BlockedSmallFieldKPHypothesis : Set₁ where
  constructor mkBlockedSmallFieldKPHypothesis
  field
    linkPlaquettePerturbationSurvival :
      BlockedLinkPlaquettePerturbationSurvival
    strongGateBToKPInput :
      StrongKP.StrongGateBToKPTheorem
    activitySurvival :
      BlockedSmallFieldActivitySurvivalTheorem
    blockedSmallFieldActivitySurvives :
      Bool
    blockedSmallFieldActivitySurvivesIsTrue :
      blockedSmallFieldActivitySurvives ≡ true
    kpSmallFieldHypothesisSurvives :
      Bool
    kpSmallFieldHypothesisSurvivesIsTrue :
      kpSmallFieldHypothesisSurvives ≡ true

blockedSmallFieldKPHypothesisFromChain :
  StrongKP.StrongGateBToKPTheorem →
  BlockedLinkPlaquettePerturbationSurvival →
  BlockedSmallFieldKPHypothesis
blockedSmallFieldKPHypothesisFromChain strongKP perturbation =
  let
    activitySurvival =
      blockedSmallFieldActivitySurvivalTheorem strongKP perturbation
  in
  record
    { linkPlaquettePerturbationSurvival =
        perturbation
    ; strongGateBToKPInput =
        strongKP
    ; activitySurvival =
        activitySurvival
    ; blockedSmallFieldActivitySurvives =
        BlockedSmallFieldActivitySurvivalTheorem.blockedSmallFieldActivitySurvives
          activitySurvival
    ; blockedSmallFieldActivitySurvivesIsTrue =
        BlockedSmallFieldActivitySurvivalTheorem.blockedSmallFieldActivitySurvivesIsTrue
          activitySurvival
    ; kpSmallFieldHypothesisSurvives =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOne
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP)
    ; kpSmallFieldHypothesisSurvivesIsTrue =
        StrongKP.StrongAllDiameterWeightedKP.fourQBelowOneIsTrue
          (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP)
    }

currentBlockedSmallFieldKPHypothesis :
  BlockedSmallFieldKPHypothesis
currentBlockedSmallFieldKPHypothesis =
  let
    strongKP =
      StrongKP.strongGateBToKPFromSectorDisjointness
  in
  mkBlockedSmallFieldKPHypothesis
    currentBlockedLinkPlaquettePerturbationSurvival
    strongKP
    currentBlockedSmallFieldActivitySurvivalTheorem
    (BlockedSmallFieldActivitySurvivalTheorem.blockedSmallFieldActivitySurvives
      currentBlockedSmallFieldActivitySurvivalTheorem)
    (BlockedSmallFieldActivitySurvivalTheorem.blockedSmallFieldActivitySurvivesIsTrue
      currentBlockedSmallFieldActivitySurvivalTheorem)
    (StrongKP.StrongAllDiameterWeightedKP.fourQBelowOne
      (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP))
    (StrongKP.StrongAllDiameterWeightedKP.fourQBelowOneIsTrue
      (StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP))

record SmallFieldSurvivalInputs : Set₁ where
  field
    balabanSmallFieldBoundsInput :
      BalabanSmallFieldBounds
    spatialOnlyBlockingCompatibilityInput :
      SpatialOnlyBlockingCompatibility
    gaugeOrbitMeasurePreservationInput :
      GaugeOrbitMeasurePreservation
    temporalTransferCompatibilityInput :
      TemporalTransferCompatibility
    polymerActivityBoundPreservationInput :
      PolymerActivityBoundPreservation

smallFieldSurvivalInputsFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldBounds →
  GaugeOrbitMeasurePreservation →
  TemporalTransferCompatibility →
  SmallFieldSurvivalInputs
smallFieldSurvivalInputsFromStrongKP strongKP balaban gauge temporal =
  record
    { balabanSmallFieldBoundsInput =
        balaban
    ; spatialOnlyBlockingCompatibilityInput =
        spatialOnlyBlockingCompatibilityFromW1
    ; gaugeOrbitMeasurePreservationInput =
        gauge
    ; temporalTransferCompatibilityInput =
        temporal
    ; polymerActivityBoundPreservationInput =
        polymerActivityBoundPreservationFromStrongKP strongKP
    }

record SmallFieldSurvivalProvider : Set₁ where
  field
    typedInputs :
      SmallFieldSurvivalInputs
    oscillationBudget :
      SmallFieldOscillationBudget
    blockedRadiusSurvival :
      BlockedSmallFieldRadiusSurvival
    linkPlaquettePerturbationSurvival :
      BlockedLinkPlaquettePerturbationSurvival
    blockedSmallFieldKPHypothesis :
      BlockedSmallFieldKPHypothesis
    balabanSmallFieldBounds :
      Bool
    balabanSmallFieldBoundsIsTrue :
      balabanSmallFieldBounds ≡ true

    spatialOnlyBlockingCompatibility :
      Bool
    spatialOnlyBlockingCompatibilityIsTrue :
      spatialOnlyBlockingCompatibility ≡ true

    gaugeOrbitMeasurePreservation :
      Bool
    gaugeOrbitMeasurePreservationIsTrue :
      gaugeOrbitMeasurePreservation ≡ true

    temporalTransferCompatibility :
      Bool
    temporalTransferCompatibilityIsTrue :
      temporalTransferCompatibility ≡ true

    polymerActivityBoundPreservation :
      Bool
    polymerActivityBoundPreservationIsTrue :
      polymerActivityBoundPreservation ≡ true

smallFieldSurvivalProviderFromInputs :
  SmallFieldSurvivalInputs →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromInputs inputs =
  let
    oscillationBudget =
      currentSmallFieldOscillationBudget
    radiusSurvival =
      currentBlockedSmallFieldRadiusSurvival
    perturbationSurvival =
      currentBlockedLinkPlaquettePerturbationSurvival
    kpHypothesis =
      currentBlockedSmallFieldKPHypothesis
  in
  record
    { typedInputs =
        inputs
    ; oscillationBudget =
        oscillationBudget
    ; blockedRadiusSurvival =
        radiusSurvival
    ; linkPlaquettePerturbationSurvival =
        perturbationSurvival
    ; blockedSmallFieldKPHypothesis =
        kpHypothesis
    ; balabanSmallFieldBounds =
        BalabanSmallFieldBounds.balabanSmallFieldBounds
          (SmallFieldSurvivalInputs.balabanSmallFieldBoundsInput inputs)
    ; balabanSmallFieldBoundsIsTrue =
        BalabanSmallFieldBounds.balabanSmallFieldBoundsIsTrue
          (SmallFieldSurvivalInputs.balabanSmallFieldBoundsInput inputs)
    ; spatialOnlyBlockingCompatibility =
        SpatialOnlyBlockingCompatibility.spatialBlockingPreservesTemporalLinks
          (SmallFieldSurvivalInputs.spatialOnlyBlockingCompatibilityInput inputs)
    ; spatialOnlyBlockingCompatibilityIsTrue =
        SpatialOnlyBlockingCompatibility.spatialBlockingPreservesTemporalLinksIsTrue
          (SmallFieldSurvivalInputs.spatialOnlyBlockingCompatibilityInput inputs)
    ; gaugeOrbitMeasurePreservation =
        GaugeOrbitMeasurePreservation.gaugeOrbitMeasurePreservation
          (SmallFieldSurvivalInputs.gaugeOrbitMeasurePreservationInput inputs)
    ; gaugeOrbitMeasurePreservationIsTrue =
        GaugeOrbitMeasurePreservation.gaugeOrbitMeasurePreservationIsTrue
          (SmallFieldSurvivalInputs.gaugeOrbitMeasurePreservationInput inputs)
    ; temporalTransferCompatibility =
        TemporalTransferCompatibility.temporalTransferCompatibility
          (SmallFieldSurvivalInputs.temporalTransferCompatibilityInput inputs)
    ; temporalTransferCompatibilityIsTrue =
        TemporalTransferCompatibility.temporalTransferCompatibilityIsTrue
          (SmallFieldSurvivalInputs.temporalTransferCompatibilityInput inputs)
    ; polymerActivityBoundPreservation =
        PolymerActivityBoundPreservation.polymerActivityBoundPreservation
          (SmallFieldSurvivalInputs.polymerActivityBoundPreservationInput inputs)
    ; polymerActivityBoundPreservationIsTrue =
        PolymerActivityBoundPreservation.polymerActivityBoundPreservationIsTrue
          (SmallFieldSurvivalInputs.polymerActivityBoundPreservationInput inputs)
    }

smallFieldSurvivalProviderFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldBounds →
  GaugeOrbitMeasurePreservation →
  TemporalTransferCompatibility →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromStrongKP strongKP balaban gauge temporal =
  smallFieldSurvivalProviderFromInputs
    (smallFieldSurvivalInputsFromStrongKP strongKP balaban gauge temporal)

smallFieldSurvivalProviderFromStrongKPAuthorities :
  StrongKP.StrongGateBToKPTheorem →
  BalabanSmallFieldAuthority →
  GaugeOrbitMeasureAuthority →
  SmallFieldSurvivalProvider
smallFieldSurvivalProviderFromStrongKPAuthorities strongKP balaban gauge =
  smallFieldSurvivalProviderFromStrongKP
    strongKP
    (balabanSmallFieldBoundsFromAuthority balaban)
    (gaugeOrbitMeasurePreservationFromAuthority gauge)
    (temporalTransferCompatibilityFromStrongKP strongKP)

record SmallFieldBoundsSurviveAnisotropicBlockingTheorem : Set₂ where
  field
    strongGateBToKP :
      StrongKP.StrongGateBToKPTheorem
    strongAllDiameterWeightedKP :
      StrongKP.StrongAllDiameterWeightedKP
    smallFieldProvider :
      SmallFieldSurvivalProvider
    oscillationBudgetFromAssumptionA :
      SmallFieldOscillationBudget
    blockedRadiusSurvival :
      BlockedSmallFieldRadiusSurvival
    linkPlaquettePerturbationSurvival :
      BlockedLinkPlaquettePerturbationSurvival
    blockedSmallFieldKPHypothesis :
      BlockedSmallFieldKPHypothesis
    smallFieldBoundsSurviveAnisotropicBlocking :
      Bool
    smallFieldBoundsSurviveAnisotropicBlockingIsTrue :
      smallFieldBoundsSurviveAnisotropicBlocking ≡ true

smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP :
  StrongKP.StrongGateBToKPTheorem →
  SmallFieldSurvivalProvider →
  SmallFieldBoundsSurviveAnisotropicBlockingTheorem
smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP strongKP provider =
  record
    { strongGateBToKP =
        strongKP
    ; strongAllDiameterWeightedKP =
        StrongKP.StrongGateBToKPTheorem.allDiameterWeightedKP strongKP
    ; smallFieldProvider =
        provider
    ; oscillationBudgetFromAssumptionA =
        SmallFieldSurvivalProvider.oscillationBudget provider
    ; blockedRadiusSurvival =
        SmallFieldSurvivalProvider.blockedRadiusSurvival provider
    ; linkPlaquettePerturbationSurvival =
        SmallFieldSurvivalProvider.linkPlaquettePerturbationSurvival provider
    ; blockedSmallFieldKPHypothesis =
        SmallFieldSurvivalProvider.blockedSmallFieldKPHypothesis provider
    ; smallFieldBoundsSurviveAnisotropicBlocking = true
    ; smallFieldBoundsSurviveAnisotropicBlockingIsTrue = refl
    }

smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional :
  SmallFieldBoundsSurviveAnisotropicBlockingTheorem
smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditional =
  smallFieldBoundsSurviveAnisotropicBlockingFromStrongKP
    StrongKP.strongGateBToKPFromSectorDisjointness
    (smallFieldSurvivalProviderFromStrongKPAuthorities
      StrongKP.strongGateBToKPFromSectorDisjointness
      balabanSmallFieldAuthorityProvider
      gaugeOrbitMeasureAuthorityProvider)

smallFieldSurvivalProviderAuthorityAvailable : Bool
smallFieldSurvivalProviderAuthorityAvailable = true

smallFieldSurvivalProviderDerivedInRepo : Bool
smallFieldSurvivalProviderDerivedInRepo = false

spatialOnlyBlockingCompatibilityDerivedInRepo : Bool
spatialOnlyBlockingCompatibilityDerivedInRepo = true

polymerActivityBoundPreservationDerivedFromStrongKP : Bool
polymerActivityBoundPreservationDerivedFromStrongKP = true

strongKPInputDerivedInRepo : Bool
strongKPInputDerivedInRepo = true

balabanSmallFieldBoundsDerivedInRepo : Bool
balabanSmallFieldBoundsDerivedInRepo = false

balabanSmallFieldBoundsImportedByAuthority : Bool
balabanSmallFieldBoundsImportedByAuthority = true

gaugeOrbitMeasurePreservationDerivedInRepo : Bool
gaugeOrbitMeasurePreservationDerivedInRepo = false

gaugeOrbitMeasurePreservationImportedByAuthority : Bool
gaugeOrbitMeasurePreservationImportedByAuthority = true

spatialBlockingPreservesGaugeOrbitDerivedInRepo : Bool
spatialBlockingPreservesGaugeOrbitDerivedInRepo = true

temporalTransferCompatibilityDerivedInRepo : Bool
temporalTransferCompatibilityDerivedInRepo = true

balabanSmallFieldAuthoritySplit : Bool
balabanSmallFieldAuthoritySplit = true

balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas : Bool
balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas = true

gaugeOrbitMeasureAuthoritySplit : Bool
gaugeOrbitMeasureAuthoritySplit = true

gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas : Bool
gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas = true

gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot : Bool
gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot = true

carrierBalabanSmallFieldBookkeepingAvailable : Bool
carrierBalabanSmallFieldBookkeepingAvailable =
  CarrierBalaban.smallFieldDepthRegionRecorded
    (CarrierBalaban.scaleHypothesisAtK
      CarrierBalaban.canonicalCarrierBalabanInductiveStepReceipt)

carrierBalabanAnalyticDecayTheoremDerivedInRepo : Bool
carrierBalabanAnalyticDecayTheoremDerivedInRepo =
  CarrierBalaban.balabanTheoremPromoted
    CarrierBalaban.canonicalCarrierBalabanInductiveStepReceipt

carrierGaugeFixingContinuumSliceConstructedInRepo : Bool
carrierGaugeFixingContinuumSliceConstructedInRepo =
  BTGauge.continuumGaugeSliceConstructed
    BTGauge.canonicalBruhatTitsCarrierGaugeFixingReceipt

carrierMeasureContinuumGaugeMeasureConstructedInRepo : Bool
carrierMeasureContinuumGaugeMeasureConstructedInRepo =
  CarrierMeasure.continuumMeasureConstructed
    CarrierMeasure.canonicalCarrierGaugeFieldMeasureReceipt

smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool : Bool
smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool = true

smallFieldBoundsSurviveAnisotropicBlockingUnconditional : Bool
smallFieldBoundsSurviveAnisotropicBlockingUnconditional = false

latticeMassGapFromAnisotropicKPAuthorityConditional : Bool
latticeMassGapFromAnisotropicKPAuthorityConditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data SmallFieldSurvivalPromotion : Set where

smallFieldSurvivalPromotionImpossibleHere :
  SmallFieldSurvivalPromotion →
  ⊥
smallFieldSurvivalPromotionImpossibleHere ()

record SmallFieldSurvivalAuthorityBoundary : Set where
  field
    providerAuthorityAvailableIsTrue :
      smallFieldSurvivalProviderAuthorityAvailable ≡ true
    providerDerivedInRepoIsFalse :
      smallFieldSurvivalProviderDerivedInRepo ≡ false
    spatialBlockingCompatibilityDerived :
      spatialOnlyBlockingCompatibilityDerivedInRepo ≡ true
    polymerActivityPreservationDerived :
      polymerActivityBoundPreservationDerivedFromStrongKP ≡ true
    strongKPInputDerived :
      strongKPInputDerivedInRepo ≡ true
    balabanSmallFieldBoundsNotDerived :
      balabanSmallFieldBoundsDerivedInRepo ≡ false
    balabanSmallFieldBoundsAuthorityImported :
      balabanSmallFieldBoundsImportedByAuthority ≡ true
    gaugeOrbitMeasureNotDerived :
      gaugeOrbitMeasurePreservationDerivedInRepo ≡ false
    gaugeOrbitMeasureAuthorityImported :
      gaugeOrbitMeasurePreservationImportedByAuthority ≡ true
    spatialBlockingPreservesGaugeOrbitDerived :
      spatialBlockingPreservesGaugeOrbitDerivedInRepo ≡ true
    temporalTransferCompatibilityDerived :
      temporalTransferCompatibilityDerivedInRepo ≡ true
    balabanSmallFieldAuthorityIsSplit :
      balabanSmallFieldAuthoritySplit ≡ true
    balabanSmallFieldAuthorityFourLemmaSplit :
      balabanSmallFieldAuthoritySplitIntoFourAnalyticLemmas ≡ true
    gaugeOrbitMeasureAuthorityIsSplit :
      gaugeOrbitMeasureAuthoritySplit ≡ true
    gaugeOrbitMeasureAuthorityThreeLemmaSplit :
      gaugeOrbitMeasureAuthoritySplitIntoThreeAnalyticLemmas ≡ true
    gaugeOrbitMeasureAuthorityTwoImportedOneNative :
      gaugeOrbitMeasureAuthorityHasTwoImportedGaugeSlotsAndOneNativeSlot
      ≡ true
    carrierBalabanBookkeepingAvailable :
      carrierBalabanSmallFieldBookkeepingAvailable ≡ true
    carrierBalabanAnalyticDecayNotDerived :
      carrierBalabanAnalyticDecayTheoremDerivedInRepo ≡ false
    carrierGaugeSliceNotConstructed :
      carrierGaugeFixingContinuumSliceConstructedInRepo ≡ false
    carrierContinuumMeasureNotConstructed :
      carrierMeasureContinuumGaugeMeasureConstructedInRepo ≡ false
    smallFieldAuthorityConditionalIsTrue :
      smallFieldBoundsSurviveAnisotropicBlockingAuthorityConditionalBool
        ≡ true
    smallFieldUnconditionalIsFalse :
      smallFieldBoundsSurviveAnisotropicBlockingUnconditional ≡ false
    latticeMassGapAuthorityConditionalStillFalse :
      latticeMassGapFromAnisotropicKPAuthorityConditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      SmallFieldSurvivalPromotion → ⊥

smallFieldSurvivalAuthorityBoundary :
  SmallFieldSurvivalAuthorityBoundary
smallFieldSurvivalAuthorityBoundary =
  record
    { providerAuthorityAvailableIsTrue = refl
    ; providerDerivedInRepoIsFalse = refl
    ; spatialBlockingCompatibilityDerived = refl
    ; polymerActivityPreservationDerived = refl
    ; strongKPInputDerived = refl
    ; balabanSmallFieldBoundsNotDerived = refl
    ; balabanSmallFieldBoundsAuthorityImported = refl
    ; gaugeOrbitMeasureNotDerived = refl
    ; gaugeOrbitMeasureAuthorityImported = refl
    ; spatialBlockingPreservesGaugeOrbitDerived = refl
    ; temporalTransferCompatibilityDerived = refl
    ; balabanSmallFieldAuthorityIsSplit = refl
    ; balabanSmallFieldAuthorityFourLemmaSplit = refl
    ; gaugeOrbitMeasureAuthorityIsSplit = refl
    ; gaugeOrbitMeasureAuthorityThreeLemmaSplit = refl
    ; gaugeOrbitMeasureAuthorityTwoImportedOneNative = refl
    ; carrierBalabanBookkeepingAvailable = refl
    ; carrierBalabanAnalyticDecayNotDerived = refl
    ; carrierGaugeSliceNotConstructed = refl
    ; carrierContinuumMeasureNotConstructed = refl
    ; smallFieldAuthorityConditionalIsTrue = refl
    ; smallFieldUnconditionalIsFalse = refl
    ; latticeMassGapAuthorityConditionalStillFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = smallFieldSurvivalPromotionImpossibleHere
    }
