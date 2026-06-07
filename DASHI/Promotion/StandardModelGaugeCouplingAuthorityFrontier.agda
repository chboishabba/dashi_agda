module DASHI.Promotion.StandardModelGaugeCouplingAuthorityFrontier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAuthorityPayloadValidator as Payload
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Norm

------------------------------------------------------------------------
-- Standard Model gauge-coupling authority frontier.
--
-- This module names the calibration and authority boundaries for SM gauge
-- couplings and running.  It carries no measured numeric values, no parsed
-- payloads, and no physical Standard Model promotion.  All consumer-facing
-- rows are metadata receipts that must be inhabited by PDG/CODATA payloads,
-- scheme/scale receipts, threshold-matching receipts, and collider
-- observable validation before any derived coupling may be used.

data GaugeCouplingSymbol : Set where
  g1 : GaugeCouplingSymbol
  g2 : GaugeCouplingSymbol
  g3 : GaugeCouplingSymbol
  alphaEM : GaugeCouplingSymbol
  alphaS : GaugeCouplingSymbol
  weakMixingAngle : GaugeCouplingSymbol

data GaugeGroupFactor : Set where
  u1Hypercharge : GaugeGroupFactor
  su2Left : GaugeGroupFactor
  su3Color : GaugeGroupFactor
  electroweakMixed : GaugeGroupFactor
  qcdStrong : GaugeGroupFactor

data RenormalizationScheme : Set where
  onShellScheme : RenormalizationScheme
  msbarScheme : RenormalizationScheme
  drbarScheme : RenormalizationScheme
  latticeQCDScheme : RenormalizationScheme
  authoritySpecifiedScheme : RenormalizationScheme

data ScaleBoundary : Set where
  zeroMomentumThomsonLimit : ScaleBoundary
  zPoleScale : ScaleBoundary
  wPoleScale : ScaleBoundary
  higgsPoleScale : ScaleBoundary
  topPoleScale : ScaleBoundary
  tauMassScale : ScaleBoundary
  colliderProcessScale : ScaleBoundary
  authorityDeclaredScale : ScaleBoundary

data GaugeAuthorityProvider : Set where
  codataAuthority : GaugeAuthorityProvider
  pdgAuthority : GaugeAuthorityProvider
  codataPDGCrossAuthority : GaugeAuthorityProvider
  colliderExperimentAuthority : GaugeAuthorityProvider
  theoryConventionAuthority : GaugeAuthorityProvider

data BoundaryStatus : Set where
  metadataOnly : BoundaryStatus
  authorityPayloadRequired : BoundaryStatus
  schemeReceiptRequired : BoundaryStatus
  thresholdReceiptRequired : BoundaryStatus
  betaFunctionReceiptRequired : BoundaryStatus
  colliderValidationRequired : BoundaryStatus

data ColliderObservableConsumer : Set where
  lepSLCZPoleConsumer : ColliderObservableConsumer
  tevatronWTopConsumer : ColliderObservableConsumer
  lhcElectroweakConsumer : ColliderObservableConsumer
  lhcJetQCDConsumer : ColliderObservableConsumer
  higgsRateConsumer : ColliderObservableConsumer
  globalSMFitConsumer : ColliderObservableConsumer

symbolLabel : GaugeCouplingSymbol → String
symbolLabel g1 = "g1"
symbolLabel g2 = "g2"
symbolLabel g3 = "g3"
symbolLabel alphaEM = "alpha_em"
symbolLabel alphaS = "alpha_s"
symbolLabel weakMixingAngle = "sin^2 theta_W / weak mixing angle"

record GaugeCouplingInputRow : Set₁ where
  field
    couplingSymbol : GaugeCouplingSymbol
    displayLabel : String
    displayLabelIsCanonical :
      displayLabel ≡ symbolLabel couplingSymbol
    gaugeFactor : GaugeGroupFactor
    authorityProvider : GaugeAuthorityProvider
    authorityTokenReference : String
    normalizedTokenReference : String
    payloadValidatorReference : String
    renormalizationScheme : RenormalizationScheme
    scaleBoundary : ScaleBoundary
    status : BoundaryStatus
    derivedFromOtherInputs : Bool
    derivedFromOtherInputsIsFalse :
      derivedFromOtherInputs ≡ false
    measuredNumericValueLoaded : Bool
    measuredNumericValueLoadedIsFalse :
      measuredNumericValueLoaded ≡ false
    derivedGaugeCouplingPromoted : Bool
    derivedGaugeCouplingPromotedIsFalse :
      derivedGaugeCouplingPromoted ≡ false

open GaugeCouplingInputRow public

mkGaugeInput :
  GaugeCouplingSymbol →
  GaugeGroupFactor →
  GaugeAuthorityProvider →
  String →
  String →
  RenormalizationScheme →
  ScaleBoundary →
  BoundaryStatus →
  GaugeCouplingInputRow
mkGaugeInput sym factor provider token normToken scheme scale status =
  record
    { couplingSymbol = sym
    ; displayLabel = symbolLabel sym
    ; displayLabelIsCanonical = refl
    ; gaugeFactor = factor
    ; authorityProvider = provider
    ; authorityTokenReference = token
    ; normalizedTokenReference = normToken
    ; payloadValidatorReference =
        "DASHI.Promotion.NumericAuthorityPayloadValidator"
    ; renormalizationScheme = scheme
    ; scaleBoundary = scale
    ; status = status
    ; derivedFromOtherInputs = false
    ; derivedFromOtherInputsIsFalse = refl
    ; measuredNumericValueLoaded = false
    ; measuredNumericValueLoadedIsFalse = refl
    ; derivedGaugeCouplingPromoted = false
    ; derivedGaugeCouplingPromotedIsFalse = refl
    }

canonicalGaugeCouplingInputs : List GaugeCouplingInputRow
canonicalGaugeCouplingInputs =
  mkGaugeInput
    g1
    u1Hypercharge
    pdgAuthority
    "PDG electroweak fit token for GUT-normalized U1Y coupling"
    "string-reference: NumericMeasuredAuthorityTokenNormalization.wzMassesNormalizedToken / fermiCouplingNormalizedToken"
    msbarScheme
    zPoleScale
    authorityPayloadRequired
  ∷ mkGaugeInput
    g2
    su2Left
    pdgAuthority
    "PDG electroweak fit token for SU2L coupling"
    "string-reference: NumericMeasuredAuthorityTokenNormalization.wzMassesNormalizedToken / fermiCouplingNormalizedToken"
    msbarScheme
    zPoleScale
    authorityPayloadRequired
  ∷ mkGaugeInput
    g3
    su3Color
    pdgAuthority
    "PDG alpha_s token with QCD scheme and scale"
    "NumericMeasuredAuthorityTokenNormalization.alphaSNormalizedToken"
    msbarScheme
    zPoleScale
    authorityPayloadRequired
  ∷ mkGaugeInput
    alphaEM
    electroweakMixed
    codataPDGCrossAuthority
    "CODATA alpha token plus PDG electroweak conversion boundary"
    "NumericMeasuredAuthorityTokenNormalization.alphaNormalizedToken"
    onShellScheme
    zeroMomentumThomsonLimit
    authorityPayloadRequired
  ∷ mkGaugeInput
    alphaS
    qcdStrong
    pdgAuthority
    "PDG alpha_s(M_Z) authority row"
    "NumericMeasuredAuthorityTokenNormalization.alphaSNormalizedToken"
    msbarScheme
    zPoleScale
    authorityPayloadRequired
  ∷ mkGaugeInput
    weakMixingAngle
    electroweakMixed
    pdgAuthority
    "PDG weak mixing angle and electroweak-fit convention row"
    "string-reference: NumericMeasuredAuthorityTokenNormalization.wzMassesNormalizedToken / fermiCouplingNormalizedToken"
    authoritySpecifiedScheme
    zPoleScale
    schemeReceiptRequired
  ∷ []

record RunningBoundaryRow : Set₁ where
  field
    runningLabel : String
    couplingSymbol : GaugeCouplingSymbol
    sourceScale : ScaleBoundary
    targetScale : ScaleBoundary
    renormalizationScheme : RenormalizationScheme
    requiredReceipts : List String
    thresholdRowsRequired : List String
    status : BoundaryStatus
    runningMapAccepted : Bool
    runningMapAcceptedIsFalse :
      runningMapAccepted ≡ false
    numericRunningPayloadLoaded : Bool
    numericRunningPayloadLoadedIsFalse :
      numericRunningPayloadLoaded ≡ false

open RunningBoundaryRow public

mkRunningBoundary :
  String →
  GaugeCouplingSymbol →
  ScaleBoundary →
  ScaleBoundary →
  RenormalizationScheme →
  BoundaryStatus →
  List String →
  List String →
  RunningBoundaryRow
mkRunningBoundary label sym source target scheme status receipts thresholds =
  record
    { runningLabel = label
    ; couplingSymbol = sym
    ; sourceScale = source
    ; targetScale = target
    ; renormalizationScheme = scheme
    ; requiredReceipts = receipts
    ; thresholdRowsRequired = thresholds
    ; status = status
    ; runningMapAccepted = false
    ; runningMapAcceptedIsFalse = refl
    ; numericRunningPayloadLoaded = false
    ; numericRunningPayloadLoadedIsFalse = refl
    }

canonicalRunningBoundaries : List RunningBoundaryRow
canonicalRunningBoundaries =
  mkRunningBoundary
    "alpha_em Thomson-limit to Z-pole running boundary"
    alphaEM
    zeroMomentumThomsonLimit
    zPoleScale
    msbarScheme
    betaFunctionReceiptRequired
    ( "leptonic vacuum-polarization receipt"
    ∷ "hadronic vacuum-polarization authority receipt"
    ∷ "scheme conversion receipt"
    ∷ []
    )
    ( "electron, muon, tau thresholds"
    ∷ "light-quark hadronic threshold model"
    ∷ []
    )
  ∷ mkRunningBoundary
    "alpha_s Z-pole to collider-process scale boundary"
    alphaS
    zPoleScale
    colliderProcessScale
    msbarScheme
    thresholdReceiptRequired
    ( "QCD beta-function coefficient receipt"
    ∷ "quark-flavour threshold matching receipt"
    ∷ "PDG alpha_s authority payload"
    ∷ []
    )
    ( "charm threshold"
    ∷ "bottom threshold"
    ∷ "top threshold"
    ∷ []
    )
  ∷ mkRunningBoundary
    "g1 electroweak fit scale boundary"
    g1
    zPoleScale
    colliderProcessScale
    msbarScheme
    betaFunctionReceiptRequired
    ( "U1Y normalization convention"
    ∷ "electroweak beta-function receipt"
    ∷ "SM particle-content threshold receipt"
    ∷ []
    )
    ( "W/Z/H/top thresholds"
    ∷ []
    )
  ∷ mkRunningBoundary
    "g2 electroweak fit scale boundary"
    g2
    zPoleScale
    colliderProcessScale
    msbarScheme
    betaFunctionReceiptRequired
    ( "SU2L generator-normalization receipt"
    ∷ "electroweak beta-function receipt"
    ∷ "SM particle-content threshold receipt"
    ∷ []
    )
    ( "W/Z/H/top thresholds"
    ∷ []
    )
  ∷ mkRunningBoundary
    "g3 top-threshold matching boundary"
    g3
    zPoleScale
    topPoleScale
    msbarScheme
    thresholdReceiptRequired
    ( "six-flavour QCD matching convention"
    ∷ "top mass authority payload"
    ∷ "PDG alpha_s authority payload"
    ∷ []
    )
    ( "top threshold"
    ∷ []
    )
  ∷ []

record BetaFunctionAuthorityRow : Set₁ where
  field
    betaLabel : String
    appliesTo : GaugeCouplingSymbol
    loopOrderBoundary : String
    schemeBoundary : RenormalizationScheme
    coefficientAuthority : String
    particleContentBoundary : String
    status : BoundaryStatus
    coefficientPayloadAccepted : Bool
    coefficientPayloadAcceptedIsFalse :
      coefficientPayloadAccepted ≡ false
    promotesRunningLaw : Bool
    promotesRunningLawIsFalse :
      promotesRunningLaw ≡ false

open BetaFunctionAuthorityRow public

mkBetaRow :
  String →
  GaugeCouplingSymbol →
  String →
  RenormalizationScheme →
  String →
  String →
  BetaFunctionAuthorityRow
mkBetaRow label sym loops scheme authority content =
  record
    { betaLabel = label
    ; appliesTo = sym
    ; loopOrderBoundary = loops
    ; schemeBoundary = scheme
    ; coefficientAuthority = authority
    ; particleContentBoundary = content
    ; status = betaFunctionReceiptRequired
    ; coefficientPayloadAccepted = false
    ; coefficientPayloadAcceptedIsFalse = refl
    ; promotesRunningLaw = false
    ; promotesRunningLawIsFalse = refl
    }

canonicalBetaFunctionAuthorityRows : List BetaFunctionAuthorityRow
canonicalBetaFunctionAuthorityRows =
  mkBetaRow
    "U1Y beta-function coefficient boundary"
    g1
    "one-loop through requested perturbative order; coefficients external"
    msbarScheme
    "PDG/review or cited perturbative-SM authority"
    "SM particle content, hypercharge normalization, threshold policy"
  ∷ mkBetaRow
    "SU2L beta-function coefficient boundary"
    g2
    "one-loop through requested perturbative order; coefficients external"
    msbarScheme
    "PDG/review or cited perturbative-SM authority"
    "SM particle content, Higgs and fermion generation convention"
  ∷ mkBetaRow
    "SU3c beta-function coefficient boundary"
    g3
    "QCD beta function with active-flavour count"
    msbarScheme
    "PDG alpha_s review / perturbative-QCD authority"
    "active quark flavours and threshold matching convention"
  ∷ mkBetaRow
    "alpha_s beta-function coefficient boundary"
    alphaS
    "QCD beta function for alpha_s(mu)"
    msbarScheme
    "PDG alpha_s review / perturbative-QCD authority"
    "active quark flavours, decoupling, and collider-scale policy"
  ∷ []

record ElectroweakInputRow : Set₁ where
  field
    inputLabel : String
    symbol : String
    authorityProvider : GaugeAuthorityProvider
    normalizedTokenReference : String
    useForCouplings : List GaugeCouplingSymbol
    status : BoundaryStatus
    numericValueLoaded : Bool
    numericValueLoadedIsFalse :
      numericValueLoaded ≡ false
    calibrationPromoted : Bool
    calibrationPromotedIsFalse :
      calibrationPromoted ≡ false

open ElectroweakInputRow public

mkEWInput :
  String →
  String →
  GaugeAuthorityProvider →
  String →
  List GaugeCouplingSymbol →
  BoundaryStatus →
  ElectroweakInputRow
mkEWInput label sym provider token consumers status =
  record
    { inputLabel = label
    ; symbol = sym
    ; authorityProvider = provider
    ; normalizedTokenReference = token
    ; useForCouplings = consumers
    ; status = status
    ; numericValueLoaded = false
    ; numericValueLoadedIsFalse = refl
    ; calibrationPromoted = false
    ; calibrationPromotedIsFalse = refl
    }

canonicalElectroweakInputs : List ElectroweakInputRow
canonicalElectroweakInputs =
  mkEWInput
    "fine-structure constant authority input"
    "alpha"
    codataAuthority
    "NumericMeasuredAuthorityTokenNormalization.alphaNormalizedToken"
    ( alphaEM ∷ g1 ∷ g2 ∷ weakMixingAngle ∷ [] )
    authorityPayloadRequired
  ∷ mkEWInput
    "Fermi coupling authority input"
    "G_F"
    codataPDGCrossAuthority
    "NumericMeasuredAuthorityTokenNormalization.fermiCouplingNormalizedToken"
    ( g2 ∷ weakMixingAngle ∷ [] )
    authorityPayloadRequired
  ∷ mkEWInput
    "W/Z mass authority input"
    "m_W, m_Z"
    pdgAuthority
    "NumericMeasuredAuthorityTokenNormalization.wzMassesNormalizedToken"
    ( g1 ∷ g2 ∷ weakMixingAngle ∷ [] )
    authorityPayloadRequired
  ∷ mkEWInput
    "Higgs mass authority input"
    "m_H"
    pdgAuthority
    "NumericMeasuredAuthorityTokenNormalization.higgsMassNormalizedToken"
    ( g1 ∷ g2 ∷ [] )
    authorityPayloadRequired
  ∷ mkEWInput
    "top mass and quark-threshold authority input"
    "m_t / quark masses"
    pdgAuthority
    "NumericMeasuredAuthorityTokenNormalization.quarkMassesNormalizedToken"
    ( g1 ∷ g2 ∷ g3 ∷ alphaS ∷ [] )
    thresholdReceiptRequired
  ∷ []

record ColliderConsumerRow : Set₁ where
  field
    consumer : ColliderObservableConsumer
    consumerLabel : String
    consumedCouplings : List GaugeCouplingSymbol
    requiredAuthorityRows : List String
    observableBoundary : String
    status : BoundaryStatus
    observableCalibrationAccepted : Bool
    observableCalibrationAcceptedIsFalse :
      observableCalibrationAccepted ≡ false
    empiricalAdequacyAccepted : Bool
    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false

open ColliderConsumerRow public

mkConsumer :
  ColliderObservableConsumer →
  String →
  List GaugeCouplingSymbol →
  List String →
  String →
  ColliderConsumerRow
mkConsumer consumer label couplings rows boundary =
  record
    { consumer = consumer
    ; consumerLabel = label
    ; consumedCouplings = couplings
    ; requiredAuthorityRows = rows
    ; observableBoundary = boundary
    ; status = colliderValidationRequired
    ; observableCalibrationAccepted = false
    ; observableCalibrationAcceptedIsFalse = refl
    ; empiricalAdequacyAccepted = false
    ; empiricalAdequacyAcceptedIsFalse = refl
    }

canonicalColliderConsumers : List ColliderConsumerRow
canonicalColliderConsumers =
  mkConsumer
    lepSLCZPoleConsumer
    "LEP/SLC Z-pole electroweak observables"
    ( g1 ∷ g2 ∷ alphaEM ∷ weakMixingAngle ∷ [] )
    ( "PDG Z-pole electroweak fit token"
    ∷ "scheme and covariance receipt"
    ∷ "radiative-correction convention receipt"
    ∷ []
    )
    "Z widths, asymmetries, and effective weak mixing angle"
  ∷ mkConsumer
    tevatronWTopConsumer
    "Tevatron W/top calibration consumers"
    ( g2 ∷ g3 ∷ alphaS ∷ [] )
    ( "W mass authority row"
    ∷ "top mass authority row"
    ∷ "QCD threshold matching row"
    ∷ []
    )
    "W mass, top cross sections, and top mass scheme boundary"
  ∷ mkConsumer
    lhcElectroweakConsumer
    "LHC electroweak precision consumers"
    ( g1 ∷ g2 ∷ alphaEM ∷ weakMixingAngle ∷ [] )
    ( "PDG/CODATA electroweak input receipt"
    ∷ "LHC detector calibration receipt"
    ∷ "fiducial observable definition"
    ∷ []
    )
    "W/Z production, diboson, and electroweak fit observables"
  ∷ mkConsumer
    lhcJetQCDConsumer
    "LHC jet and QCD alpha_s consumers"
    ( g3 ∷ alphaS ∷ [] )
    ( "PDG alpha_s authority row"
    ∷ "jet energy scale calibration"
    ∷ "PDF and scale-variation receipt"
    ∷ []
    )
    "inclusive jets, event shapes, and high-scale alpha_s extraction"
  ∷ mkConsumer
    higgsRateConsumer
    "Higgs rate and branching-ratio consumers"
    ( g1 ∷ g2 ∷ g3 ∷ alphaEM ∷ alphaS ∷ [] )
    ( "Higgs mass authority row"
    ∷ "electroweak input scheme receipt"
    ∷ "QCD correction and alpha_s receipt"
    ∷ []
    )
    "production cross sections, partial widths, and branching ratios"
  ∷ mkConsumer
    globalSMFitConsumer
    "global Standard Model fit consumer"
    ( g1 ∷ g2 ∷ g3 ∷ alphaEM ∷ alphaS ∷ weakMixingAngle ∷ [] )
    ( "complete PDG/CODATA authority envelope"
    ∷ "covariance matrix or independence receipt"
    ∷ "holdout and residual policy"
    ∷ []
    )
    "global likelihood fit over electroweak, Higgs, top, and QCD data"
  ∷ []

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record StandardModelGaugeCouplingAuthorityReceipt : Set₁ where
  field
    receiptLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourcePayloadValidatorReceipt :
      Payload.NumericAuthorityPayloadValidatorReceipt
    alphaNormalizedToken : Norm.NormalizedMeasuredAuthorityToken
    alphaSNormalizedToken : Norm.NormalizedMeasuredAuthorityToken
    gaugeCouplingInputs : List GaugeCouplingInputRow
    runningBoundaries : List RunningBoundaryRow
    betaFunctionAuthorityRows : List BetaFunctionAuthorityRow
    electroweakInputs : List ElectroweakInputRow
    colliderConsumers : List ColliderConsumerRow
    gaugeCouplingInputCount : Nat
    gaugeCouplingInputCountIs6 :
      gaugeCouplingInputCount ≡ 6
    runningBoundaryCount : Nat
    runningBoundaryCountIs5 :
      runningBoundaryCount ≡ 5
    betaFunctionAuthorityRowCount : Nat
    betaFunctionAuthorityRowCountIs4 :
      betaFunctionAuthorityRowCount ≡ 4
    electroweakInputCount : Nat
    electroweakInputCountIs5 :
      electroweakInputCount ≡ 5
    colliderConsumerCount : Nat
    colliderConsumerCountIs6 :
      colliderConsumerCount ≡ 6
    payloadEnvelopeCountCrossCheck : Nat
    payloadEnvelopeCountCrossCheckIs18 :
      payloadEnvelopeCountCrossCheck ≡ 18
    payloadAcceptedAuthorityTokenPresent : Bool
    payloadAcceptedAuthorityTokenPresentIsFalse :
      payloadAcceptedAuthorityTokenPresent ≡ false
    payloadNumericValueLoaded : Bool
    payloadNumericValueLoadedIsFalse :
      payloadNumericValueLoaded ≡ false
    registryPhysicalLawDerived : Bool
    registryPhysicalLawDerivedIsFalse :
      registryPhysicalLawDerived ≡ false
    registryCalibrationPromoted : Bool
    registryCalibrationPromotedIsFalse :
      registryCalibrationPromoted ≡ false
    registryEmpiricalAdequacyAccepted : Bool
    registryEmpiricalAdequacyAcceptedIsFalse :
      registryEmpiricalAdequacyAccepted ≡ false
    derivedGaugeCouplingsPromoted : Bool
    derivedGaugeCouplingsPromotedIsFalse :
      derivedGaugeCouplingsPromoted ≡ false
    physicalStandardModelPromoted : Bool
    physicalStandardModelPromotedIsFalse :
      physicalStandardModelPromoted ≡ false
    empiricalAdequacyPromoted : Bool
    empiricalAdequacyPromotedIsFalse :
      empiricalAdequacyPromoted ≡ false
    falseDerivedGaugeCouplingGuard : Bool
    falseDerivedGaugeCouplingGuardIsTrue :
      falseDerivedGaugeCouplingGuard ≡ true
    falsePhysicalSMPromotionGuard : Bool
    falsePhysicalSMPromotionGuardIsTrue :
      falsePhysicalSMPromotionGuard ≡ true
    falseEmpiricalAdequacyGuard : Bool
    falseEmpiricalAdequacyGuardIsTrue :
      falseEmpiricalAdequacyGuard ≡ true
    frontierNotes : List String

open StandardModelGaugeCouplingAuthorityReceipt public

canonicalStandardModelGaugeCouplingAuthorityReceipt :
  StandardModelGaugeCouplingAuthorityReceipt
canonicalStandardModelGaugeCouplingAuthorityReceipt =
  record
    { receiptLabel =
        "Standard Model gauge-coupling authority frontier; metadata only"
    ; sourceRegistry =
        Registry.repoWideConstantsRegistry
    ; sourcePayloadValidatorReceipt =
        Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; alphaNormalizedToken =
        Norm.alphaNormalizedToken
    ; alphaSNormalizedToken =
        Norm.alphaSNormalizedToken
    ; gaugeCouplingInputs =
        canonicalGaugeCouplingInputs
    ; runningBoundaries =
        canonicalRunningBoundaries
    ; betaFunctionAuthorityRows =
        canonicalBetaFunctionAuthorityRows
    ; electroweakInputs =
        canonicalElectroweakInputs
    ; colliderConsumers =
        canonicalColliderConsumers
    ; gaugeCouplingInputCount =
        listCount canonicalGaugeCouplingInputs
    ; gaugeCouplingInputCountIs6 =
        refl
    ; runningBoundaryCount =
        listCount canonicalRunningBoundaries
    ; runningBoundaryCountIs5 =
        refl
    ; betaFunctionAuthorityRowCount =
        listCount canonicalBetaFunctionAuthorityRows
    ; betaFunctionAuthorityRowCountIs4 =
        refl
    ; electroweakInputCount =
        listCount canonicalElectroweakInputs
    ; electroweakInputCountIs5 =
        refl
    ; colliderConsumerCount =
        listCount canonicalColliderConsumers
    ; colliderConsumerCountIs6 =
        refl
    ; payloadEnvelopeCountCrossCheck =
        Payload.NumericAuthorityPayloadValidatorReceipt.payloadEnvelopeCount
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; payloadEnvelopeCountCrossCheckIs18 =
        Payload.NumericAuthorityPayloadValidatorReceipt.payloadEnvelopeCountIs18
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; payloadAcceptedAuthorityTokenPresent =
        Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresent
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; payloadAcceptedAuthorityTokenPresentIsFalse =
        Payload.NumericAuthorityPayloadValidatorReceipt.acceptedAuthorityTokenPresentIsFalse
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; payloadNumericValueLoaded =
        Payload.NumericAuthorityPayloadValidatorReceipt.numericValueLoaded
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; payloadNumericValueLoadedIsFalse =
        Payload.NumericAuthorityPayloadValidatorReceipt.numericValueLoadedIsFalse
          Payload.canonicalNumericAuthorityPayloadValidatorReceipt
    ; registryPhysicalLawDerived =
        Registry.ConstantsRegistry.physicalLawDerived
          Registry.repoWideConstantsRegistry
    ; registryPhysicalLawDerivedIsFalse =
        Registry.ConstantsRegistry.physicalLawDerivedIsFalse
          Registry.repoWideConstantsRegistry
    ; registryCalibrationPromoted =
        Registry.ConstantsRegistry.calibrationPromoted
          Registry.repoWideConstantsRegistry
    ; registryCalibrationPromotedIsFalse =
        Registry.ConstantsRegistry.calibrationPromotedIsFalse
          Registry.repoWideConstantsRegistry
    ; registryEmpiricalAdequacyAccepted =
        Registry.ConstantsRegistry.empiricalAdequacyAccepted
          Registry.repoWideConstantsRegistry
    ; registryEmpiricalAdequacyAcceptedIsFalse =
        Registry.ConstantsRegistry.empiricalAdequacyAcceptedIsFalse
          Registry.repoWideConstantsRegistry
    ; derivedGaugeCouplingsPromoted =
        false
    ; derivedGaugeCouplingsPromotedIsFalse =
        refl
    ; physicalStandardModelPromoted =
        false
    ; physicalStandardModelPromotedIsFalse =
        refl
    ; empiricalAdequacyPromoted =
        false
    ; empiricalAdequacyPromotedIsFalse =
        refl
    ; falseDerivedGaugeCouplingGuard =
        true
    ; falseDerivedGaugeCouplingGuardIsTrue =
        refl
    ; falsePhysicalSMPromotionGuard =
        true
    ; falsePhysicalSMPromotionGuardIsTrue =
        refl
    ; falseEmpiricalAdequacyGuard =
        true
    ; falseEmpiricalAdequacyGuardIsTrue =
        refl
    ; frontierNotes =
        "g1, g2, g3, alpha_em, alpha_s, and weak mixing angle are authority/calibration slots, not derived constants"
        ∷ "renormalization scheme, scale, threshold matching, beta functions, and electroweak inputs are explicit frontier rows"
        ∷ "PDG/CODATA payloads are referenced through the numeric authority validator and normalized token surfaces"
        ∷ "collider observable consumers remain validation clients; no empirical adequacy claim is accepted here"
        ∷ []
    }

canonicalGaugeCouplingInputCountIs6 :
  gaugeCouplingInputCount
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 6
canonicalGaugeCouplingInputCountIs6 = refl

canonicalGaugeRunningBoundaryCountIs5 :
  runningBoundaryCount
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 5
canonicalGaugeRunningBoundaryCountIs5 = refl

canonicalGaugeBetaFunctionAuthorityRowCountIs4 :
  betaFunctionAuthorityRowCount
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 4
canonicalGaugeBetaFunctionAuthorityRowCountIs4 = refl

canonicalGaugeElectroweakInputCountIs5 :
  electroweakInputCount
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 5
canonicalGaugeElectroweakInputCountIs5 = refl

canonicalGaugeColliderConsumerCountIs6 :
  colliderConsumerCount
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 6
canonicalGaugeColliderConsumerCountIs6 = refl

canonicalGaugePayloadEnvelopeCrossCheckIs18 :
  payloadEnvelopeCountCrossCheck
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ 18
canonicalGaugePayloadEnvelopeCrossCheckIs18 = refl

canonicalGaugePayloadAuthorityTokenPresentIsFalse :
  payloadAcceptedAuthorityTokenPresent
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ false
canonicalGaugePayloadAuthorityTokenPresentIsFalse = refl

canonicalGaugePayloadNumericValueLoadedIsFalse :
  payloadNumericValueLoaded
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ false
canonicalGaugePayloadNumericValueLoadedIsFalse = refl

canonicalGaugeDerivedCouplingsPromotedIsFalse :
  derivedGaugeCouplingsPromoted
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ false
canonicalGaugeDerivedCouplingsPromotedIsFalse = refl

canonicalGaugePhysicalSMPromotedIsFalse :
  physicalStandardModelPromoted
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ false
canonicalGaugePhysicalSMPromotedIsFalse = refl

canonicalGaugeEmpiricalAdequacyPromotedIsFalse :
  empiricalAdequacyPromoted
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ false
canonicalGaugeEmpiricalAdequacyPromotedIsFalse = refl

canonicalGaugeFalseDerivedCouplingGuardIsTrue :
  falseDerivedGaugeCouplingGuard
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ true
canonicalGaugeFalseDerivedCouplingGuardIsTrue = refl

canonicalGaugeFalsePhysicalSMGuardIsTrue :
  falsePhysicalSMPromotionGuard
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ true
canonicalGaugeFalsePhysicalSMGuardIsTrue = refl

canonicalGaugeFalseEmpiricalAdequacyGuardIsTrue :
  falseEmpiricalAdequacyGuard
    canonicalStandardModelGaugeCouplingAuthorityReceipt
  ≡ true
canonicalGaugeFalseEmpiricalAdequacyGuardIsTrue = refl
