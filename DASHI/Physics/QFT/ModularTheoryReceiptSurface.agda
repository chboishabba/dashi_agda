module DASHI.Physics.QFT.ModularTheoryReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT

------------------------------------------------------------------------
-- Modular theory receipt surfaces for AQFT.
--
-- This module records proof targets for the representation-theoretic layer
-- that sits after an AQFT local algebra net:
--
--   * GNS representation and von Neumann closure,
--   * Tomita-Takesaki modular operator, conjugation, and modular flow,
--   * KMS condition target,
--   * Unruh/Rindler modular receipt,
--   * Bisognano-Wichmann dependency receipt.
--
-- It deliberately does not construct a Hilbert space, state, von Neumann
-- algebra, modular data, thermal state, interacting QFT, Standard Model
-- net, or GRQFT promotion receipt.

data ModularTheoryStatus : Set where
  modularTheoryTargetsOnlyNoPromotion :
    ModularTheoryStatus

data ModularTheoryOpenObligation : Set where
  missingGNSStateFunctional :
    ModularTheoryOpenObligation

  missingGNSHilbertRepresentation :
    ModularTheoryOpenObligation

  missingCyclicVector :
    ModularTheoryOpenObligation

  missingVonNeumannClosure :
    ModularTheoryOpenObligation

  missingCyclicSeparatingVector :
    ModularTheoryOpenObligation

  missingTomitaOperator :
    ModularTheoryOpenObligation

  missingModularOperator :
    ModularTheoryOpenObligation

  missingModularConjugation :
    ModularTheoryOpenObligation

  missingModularFlow :
    ModularTheoryOpenObligation

  missingKMSAnalyticStrip :
    ModularTheoryOpenObligation

  missingRindlerWedgeNet :
    ModularTheoryOpenObligation

  missingUnruhTemperatureNormalization :
    ModularTheoryOpenObligation

  missingBisognanoWichmannPoincareCovariance :
    ModularTheoryOpenObligation

  missingBisognanoWichmannSpectrumCondition :
    ModularTheoryOpenObligation

  missingBisognanoWichmannWedgeDuality :
    ModularTheoryOpenObligation

canonicalModularTheoryOpenObligations :
  List ModularTheoryOpenObligation
canonicalModularTheoryOpenObligations =
  missingGNSStateFunctional
  ∷ missingGNSHilbertRepresentation
  ∷ missingCyclicVector
  ∷ missingVonNeumannClosure
  ∷ missingCyclicSeparatingVector
  ∷ missingTomitaOperator
  ∷ missingModularOperator
  ∷ missingModularConjugation
  ∷ missingModularFlow
  ∷ missingKMSAnalyticStrip
  ∷ missingRindlerWedgeNet
  ∷ missingUnruhTemperatureNormalization
  ∷ missingBisognanoWichmannPoincareCovariance
  ∷ missingBisognanoWichmannSpectrumCondition
  ∷ missingBisognanoWichmannWedgeDuality
  ∷ []

data ModularTheoryPromotionAuthorityToken : Set where

data BorchersBGLAuthorityCitation : Set where
  borchers1992CPTModularInclusions :
    BorchersBGLAuthorityCitation

  brunettiGuidoLongo2002ModularLocalizationWignerParticles :
    BorchersBGLAuthorityCitation

  geometricBisognanoWichmannForNets :
    BorchersBGLAuthorityCitation

canonicalBorchersBGLAuthorityCitations :
  List BorchersBGLAuthorityCitation
canonicalBorchersBGLAuthorityCitations =
  borchers1992CPTModularInclusions
  ∷ brunettiGuidoLongo2002ModularLocalizationWignerParticles
  ∷ geometricBisognanoWichmannForNets
  ∷ []

postulate
  StateFunctional :
    AQFT.Region →
    Set

  GNSHilbertSpace :
    AQFT.Region →
    Set

  GNSRepresentation :
    (region : AQFT.Region) →
    GNSHilbertSpace region →
    Set

  GNSCyclicVector :
    (region : AQFT.Region) →
    GNSHilbertSpace region →
    Set

  VonNeumannAlgebra :
    AQFT.Region →
    Set

  TomitaOperator :
    AQFT.Region →
    Set

  ModularOperator :
    AQFT.Region →
    Set

  ModularConjugation :
    AQFT.Region →
    Set

  ModularFlow :
    AQFT.Region →
    Set

  KMSCondition :
    AQFT.Region →
    Set

  RindlerWedgeData :
    AQFT.Region →
    Set

  BisognanoWichmannDependency :
    AQFT.Region →
    Set

record GNSVonNeumannClosureSurface : Setω where
  field
    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    region :
      AQFT.Region

    stateFunctional :
      StateFunctional region

    hilbertSpace :
      GNSHilbertSpace region

    representation :
      GNSRepresentation region hilbertSpace

    cyclicVector :
      GNSCyclicVector region hilbertSpace

    vonNeumannClosure :
      VonNeumannAlgebra region

    localAlgebraRepresentationTarget :
      Set

    weakClosureTarget :
      Set

    gnsBoundary :
      List String

open GNSVonNeumannClosureSurface public

record TomitaTakesakiModularSurface : Setω where
  field
    gnsSurface :
      GNSVonNeumannClosureSurface

    cyclicSeparatingVectorTarget :
      Set

    tomitaOperator :
      TomitaOperator (GNSVonNeumannClosureSurface.region gnsSurface)

    modularOperator :
      ModularOperator (GNSVonNeumannClosureSurface.region gnsSurface)

    modularConjugation :
      ModularConjugation (GNSVonNeumannClosureSurface.region gnsSurface)

    modularFlow :
      ModularFlow (GNSVonNeumannClosureSurface.region gnsSurface)

    tomitaPolarDecompositionTarget :
      Set

    modularAutomorphismTarget :
      Set

    standardFormTarget :
      Set

    tomitaBoundary :
      List String

open TomitaTakesakiModularSurface public

record KMSConditionReceiptTarget : Setω where
  field
    modularSurface :
      TomitaTakesakiModularSurface

    inverseTemperatureLabel :
      String

    kmsCondition :
      KMSCondition
        (GNSVonNeumannClosureSurface.region
          (TomitaTakesakiModularSurface.gnsSurface modularSurface))

    analyticStripTarget :
      Set

    boundaryCorrelationTarget :
      Set

    kmsPromoted :
      Bool

    kmsPromotedIsFalse :
      kmsPromoted ≡ false

    kmsBoundary :
      List String

open KMSConditionReceiptTarget public

record UnruhRindlerModularReceipt : Setω where
  field
    kmsTarget :
      KMSConditionReceiptTarget

    wedgeRegion :
      AQFT.Region

    rindlerWedgeData :
      RindlerWedgeData wedgeRegion

    boostFlowTarget :
      ModularFlow wedgeRegion

    unruhTemperatureLabel :
      String

    unruhTemperatureLabel-v :
      unruhTemperatureLabel
      ≡
      "T = acceleration-over-2-pi-target-only"

    rindlerVacuumRestrictionTarget :
      Set

    unruhPromoted :
      Bool

    unruhPromotedIsFalse :
      unruhPromoted ≡ false

    unruhBoundary :
      List String

open UnruhRindlerModularReceipt public

record BisognanoWichmannReceiptTarget : Setω where
  field
    unruhReceipt :
      UnruhRindlerModularReceipt

    wedgeRegion :
      AQFT.Region

    bwDependency :
      BisognanoWichmannDependency wedgeRegion

    poincareCovarianceTarget :
      Set

    spectrumConditionTarget :
      Set

    vacuumCyclicSeparatingTarget :
      Set

    wedgeDualityTarget :
      Set

    modularFlowMatchesBoostTarget :
      Set

    modularConjugationMatchesReflectionTarget :
      Set

    bwPromoted :
      Bool

    bwPromotedIsFalse :
      bwPromoted ≡ false

    bisognanoWichmannBoundary :
      List String

open BisognanoWichmannReceiptTarget public

record BorchersBGLAuthorityCitationSurface : Setω where
  field
    borchersCitation :
      String

    borchersCitation-v :
      borchersCitation
      ≡
      "Borchers-1992-CPT-theorem-modular-inclusions-and-positive-energy"

    bglCitation :
      String

    bglCitation-v :
      bglCitation
      ≡
      "Brunetti-Guido-Longo-2002-modular-localization-and-Wigner-particles"

    citationTokens :
      List BorchersBGLAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalBorchersBGLAuthorityCitations

    citedAuthorityRecorded :
      Bool

    citedAuthorityRecordedIsTrue :
      citedAuthorityRecorded ≡ true

    constructsLocalModularTheorem :
      Bool

    constructsLocalModularTheoremIsFalse :
      constructsLocalModularTheorem ≡ false

    borchersBGLAuthorityBoundary :
      List String

open BorchersBGLAuthorityCitationSurface public

record BisognanoWichmannAuthorityReceipt : Setω where
  field
    borchersBGLAuthority :
      BorchersBGLAuthorityCitationSurface

    wedgeRegion :
      AQFT.Region

    rindlerWedgeData :
      RindlerWedgeData wedgeRegion

    energyPositivityHypothesis :
      Set

    vacuumHypothesis :
      Set

    poincareCovarianceHypothesis :
      Set

    wedgeModularFlow :
      ModularFlow wedgeRegion

    wedgeBoostFlow :
      ModularFlow wedgeRegion

    modularFlowEqualsBoostFlowUnderEnergyPositivityVacuum :
      energyPositivityHypothesis →
      vacuumHypothesis →
      poincareCovarianceHypothesis →
      wedgeModularFlow
      ≡
      wedgeBoostFlow

    bwAuthorityPromoted :
      Bool

    bwAuthorityPromotedIsFalse :
      bwAuthorityPromoted ≡ false

    bwAuthorityBoundary :
      List String

open BisognanoWichmannAuthorityReceipt public

record GeometricBisognanoWichmannNetReceipt : Setω where
  field
    borchersBGLGeometricAuthority :
      BorchersBGLAuthorityCitationSurface

    wedgeRegion :
      AQFT.Region

    rightRindlerWedgeData :
      RindlerWedgeData wedgeRegion

    rightRindlerWedgeLabel :
      String

    rightRindlerWedgeLabel-v :
      rightRindlerWedgeLabel
      ≡
      "W_R = { x : x1 > abs x0 }"

    boostRapidityNormalization :
      String

    boostRapidityNormalization-v :
      boostRapidityNormalization
      ≡
      "Lambda_t boost rapidity = 2*pi*t"

    wedgeModularFlow :
      ModularFlow wedgeRegion

    wedgeBoostAutomorphismFlow :
      ModularFlow wedgeRegion

    haagDualityHypothesis :
      Set

    poincareCovarianceHypothesis :
      Set

    positiveEnergyHypothesis :
      Set

    cyclicSeparatingVacuumStandardnessHypothesis :
      Set

    standardWedgePairTarget :
      Set

    sigmaOmegaEqualsBoostAutomorphismTarget :
      haagDualityHypothesis →
      poincareCovarianceHypothesis →
      positiveEnergyHypothesis →
      cyclicSeparatingVacuumStandardnessHypothesis →
      wedgeModularFlow
      ≡
      wedgeBoostAutomorphismFlow

    modularConjugationReflectsWedgeTarget :
      Set

    geometricNetAuthorityLabel :
      String

    geometricNetAuthorityLabel-v :
      geometricNetAuthorityLabel
      ≡
      "Borchers-BGL-geometric-net-Bisognano-Wichmann-authority"

    geometricBWNetAuthorityPromoted :
      Bool

    geometricBWNetAuthorityPromotedIsFalse :
      geometricBWNetAuthorityPromoted ≡ false

    geometricBWNetBoundary :
      List String

open GeometricBisognanoWichmannNetReceipt public

postulate
  abstractRegion :
    AQFT.Region

  abstractStateFunctional :
    StateFunctional abstractRegion

  abstractGNSHilbertSpace :
    GNSHilbertSpace abstractRegion

  abstractGNSRepresentation :
    GNSRepresentation abstractRegion abstractGNSHilbertSpace

  abstractGNSCyclicVector :
    GNSCyclicVector abstractRegion abstractGNSHilbertSpace

  abstractVonNeumannClosure :
    VonNeumannAlgebra abstractRegion

  abstractLocalAlgebraRepresentationTarget :
    Set

  abstractWeakClosureTarget :
    Set

  abstractCyclicSeparatingVectorTarget :
    Set

  abstractTomitaOperator :
    TomitaOperator abstractRegion

  abstractModularOperator :
    ModularOperator abstractRegion

  abstractModularConjugation :
    ModularConjugation abstractRegion

  abstractModularFlow :
    ModularFlow abstractRegion

  abstractTomitaPolarDecompositionTarget :
    Set

  abstractModularAutomorphismTarget :
    Set

  abstractStandardFormTarget :
    Set

  abstractKMSCondition :
    KMSCondition abstractRegion

  abstractAnalyticStripTarget :
    Set

  abstractBoundaryCorrelationTarget :
    Set

  abstractRindlerWedgeData :
    RindlerWedgeData abstractRegion

  abstractRindlerVacuumRestrictionTarget :
    Set

  abstractBisognanoWichmannDependency :
    BisognanoWichmannDependency abstractRegion

  abstractPoincareCovarianceTarget :
    Set

  abstractSpectrumConditionTarget :
    Set

  abstractVacuumCyclicSeparatingTarget :
    Set

  abstractWedgeDualityTarget :
    Set

  abstractModularFlowMatchesBoostTarget :
    Set

  abstractModularConjugationMatchesReflectionTarget :
    Set

  abstractBWAuthorityEnergyPositivityHypothesis :
    Set

  abstractBWAuthorityVacuumHypothesis :
    Set

  abstractBWAuthorityPoincareCovarianceHypothesis :
    Set

  abstractBWAuthorityModularFlowEqualsBoostFlow :
    abstractBWAuthorityEnergyPositivityHypothesis →
    abstractBWAuthorityVacuumHypothesis →
    abstractBWAuthorityPoincareCovarianceHypothesis →
    abstractModularFlow
    ≡
    abstractModularFlow

  abstractGeometricBWNetHaagDualityHypothesis :
    Set

  abstractGeometricBWNetPoincareCovarianceHypothesis :
    Set

  abstractGeometricBWNetPositiveEnergyHypothesis :
    Set

  abstractGeometricBWNetCyclicSeparatingVacuumStandardnessHypothesis :
    Set

  abstractGeometricBWNetStandardWedgePairTarget :
    Set

  abstractGeometricBWNetSigmaOmegaEqualsBoostAutomorphismTarget :
    abstractGeometricBWNetHaagDualityHypothesis →
    abstractGeometricBWNetPoincareCovarianceHypothesis →
    abstractGeometricBWNetPositiveEnergyHypothesis →
    abstractGeometricBWNetCyclicSeparatingVacuumStandardnessHypothesis →
    abstractModularFlow
    ≡
    abstractModularFlow

  abstractGeometricBWNetModularConjugationReflectsWedgeTarget :
    Set

canonicalBorchersBGLAuthorityCitationSurface :
  BorchersBGLAuthorityCitationSurface
canonicalBorchersBGLAuthorityCitationSurface =
  record
    { borchersCitation =
        "Borchers-1992-CPT-theorem-modular-inclusions-and-positive-energy"
    ; borchersCitation-v =
        refl
    ; bglCitation =
        "Brunetti-Guido-Longo-2002-modular-localization-and-Wigner-particles"
    ; bglCitation-v =
        refl
    ; citationTokens =
        canonicalBorchersBGLAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; citedAuthorityRecorded =
        true
    ; citedAuthorityRecordedIsTrue =
        refl
    ; constructsLocalModularTheorem =
        false
    ; constructsLocalModularTheoremIsFalse =
        refl
    ; borchersBGLAuthorityBoundary =
        "Borchers/BGL/geometric-net authority is recorded as cited modular-theory authority"
        ∷ "the citation surface does not construct Poincare covariance, positive energy, vacuum standardness, or wedge duality"
        ∷ "local promotion still requires an explicit modular-theory authority token"
        ∷ []
    }

canonicalBisognanoWichmannAuthorityReceipt :
  BisognanoWichmannAuthorityReceipt
canonicalBisognanoWichmannAuthorityReceipt =
  record
    { borchersBGLAuthority =
        canonicalBorchersBGLAuthorityCitationSurface
    ; wedgeRegion =
        abstractRegion
    ; rindlerWedgeData =
        abstractRindlerWedgeData
    ; energyPositivityHypothesis =
        abstractBWAuthorityEnergyPositivityHypothesis
    ; vacuumHypothesis =
        abstractBWAuthorityVacuumHypothesis
    ; poincareCovarianceHypothesis =
        abstractBWAuthorityPoincareCovarianceHypothesis
    ; wedgeModularFlow =
        abstractModularFlow
    ; wedgeBoostFlow =
        abstractModularFlow
    ; modularFlowEqualsBoostFlowUnderEnergyPositivityVacuum =
        abstractBWAuthorityModularFlowEqualsBoostFlow
    ; bwAuthorityPromoted =
        false
    ; bwAuthorityPromotedIsFalse =
        refl
    ; bwAuthorityBoundary =
        "Bisognano-Wichmann authority states that wedge modular flow equals boost flow under positive energy, vacuum, and covariance hypotheses"
        ∷ "the equality is a postulate-shaped authority field, not a local theorem construction"
        ∷ "the canonical receipt is non-promoting and does not issue a GRQFT, Standard Model, or interacting-QFT receipt"
        ∷ []
    }

canonicalGeometricBisognanoWichmannNetReceipt :
  GeometricBisognanoWichmannNetReceipt
canonicalGeometricBisognanoWichmannNetReceipt =
  record
    { borchersBGLGeometricAuthority =
        canonicalBorchersBGLAuthorityCitationSurface
    ; wedgeRegion =
        abstractRegion
    ; rightRindlerWedgeData =
        abstractRindlerWedgeData
    ; rightRindlerWedgeLabel =
        "W_R = { x : x1 > abs x0 }"
    ; rightRindlerWedgeLabel-v =
        refl
    ; boostRapidityNormalization =
        "Lambda_t boost rapidity = 2*pi*t"
    ; boostRapidityNormalization-v =
        refl
    ; wedgeModularFlow =
        abstractModularFlow
    ; wedgeBoostAutomorphismFlow =
        abstractModularFlow
    ; haagDualityHypothesis =
        abstractGeometricBWNetHaagDualityHypothesis
    ; poincareCovarianceHypothesis =
        abstractGeometricBWNetPoincareCovarianceHypothesis
    ; positiveEnergyHypothesis =
        abstractGeometricBWNetPositiveEnergyHypothesis
    ; cyclicSeparatingVacuumStandardnessHypothesis =
        abstractGeometricBWNetCyclicSeparatingVacuumStandardnessHypothesis
    ; standardWedgePairTarget =
        abstractGeometricBWNetStandardWedgePairTarget
    ; sigmaOmegaEqualsBoostAutomorphismTarget =
        abstractGeometricBWNetSigmaOmegaEqualsBoostAutomorphismTarget
    ; modularConjugationReflectsWedgeTarget =
        abstractGeometricBWNetModularConjugationReflectsWedgeTarget
    ; geometricNetAuthorityLabel =
        "Borchers-BGL-geometric-net-Bisognano-Wichmann-authority"
    ; geometricNetAuthorityLabel-v =
        refl
    ; geometricBWNetAuthorityPromoted =
        false
    ; geometricBWNetAuthorityPromotedIsFalse =
        refl
    ; geometricBWNetBoundary =
        "GeometricBisognanoWichmannNetReceipt fixes the right Rindler wedge W_R and boost rapidity 2*pi*t"
        ∷ "the theorem target is sigma^omega_t(a) = alpha_t(a), represented as equality between wedge modular flow and boost automorphism flow"
        ∷ "Haag duality, Poincare covariance, positive energy, and cyclic-separating vacuum standardness are explicit hypotheses"
        ∷ "Borchers/BGL/geometric-net authority is recorded as a non-promoting citation receipt"
        ∷ []
    }

canonicalGNSVonNeumannClosureSurface :
  GNSVonNeumannClosureSurface
canonicalGNSVonNeumannClosureSurface =
  record
    { typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; region =
        abstractRegion
    ; stateFunctional =
        abstractStateFunctional
    ; hilbertSpace =
        abstractGNSHilbertSpace
    ; representation =
        abstractGNSRepresentation
    ; cyclicVector =
        abstractGNSCyclicVector
    ; vonNeumannClosure =
        abstractVonNeumannClosure
    ; localAlgebraRepresentationTarget =
        abstractLocalAlgebraRepresentationTarget
    ; weakClosureTarget =
        abstractWeakClosureTarget
    ; gnsBoundary =
        "GNS/von-Neumann closure is a representation target, not a constructed representation"
        ∷ "the selected state functional, cyclic vector, and weak closure remain open obligations"
        ∷ "this surface does not select a vacuum, Born-rule adapter, or interacting AQFT net"
        ∷ []
    }

canonicalTomitaTakesakiModularSurface :
  TomitaTakesakiModularSurface
canonicalTomitaTakesakiModularSurface =
  record
    { gnsSurface =
        canonicalGNSVonNeumannClosureSurface
    ; cyclicSeparatingVectorTarget =
        abstractCyclicSeparatingVectorTarget
    ; tomitaOperator =
        abstractTomitaOperator
    ; modularOperator =
        abstractModularOperator
    ; modularConjugation =
        abstractModularConjugation
    ; modularFlow =
        abstractModularFlow
    ; tomitaPolarDecompositionTarget =
        abstractTomitaPolarDecompositionTarget
    ; modularAutomorphismTarget =
        abstractModularAutomorphismTarget
    ; standardFormTarget =
        abstractStandardFormTarget
    ; tomitaBoundary =
        "Tomita-Takesaki data are staged as operator/conjugation/flow targets only"
        ∷ "cyclic-separating vector and polar-decomposition obligations are not discharged here"
        ∷ "modular flow is not promoted to physical time evolution by this surface"
        ∷ []
    }

canonicalKMSConditionReceiptTarget :
  KMSConditionReceiptTarget
canonicalKMSConditionReceiptTarget =
  record
    { modularSurface =
        canonicalTomitaTakesakiModularSurface
    ; inverseTemperatureLabel =
        "beta-target-only"
    ; kmsCondition =
        abstractKMSCondition
    ; analyticStripTarget =
        abstractAnalyticStripTarget
    ; boundaryCorrelationTarget =
        abstractBoundaryCorrelationTarget
    ; kmsPromoted =
        false
    ; kmsPromotedIsFalse =
        refl
    ; kmsBoundary =
        "KMS condition is an analytic-strip and boundary-correlation target only"
        ∷ "no thermal state, equilibrium theorem, or physical temperature calibration is constructed here"
        ∷ []
    }

canonicalUnruhRindlerModularReceipt :
  UnruhRindlerModularReceipt
canonicalUnruhRindlerModularReceipt =
  record
    { kmsTarget =
        canonicalKMSConditionReceiptTarget
    ; wedgeRegion =
        abstractRegion
    ; rindlerWedgeData =
        abstractRindlerWedgeData
    ; boostFlowTarget =
        abstractModularFlow
    ; unruhTemperatureLabel =
        "T = acceleration-over-2-pi-target-only"
    ; unruhTemperatureLabel-v =
        refl
    ; rindlerVacuumRestrictionTarget =
        abstractRindlerVacuumRestrictionTarget
    ; unruhPromoted =
        false
    ; unruhPromotedIsFalse =
        refl
    ; unruhBoundary =
        "Unruh/Rindler receipt records the wedge modular-flow and KMS target only"
        ∷ "Rindler wedge net, acceleration normalisation, and vacuum restriction remain open"
        ∷ "no detector response, empirical temperature calibration, or interacting AQFT claim is promoted"
        ∷ []
    }

canonicalBisognanoWichmannReceiptTarget :
  BisognanoWichmannReceiptTarget
canonicalBisognanoWichmannReceiptTarget =
  record
    { unruhReceipt =
        canonicalUnruhRindlerModularReceipt
    ; wedgeRegion =
        abstractRegion
    ; bwDependency =
        abstractBisognanoWichmannDependency
    ; poincareCovarianceTarget =
        abstractPoincareCovarianceTarget
    ; spectrumConditionTarget =
        abstractSpectrumConditionTarget
    ; vacuumCyclicSeparatingTarget =
        abstractVacuumCyclicSeparatingTarget
    ; wedgeDualityTarget =
        abstractWedgeDualityTarget
    ; modularFlowMatchesBoostTarget =
        abstractModularFlowMatchesBoostTarget
    ; modularConjugationMatchesReflectionTarget =
        abstractModularConjugationMatchesReflectionTarget
    ; bwPromoted =
        false
    ; bwPromotedIsFalse =
        refl
    ; bisognanoWichmannBoundary =
        "Bisognano-Wichmann receipt is a dependency target, not a proved theorem"
        ∷ "Poincare covariance, spectrum condition, cyclic-separating vacuum, and wedge duality remain required"
        ∷ "matching modular flow to boosts and modular conjugation to reflection remains open"
        ∷ "no GRQFT, Standard Model, or full unification promotion follows from this surface"
        ∷ []
    }

record ModularTheoryReceiptSurface : Setω where
  field
    status :
      ModularTheoryStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    gnsVonNeumannSurface :
      GNSVonNeumannClosureSurface

    tomitaTakesakiSurface :
      TomitaTakesakiModularSurface

    kmsConditionTarget :
      KMSConditionReceiptTarget

    unruhRindlerReceipt :
      UnruhRindlerModularReceipt

    bisognanoWichmannTarget :
      BisognanoWichmannReceiptTarget

    borchersBGLAuthority :
      BorchersBGLAuthorityCitationSurface

    bisognanoWichmannAuthority :
      BisognanoWichmannAuthorityReceipt

    geometricBisognanoWichmannNetReceipt :
      GeometricBisognanoWichmannNetReceipt

    openObligations :
      List ModularTheoryOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalModularTheoryOpenObligations

    modularTheoryPromoted :
      Bool

    modularTheoryPromotedIsFalse :
      modularTheoryPromoted ≡ false

    noPromotionWithoutAuthority :
      ModularTheoryPromotionAuthorityToken →
      ⊥

    modularTheoryBoundary :
      List String

open ModularTheoryReceiptSurface public

canonicalModularTheoryReceiptSurface :
  ModularTheoryReceiptSurface
canonicalModularTheoryReceiptSurface =
  record
    { status =
        modularTheoryTargetsOnlyNoPromotion
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; gnsVonNeumannSurface =
        canonicalGNSVonNeumannClosureSurface
    ; tomitaTakesakiSurface =
        canonicalTomitaTakesakiModularSurface
    ; kmsConditionTarget =
        canonicalKMSConditionReceiptTarget
    ; unruhRindlerReceipt =
        canonicalUnruhRindlerModularReceipt
    ; bisognanoWichmannTarget =
        canonicalBisognanoWichmannReceiptTarget
    ; borchersBGLAuthority =
        canonicalBorchersBGLAuthorityCitationSurface
    ; bisognanoWichmannAuthority =
        canonicalBisognanoWichmannAuthorityReceipt
    ; geometricBisognanoWichmannNetReceipt =
        canonicalGeometricBisognanoWichmannNetReceipt
    ; openObligations =
        canonicalModularTheoryOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; modularTheoryPromoted =
        false
    ; modularTheoryPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; modularTheoryBoundary =
        "ModularTheoryReceiptSurface records GNS/von-Neumann, Tomita-Takesaki, KMS, Unruh/Rindler, and Bisognano-Wichmann targets"
        ∷ "Borchers/BGL/geometric-net authority is cited only as a non-promoting postulate-shaped receipt for wedge modular flow equals boost flow"
        ∷ "GeometricBisognanoWichmannNetReceipt records W_R, boost flow, sigma^omega = boost, and the Haag-duality/covariance/energy/standardness hypotheses"
        ∷ "all representation, state, modular, wedge, covariance, and spectrum-condition data remain abstract obligations"
        ∷ "this module does not construct a C-star algebra representation, thermal state, vacuum, interacting QFT, Standard Model, or GRQFT receipt"
        ∷ []
    }
