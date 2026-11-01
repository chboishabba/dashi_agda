module DASHI.Physics.QFT.ModularTheoryReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT

subst :
  {A : Set} →
  (P : A → Set) →
  {x y : A} →
  x ≡ y →
  P x →
  P y
subst P refl px =
  px

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl =
  refl

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

  blockedByDepthFilteredLocalAlgebraSurface :
    ModularTheoryOpenObligation

  blockedByCStarCompletionAuthority :
    ModularTheoryOpenObligation

  missingNullIdealPreHilbertQuotientTheorem :
    ModularTheoryOpenObligation

  missingGNSDensityTheorem :
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

data GNSCauchySchwarzMissingLaw : Set where
  missingParametricPreCStarMultiplicationLaw :
    GNSCauchySchwarzMissingLaw

  missingParametricPreCStarStarInvolutionLaw :
    GNSCauchySchwarzMissingLaw

  missingParametricPreCStarPositiveConeOrder :
    GNSCauchySchwarzMissingLaw

  missingPositiveFiniteTraceStateFunctional :
    GNSCauchySchwarzMissingLaw

  missingFiniteTraceStateCauchySchwarzInequality :
    GNSCauchySchwarzMissingLaw

  missingNullIdealLeftMultiplicationClosureLaw :
    GNSCauchySchwarzMissingLaw

canonicalGNSCauchySchwarzMissingLaws :
  List GNSCauchySchwarzMissingLaw
canonicalGNSCauchySchwarzMissingLaws =
  missingParametricPreCStarMultiplicationLaw
  ∷ missingParametricPreCStarStarInvolutionLaw
  ∷ missingParametricPreCStarPositiveConeOrder
  ∷ missingPositiveFiniteTraceStateFunctional
  ∷ missingFiniteTraceStateCauchySchwarzInequality
  ∷ missingNullIdealLeftMultiplicationClosureLaw
  ∷ []

canonicalModularTheoryOpenObligations :
  List ModularTheoryOpenObligation
canonicalModularTheoryOpenObligations =
  missingTomitaOperator
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

data BratteliRobinsonModularAuthorityCitation : Set where
  bratteliRobinsonOperatorAlgebrasAndQuantumStatisticalMechanics :
    BratteliRobinsonModularAuthorityCitation

  bratteliRobinsonTomitaTakesakiModularTheory :
    BratteliRobinsonModularAuthorityCitation

canonicalBratteliRobinsonModularAuthorityCitations :
  List BratteliRobinsonModularAuthorityCitation
canonicalBratteliRobinsonModularAuthorityCitations =
  bratteliRobinsonOperatorAlgebrasAndQuantumStatisticalMechanics
  ∷ bratteliRobinsonTomitaTakesakiModularTheory
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

  LorentzBoostOneParameterGroup :
    AQFT.Region →
    Set

  BisognanoWichmannFlowEqualityTarget :
    (region : AQFT.Region) →
    VonNeumannAlgebra region →
    ModularFlow region →
    LorentzBoostOneParameterGroup region →
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

  GNSNullIdeal :
    (region : AQFT.Region) →
    StateFunctional region →
    Set

  GNSPreHilbertQuotient :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    GNSNullIdeal region stateFunctional →
    Set

  GNSPositiveNormalizedStateTarget :
    (region : AQFT.Region) →
    StateFunctional region →
    Set

  GNSLocalAlgebraDomainTarget :
    (region : AQFT.Region) →
    StateFunctional region →
    Set

  GNSNullIdealLeftIdealTarget :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    GNSNullIdeal region stateFunctional →
    Set

  GNSInnerProductDescendsTarget :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    (nullIdeal : GNSNullIdeal region stateFunctional) →
    GNSPreHilbertQuotient region stateFunctional nullIdeal →
    Set

  GNSHilbertCompletionTarget :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    (nullIdeal : GNSNullIdeal region stateFunctional) →
    GNSPreHilbertQuotient region stateFunctional nullIdeal →
    GNSHilbertSpace region →
    Set

  GNSRepresentationActionTarget :
    (region : AQFT.Region) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    Set

  GNSQuotientRepresentationWellDefinedTarget :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    (nullIdeal : GNSNullIdeal region stateFunctional) →
    (preHilbertQuotient :
      GNSPreHilbertQuotient region stateFunctional nullIdeal) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    Set

  GNSUniversalPropertyTarget :
    (region : AQFT.Region) →
    (stateFunctional : StateFunctional region) →
    (nullIdeal : GNSNullIdeal region stateFunctional) →
    (preHilbertQuotient :
      GNSPreHilbertQuotient region stateFunctional nullIdeal) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    Set

  GNSCyclicOrbitTarget :
    (region : AQFT.Region) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    GNSCyclicVector region hilbertSpace →
    Set

  GNSCyclicOrbitDenseTarget :
    (region : AQFT.Region) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    GNSCyclicVector region hilbertSpace →
    Set

  GNSVonNeumannWeakClosureTarget :
    (region : AQFT.Region) →
    (hilbertSpace : GNSHilbertSpace region) →
    GNSRepresentation region hilbertSpace →
    VonNeumannAlgebra region →
    Set

record L5GNSDependencySurface : Setω where
  field
    depthFilteredLocalAlgebraSurfaceLabel :
      String

    depthFilteredLocalAlgebraSurfaceLabel-v :
      depthFilteredLocalAlgebraSurfaceLabel
      ≡
      "AQFTCarrierAlgebraQuotientSurface.DepthFilteredLocalAlgebraSurface"

    aqftAlgebraColimitCompletionSurfaceLabel :
      String

    aqftAlgebraColimitCompletionSurfaceLabel-v :
      aqftAlgebraColimitCompletionSurfaceLabel
      ≡
      "AQFTCarrierAlgebraQuotientSurface.AQFTAlgebraColimitCompletionSurface"

    delta3aCompletionConstructivityLabel :
      String

    delta3aCompletionConstructivityLabel-v :
      delta3aCompletionConstructivityLabel
      ≡
      "AQFTCarrierAlgebraQuotientSurface.TierBPaper3Delta3aCStarCompletionConstructivity"

    depthFilteredLocalAlgebraSupplied :
      Bool

    depthFilteredLocalAlgebraSuppliedIsTrue :
      depthFilteredLocalAlgebraSupplied ≡ true

    cstarCompletionLocallyConstructed :
      Bool

    cstarCompletionLocallyConstructedIsFalse :
      cstarCompletionLocallyConstructed ≡ false

    cstarCompletionSafeAuthorityOnly :
      Bool

    cstarCompletionSafeAuthorityOnlyIsTrue :
      cstarCompletionSafeAuthorityOnly ≡ true

    cstarCompletionAuthorityConsumed :
      Bool

    cstarCompletionAuthorityConsumedIsTrue :
      cstarCompletionAuthorityConsumed ≡ true

    l5DependencyBoundary :
      List String

open L5GNSDependencySurface public

record GNSStateFunctionalReceipt
  (region : AQFT.Region) : Setω where
  field
    l5DependencySurface :
      L5GNSDependencySurface

    stateFunctional :
      StateFunctional region

    positiveNormalizedStateTarget :
      GNSPositiveNormalizedStateTarget region stateFunctional

    localAlgebraDomainTarget :
      GNSLocalAlgebraDomainTarget region stateFunctional

    stateFunctionalSelected :
      Bool

    stateFunctionalSelectedIsTrue :
      stateFunctionalSelected ≡ true

    stateFunctionalConstructedFromDepthFilteredCompletion :
      Bool

    stateFunctionalConstructedFromDepthFilteredCompletionIsFalse :
      stateFunctionalConstructedFromDepthFilteredCompletion ≡ false

    stateFunctionalPromoted :
      Bool

    stateFunctionalPromotedIsFalse :
      stateFunctionalPromoted ≡ false

    stateFunctionalBoundary :
      List String

open GNSStateFunctionalReceipt public

record GNSNullIdealPreHilbertQuotientReceipt
  (region : AQFT.Region)
  (stateFunctional : StateFunctional region) : Setω where
  field
    stateFunctionalReceipt :
      GNSStateFunctionalReceipt region

    stateFunctionalReceiptMatches :
      GNSStateFunctionalReceipt.stateFunctional stateFunctionalReceipt
      ≡
      stateFunctional

    nullIdeal :
      GNSNullIdeal region stateFunctional

    nullIdealLabel :
      String

    nullIdealLabel-v :
      nullIdealLabel
      ≡
      "N_phi = { a | phi(a* a)=0 }"

    nullIdealLeftIdealTarget :
      GNSNullIdealLeftIdealTarget region stateFunctional nullIdeal

    preHilbertQuotient :
      GNSPreHilbertQuotient region stateFunctional nullIdeal

    preHilbertQuotientLabel :
      String

    preHilbertQuotientLabel-v :
      preHilbertQuotientLabel
      ≡
      "A/N_phi"

    innerProductDescendsTarget :
      GNSInnerProductDescendsTarget
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient

    quotientCurrentlyInhabitedAsReceipt :
      Bool

    quotientCurrentlyInhabitedAsReceiptIsTrue :
      quotientCurrentlyInhabitedAsReceipt ≡ true

    quotientTheoremPromoted :
      Bool

    quotientTheoremPromotedIsFalse :
      quotientTheoremPromoted ≡ false

    quotientBoundary :
      List String

open GNSNullIdealPreHilbertQuotientReceipt public

record GNSHilbertRepresentationReceipt
  (region : AQFT.Region)
  (stateFunctional : StateFunctional region)
  (nullIdeal : GNSNullIdeal region stateFunctional)
  (preHilbertQuotient :
    GNSPreHilbertQuotient region stateFunctional nullIdeal) : Setω where
  field
    nullIdealPreHilbertQuotientReceipt :
      GNSNullIdealPreHilbertQuotientReceipt
        region
        stateFunctional

    nullIdealReceiptMatches :
      GNSNullIdealPreHilbertQuotientReceipt.nullIdeal
        nullIdealPreHilbertQuotientReceipt
      ≡
      nullIdeal

    preHilbertQuotientReceiptMatches :
      subst
        (λ ideal →
          GNSPreHilbertQuotient region stateFunctional ideal)
        nullIdealReceiptMatches
        (GNSNullIdealPreHilbertQuotientReceipt.preHilbertQuotient
          nullIdealPreHilbertQuotientReceipt)
      ≡
      preHilbertQuotient

    hilbertSpace :
      GNSHilbertSpace region

    hilbertCompletionTarget :
      GNSHilbertCompletionTarget
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient
        hilbertSpace

    representation :
      GNSRepresentation region hilbertSpace

    representationActionTarget :
      GNSRepresentationActionTarget region hilbertSpace representation

    quotientRepresentationWellDefinedTarget :
      GNSQuotientRepresentationWellDefinedTarget
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient
        hilbertSpace
        representation

    hilbertRepresentationCurrentlyInhabitedAsReceipt :
      Bool

    hilbertRepresentationCurrentlyInhabitedAsReceiptIsTrue :
      hilbertRepresentationCurrentlyInhabitedAsReceipt ≡ true

    hilbertRepresentationPromoted :
      Bool

    hilbertRepresentationPromotedIsFalse :
      hilbertRepresentationPromoted ≡ false

    hilbertRepresentationBoundary :
      List String

open GNSHilbertRepresentationReceipt public

record GNSUniversalPropertyReceipt
  (region : AQFT.Region)
  (stateFunctional : StateFunctional region)
  (nullIdeal : GNSNullIdeal region stateFunctional)
  (preHilbertQuotient :
    GNSPreHilbertQuotient region stateFunctional nullIdeal)
  (hilbertSpace : GNSHilbertSpace region)
  (representation : GNSRepresentation region hilbertSpace) : Setω where
  field
    hilbertRepresentationReceipt :
      GNSHilbertRepresentationReceipt
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient

    hilbertSpaceReceiptMatches :
      hilbertSpace
      ≡
      GNSHilbertRepresentationReceipt.hilbertSpace
        hilbertRepresentationReceipt

    representationReceiptMatches :
      representation
      ≡
      subst
        (λ hilbert →
          GNSRepresentation region hilbert)
        (sym hilbertSpaceReceiptMatches)
        (GNSHilbertRepresentationReceipt.representation
          hilbertRepresentationReceipt)

    universalPropertyTarget :
      GNSUniversalPropertyTarget
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient
        hilbertSpace
        representation

    universalPropertyReceiptInhabited :
      Bool

    universalPropertyReceiptInhabitedIsTrue :
      universalPropertyReceiptInhabited ≡ true

    universalPropertyPromoted :
      Bool

    universalPropertyPromotedIsFalse :
      universalPropertyPromoted ≡ false

    universalPropertyBoundary :
      List String

open GNSUniversalPropertyReceipt public

record GNSCyclicVectorDensityReceipt
  (region : AQFT.Region)
  (hilbertSpace : GNSHilbertSpace region)
  (representation : GNSRepresentation region hilbertSpace) : Setω where
  field
    cyclicVector :
      GNSCyclicVector region hilbertSpace

    cyclicOrbitTarget :
      GNSCyclicOrbitTarget
        region
        hilbertSpace
        representation
        cyclicVector

    cyclicOrbitDenseTarget :
      GNSCyclicOrbitDenseTarget
        region
        hilbertSpace
        representation
        cyclicVector

    densityLabel :
      String

    densityLabel-v :
      densityLabel
      ≡
      "pi_phi(A(O)) Omega_phi is dense in H_phi"

    cyclicVectorCurrentlyInhabitedAsReceipt :
      Bool

    cyclicVectorCurrentlyInhabitedAsReceiptIsTrue :
      cyclicVectorCurrentlyInhabitedAsReceipt ≡ true

    densityTheoremPromoted :
      Bool

    densityTheoremPromotedIsFalse :
      densityTheoremPromoted ≡ false

    densityBoundary :
      List String

open GNSCyclicVectorDensityReceipt public

record GNSVonNeumannClosureReceipt
  (region : AQFT.Region)
  (hilbertSpace : GNSHilbertSpace region)
  (representation : GNSRepresentation region hilbertSpace)
  (cyclicVector : GNSCyclicVector region hilbertSpace) : Setω where
  field
    cyclicVectorDensityReceipt :
      GNSCyclicVectorDensityReceipt
        region
        hilbertSpace
        representation

    cyclicVectorReceiptMatches :
      GNSCyclicVectorDensityReceipt.cyclicVector cyclicVectorDensityReceipt
      ≡
      cyclicVector

    vonNeumannClosure :
      VonNeumannAlgebra region

    weakClosureTarget :
      GNSVonNeumannWeakClosureTarget
        region
        hilbertSpace
        representation
        vonNeumannClosure

    vonNeumannClosureLabel :
      String

    vonNeumannClosureLabel-v :
      vonNeumannClosureLabel
      ≡
      "pi_phi(A(O))''"

    vonNeumannClosureCurrentlyInhabitedAsReceipt :
      Bool

    vonNeumannClosureCurrentlyInhabitedAsReceiptIsTrue :
      vonNeumannClosureCurrentlyInhabitedAsReceipt ≡ true

    vonNeumannClosurePromoted :
      Bool

    vonNeumannClosurePromotedIsFalse :
      vonNeumannClosurePromoted ≡ false

    vonNeumannClosureBoundary :
      List String

open GNSVonNeumannClosureReceipt public

record GNSVonNeumannClosureSurface : Setω where
  field
    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    region :
      AQFT.Region

    l5DependencySurface :
      L5GNSDependencySurface

    gnsStateFunctionalReceipt :
      GNSStateFunctionalReceipt region

    stateFunctional :
      StateFunctional region

    stateFunctionalMatchesReceipt :
      stateFunctional
      ≡
      GNSStateFunctionalReceipt.stateFunctional gnsStateFunctionalReceipt

    gnsNullIdealPreHilbertQuotientReceipt :
      GNSNullIdealPreHilbertQuotientReceipt region stateFunctional

    nullIdeal :
      GNSNullIdeal region stateFunctional

    nullIdealMatchesReceipt :
      nullIdeal
      ≡
      GNSNullIdealPreHilbertQuotientReceipt.nullIdeal
        gnsNullIdealPreHilbertQuotientReceipt

    preHilbertQuotient :
      GNSPreHilbertQuotient region stateFunctional nullIdeal

    preHilbertQuotientMatchesReceipt :
      subst
        (λ ideal →
          GNSPreHilbertQuotient region stateFunctional ideal)
        nullIdealMatchesReceipt
        preHilbertQuotient
      ≡
      GNSNullIdealPreHilbertQuotientReceipt.preHilbertQuotient
        gnsNullIdealPreHilbertQuotientReceipt

    gnsHilbertRepresentationReceipt :
      GNSHilbertRepresentationReceipt
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient

    hilbertSpace :
      GNSHilbertSpace region

    hilbertSpaceMatchesReceipt :
      hilbertSpace
      ≡
      GNSHilbertRepresentationReceipt.hilbertSpace
        gnsHilbertRepresentationReceipt

    representation :
      GNSRepresentation region hilbertSpace

    representationMatchesReceipt :
      representation
      ≡
      subst
        (λ hilbert →
          GNSRepresentation region hilbert)
        (sym hilbertSpaceMatchesReceipt)
        (GNSHilbertRepresentationReceipt.representation
          gnsHilbertRepresentationReceipt)

    gnsUniversalPropertyReceipt :
      GNSUniversalPropertyReceipt
        region
        stateFunctional
        nullIdeal
        preHilbertQuotient
        hilbertSpace
        representation

    gnsCyclicVectorDensityReceipt :
      GNSCyclicVectorDensityReceipt
        region
        hilbertSpace
        representation

    cyclicVector :
      GNSCyclicVector region hilbertSpace

    cyclicVectorMatchesReceipt :
      cyclicVector
      ≡
      GNSCyclicVectorDensityReceipt.cyclicVector
        gnsCyclicVectorDensityReceipt

    gnsVonNeumannClosureReceipt :
      GNSVonNeumannClosureReceipt
        region
        hilbertSpace
        representation
        cyclicVector

    vonNeumannClosure :
      VonNeumannAlgebra region

    vonNeumannClosureMatchesReceipt :
      vonNeumannClosure
      ≡
      GNSVonNeumannClosureReceipt.vonNeumannClosure
        gnsVonNeumannClosureReceipt

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

record BratteliRobinsonModularAuthorityCitationSurface : Setω where
  field
    bratteliRobinsonCitation :
      String

    bratteliRobinsonCitation-v :
      bratteliRobinsonCitation
      ≡
      "Bratteli-Robinson-Operator-Algebras-and-Quantum-Statistical-Mechanics-modular-theory"

    citationTokens :
      List BratteliRobinsonModularAuthorityCitation

    citationTokensAreCanonical :
      citationTokens
      ≡
      canonicalBratteliRobinsonModularAuthorityCitations

    citationAuthorityOnly :
      Bool

    citationAuthorityOnlyIsTrue :
      citationAuthorityOnly ≡ true

    constructsLocalTomitaTakesakiProof :
      Bool

    constructsLocalTomitaTakesakiProofIsFalse :
      constructsLocalTomitaTakesakiProof ≡ false

    bratteliRobinsonBoundary :
      List String

open BratteliRobinsonModularAuthorityCitationSurface public

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

record PostPaper7BisognanoWichmannInternalProofTargetSurface : Setω where
  field
    citationAuthority :
      BorchersBGLAuthorityCitationSurface

    bwReceiptTarget :
      BisognanoWichmannReceiptTarget

    geometricBWNetReceipt :
      GeometricBisognanoWichmannNetReceipt

    wedgeRegion :
      AQFT.Region

    wedgeAlgebra :
      VonNeumannAlgebra wedgeRegion

    wedgeModularFlow :
      ModularFlow wedgeRegion

    lorentzBoostFlow :
      LorentzBoostOneParameterGroup wedgeRegion

    equalityTargetLabel :
      String

    equalityTargetLabel-v :
      equalityTargetLabel
      ≡
      "Delta_W^it A(W) Delta_W^-it = U(Lambda_W(2*pi*t)) A(W) U(Lambda_W(2*pi*t))^-1"

    haagDualityDependency :
      Set

    reehSchliederDependency :
      Set

    poincareCovarianceDependency :
      Set

    positiveEnergyDependency :
      Set

    modularFlowEqualsLorentzBoostTarget :
      haagDualityDependency →
      reehSchliederDependency →
      poincareCovarianceDependency →
      positiveEnergyDependency →
      BisognanoWichmannFlowEqualityTarget
        wedgeRegion
        wedgeAlgebra
        wedgeModularFlow
        lorentzBoostFlow

    dependenciesThreaded :
      Bool

    dependenciesThreadedIsTrue :
      dependenciesThreaded ≡ true

    citationAuthorityOnly :
      Bool

    citationAuthorityOnlyIsTrue :
      citationAuthorityOnly ≡ true

    citationAuthorityConstructsLocalProof :
      BorchersBGLAuthorityCitationSurface.constructsLocalModularTheorem
        citationAuthority
      ≡
      false

    bwReceiptPromotionStillFalse :
      BisognanoWichmannReceiptTarget.bwPromoted bwReceiptTarget
      ≡
      false

    geometricAuthorityPromotionStillFalse :
      GeometricBisognanoWichmannNetReceipt.geometricBWNetAuthorityPromoted
        geometricBWNetReceipt
      ≡
      false

    internalBWProofConstructed :
      Bool

    internalBWProofConstructedIsFalse :
      internalBWProofConstructed ≡ false

    postPaper7BWPromoted :
      Bool

    postPaper7BWPromotedIsFalse :
      postPaper7BWPromoted ≡ false

    postPaper7BWBoundary :
      List String

open PostPaper7BisognanoWichmannInternalProofTargetSurface public

postulate
  abstractRegion :
    AQFT.Region

  abstractStateFunctional :
    StateFunctional abstractRegion

  abstractGNSPositiveNormalizedStateTarget :
    GNSPositiveNormalizedStateTarget
      abstractRegion
      abstractStateFunctional

  abstractGNSLocalAlgebraDomainTarget :
    GNSLocalAlgebraDomainTarget
      abstractRegion
      abstractStateFunctional

  abstractGNSNullIdeal :
    GNSNullIdeal
      abstractRegion
      abstractStateFunctional

  abstractGNSNullIdealLeftIdealTarget :
    GNSNullIdealLeftIdealTarget
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal

  abstractGNSPreHilbertQuotient :
    GNSPreHilbertQuotient
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal

  abstractGNSInnerProductDescendsTarget :
    GNSInnerProductDescendsTarget
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal
      abstractGNSPreHilbertQuotient

  abstractGNSHilbertSpace :
    GNSHilbertSpace abstractRegion

  abstractGNSHilbertCompletionTarget :
    GNSHilbertCompletionTarget
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal
      abstractGNSPreHilbertQuotient
      abstractGNSHilbertSpace

  abstractGNSRepresentation :
    GNSRepresentation abstractRegion abstractGNSHilbertSpace

  abstractGNSRepresentationActionTarget :
    GNSRepresentationActionTarget
      abstractRegion
      abstractGNSHilbertSpace
      abstractGNSRepresentation

  abstractGNSQuotientRepresentationWellDefinedTarget :
    GNSQuotientRepresentationWellDefinedTarget
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal
      abstractGNSPreHilbertQuotient
      abstractGNSHilbertSpace
      abstractGNSRepresentation

  abstractGNSUniversalPropertyTarget :
    GNSUniversalPropertyTarget
      abstractRegion
      abstractStateFunctional
      abstractGNSNullIdeal
      abstractGNSPreHilbertQuotient
      abstractGNSHilbertSpace
      abstractGNSRepresentation

  abstractGNSCyclicVector :
    GNSCyclicVector abstractRegion abstractGNSHilbertSpace

  abstractGNSCyclicOrbitTarget :
    GNSCyclicOrbitTarget
      abstractRegion
      abstractGNSHilbertSpace
      abstractGNSRepresentation
      abstractGNSCyclicVector

  abstractGNSCyclicOrbitDenseTarget :
    GNSCyclicOrbitDenseTarget
      abstractRegion
      abstractGNSHilbertSpace
      abstractGNSRepresentation
      abstractGNSCyclicVector

  abstractVonNeumannClosure :
    VonNeumannAlgebra abstractRegion

  abstractGNSVonNeumannWeakClosureTarget :
    GNSVonNeumannWeakClosureTarget
      abstractRegion
      abstractGNSHilbertSpace
      abstractGNSRepresentation
      abstractVonNeumannClosure

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

  abstractLorentzBoostFlow :
    LorentzBoostOneParameterGroup abstractRegion

  abstractPostPaper7WedgeAlgebra :
    VonNeumannAlgebra abstractRegion

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

  abstractPostPaper7BWHaagDualityDependency :
    Set

  abstractPostPaper7BWReehSchliederDependency :
    Set

  abstractPostPaper7BWPoincareCovarianceDependency :
    Set

  abstractPostPaper7BWPositiveEnergyDependency :
    Set

  abstractPostPaper7BWModularFlowEqualsLorentzBoostTarget :
    abstractPostPaper7BWHaagDualityDependency →
    abstractPostPaper7BWReehSchliederDependency →
    abstractPostPaper7BWPoincareCovarianceDependency →
    abstractPostPaper7BWPositiveEnergyDependency →
    BisognanoWichmannFlowEqualityTarget
      abstractRegion
      abstractPostPaper7WedgeAlgebra
      abstractModularFlow
      abstractLorentzBoostFlow

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

canonicalBratteliRobinsonModularAuthorityCitationSurface :
  BratteliRobinsonModularAuthorityCitationSurface
canonicalBratteliRobinsonModularAuthorityCitationSurface =
  record
    { bratteliRobinsonCitation =
        "Bratteli-Robinson-Operator-Algebras-and-Quantum-Statistical-Mechanics-modular-theory"
    ; bratteliRobinsonCitation-v =
        refl
    ; citationTokens =
        canonicalBratteliRobinsonModularAuthorityCitations
    ; citationTokensAreCanonical =
        refl
    ; citationAuthorityOnly =
        true
    ; citationAuthorityOnlyIsTrue =
        refl
    ; constructsLocalTomitaTakesakiProof =
        false
    ; constructsLocalTomitaTakesakiProofIsFalse =
        refl
    ; bratteliRobinsonBoundary =
        "Bratteli-Robinson modular authority is recorded as citation-only Tomita-Takesaki authority"
        ∷ "the citation surface targets Tomita operator closure and polar decomposition after the GNS universal property"
        ∷ "it does not construct a local Tomita-Takesaki proof, modular automorphism theorem, KMS theorem, or physical time evolution"
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

canonicalL5GNSDependencySurface :
  L5GNSDependencySurface
canonicalL5GNSDependencySurface =
  record
    { depthFilteredLocalAlgebraSurfaceLabel =
        "AQFTCarrierAlgebraQuotientSurface.DepthFilteredLocalAlgebraSurface"
    ; depthFilteredLocalAlgebraSurfaceLabel-v =
        refl
    ; aqftAlgebraColimitCompletionSurfaceLabel =
        "AQFTCarrierAlgebraQuotientSurface.AQFTAlgebraColimitCompletionSurface"
    ; aqftAlgebraColimitCompletionSurfaceLabel-v =
        refl
    ; delta3aCompletionConstructivityLabel =
        "AQFTCarrierAlgebraQuotientSurface.TierBPaper3Delta3aCStarCompletionConstructivity"
    ; delta3aCompletionConstructivityLabel-v =
        refl
    ; depthFilteredLocalAlgebraSupplied =
        true
    ; depthFilteredLocalAlgebraSuppliedIsTrue =
        refl
    ; cstarCompletionLocallyConstructed =
        false
    ; cstarCompletionLocallyConstructedIsFalse =
        refl
    ; cstarCompletionSafeAuthorityOnly =
        true
    ; cstarCompletionSafeAuthorityOnlyIsTrue =
        refl
    ; cstarCompletionAuthorityConsumed =
        true
    ; cstarCompletionAuthorityConsumedIsTrue =
        refl
    ; l5DependencyBoundary =
        "m4 consumes l5 through labeled AQFTCarrierAlgebraQuotientSurface dependency surfaces only"
        ∷ "DepthFilteredLocalAlgebraSurface is supplied by the l5 quotient surface and consumed here by label to avoid an import cycle"
        ∷ "the C*-completion socket is consumed as safe authority only and is not a local construction of a completed algebra or representation"
        ∷ []
    }

canonicalGNSStateFunctionalReceipt :
  GNSStateFunctionalReceipt abstractRegion
canonicalGNSStateFunctionalReceipt =
  record
    { l5DependencySurface =
        canonicalL5GNSDependencySurface
    ; stateFunctional =
        abstractStateFunctional
    ; positiveNormalizedStateTarget =
        abstractGNSPositiveNormalizedStateTarget
    ; localAlgebraDomainTarget =
        abstractGNSLocalAlgebraDomainTarget
    ; stateFunctionalSelected =
        true
    ; stateFunctionalSelectedIsTrue =
        refl
    ; stateFunctionalConstructedFromDepthFilteredCompletion =
        false
    ; stateFunctionalConstructedFromDepthFilteredCompletionIsFalse =
        refl
    ; stateFunctionalPromoted =
        false
    ; stateFunctionalPromotedIsFalse =
        refl
    ; stateFunctionalBoundary =
        "missingGNSStateFunctional is advanced to an explicit selected-state-functional receipt"
        ∷ "positivity, normalization, and the local-algebra domain are target fields over the abstract AQFT region"
        ∷ "selection is recorded, but construction from DepthFilteredLocalAlgebraSurface plus C*-completion remains blocked"
        ∷ []
    }

canonicalGNSNullIdealPreHilbertQuotientReceipt :
  GNSNullIdealPreHilbertQuotientReceipt
    abstractRegion
    abstractStateFunctional
canonicalGNSNullIdealPreHilbertQuotientReceipt =
  record
    { stateFunctionalReceipt =
        canonicalGNSStateFunctionalReceipt
    ; stateFunctionalReceiptMatches =
        refl
    ; nullIdeal =
        abstractGNSNullIdeal
    ; nullIdealLabel =
        "N_phi = { a | phi(a* a)=0 }"
    ; nullIdealLabel-v =
        refl
    ; nullIdealLeftIdealTarget =
        abstractGNSNullIdealLeftIdealTarget
    ; preHilbertQuotient =
        abstractGNSPreHilbertQuotient
    ; preHilbertQuotientLabel =
        "A/N_phi"
    ; preHilbertQuotientLabel-v =
        refl
    ; innerProductDescendsTarget =
        abstractGNSInnerProductDescendsTarget
    ; quotientCurrentlyInhabitedAsReceipt =
        true
    ; quotientCurrentlyInhabitedAsReceiptIsTrue =
        refl
    ; quotientTheoremPromoted =
        false
    ; quotientTheoremPromotedIsFalse =
        refl
    ; quotientBoundary =
        "the GNS null ideal N_phi and pre-Hilbert quotient A/N_phi are now explicit receipt fields"
        ∷ "left-ideal and inner-product descent obligations are named targets, not discharged theorems"
        ∷ "the quotient receipt is inhabited abstractly while the concrete l5 algebra and C*-completion blockers remain"
        ∷ []
    }

canonicalGNSHilbertRepresentationReceipt :
  GNSHilbertRepresentationReceipt
    abstractRegion
    abstractStateFunctional
    abstractGNSNullIdeal
    abstractGNSPreHilbertQuotient
canonicalGNSHilbertRepresentationReceipt =
  record
    { nullIdealPreHilbertQuotientReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; nullIdealReceiptMatches =
        refl
    ; preHilbertQuotientReceiptMatches =
        refl
    ; hilbertSpace =
        abstractGNSHilbertSpace
    ; hilbertCompletionTarget =
        abstractGNSHilbertCompletionTarget
    ; representation =
        abstractGNSRepresentation
    ; representationActionTarget =
        abstractGNSRepresentationActionTarget
    ; quotientRepresentationWellDefinedTarget =
        abstractGNSQuotientRepresentationWellDefinedTarget
    ; hilbertRepresentationCurrentlyInhabitedAsReceipt =
        true
    ; hilbertRepresentationCurrentlyInhabitedAsReceiptIsTrue =
        refl
    ; hilbertRepresentationPromoted =
        false
    ; hilbertRepresentationPromotedIsFalse =
        refl
    ; hilbertRepresentationBoundary =
        "missingGNSHilbertRepresentation is advanced to a Hilbert-completion and representation receipt"
        ∷ "the representation is tied to the null-ideal/pre-Hilbert quotient by well-definedness targets"
        ∷ "no concrete Hilbert completion or representation theorem is promoted without the l5 completion input"
        ∷ []
    }

canonicalGNSUniversalPropertyReceipt :
  GNSUniversalPropertyReceipt
    abstractRegion
    abstractStateFunctional
    abstractGNSNullIdeal
    abstractGNSPreHilbertQuotient
    abstractGNSHilbertSpace
    abstractGNSRepresentation
canonicalGNSUniversalPropertyReceipt =
  record
    { hilbertRepresentationReceipt =
        canonicalGNSHilbertRepresentationReceipt
    ; hilbertSpaceReceiptMatches =
        refl
    ; representationReceiptMatches =
        refl
    ; universalPropertyTarget =
        abstractGNSUniversalPropertyTarget
    ; universalPropertyReceiptInhabited =
        true
    ; universalPropertyReceiptInhabitedIsTrue =
        refl
    ; universalPropertyPromoted =
        false
    ; universalPropertyPromotedIsFalse =
        refl
    ; universalPropertyBoundary =
        "missingGNSUniversalProperty is now represented as an explicit receipt target over the selected GNS Hilbert representation"
        ∷ "the receipt is tied to the null ideal, pre-Hilbert quotient, Hilbert completion, and representation fields"
        ∷ "the universal property theorem is not promoted until l5 supplies concrete local-algebra and C-star-completion input"
        ∷ []
    }

canonicalGNSCyclicVectorDensityReceipt :
  GNSCyclicVectorDensityReceipt
    abstractRegion
    abstractGNSHilbertSpace
    abstractGNSRepresentation
canonicalGNSCyclicVectorDensityReceipt =
  record
    { cyclicVector =
        abstractGNSCyclicVector
    ; cyclicOrbitTarget =
        abstractGNSCyclicOrbitTarget
    ; cyclicOrbitDenseTarget =
        abstractGNSCyclicOrbitDenseTarget
    ; densityLabel =
        "pi_phi(A(O)) Omega_phi is dense in H_phi"
    ; densityLabel-v =
        refl
    ; cyclicVectorCurrentlyInhabitedAsReceipt =
        true
    ; cyclicVectorCurrentlyInhabitedAsReceiptIsTrue =
        refl
    ; densityTheoremPromoted =
        false
    ; densityTheoremPromotedIsFalse =
        refl
    ; densityBoundary =
        "missingCyclicVector is advanced to an explicit Omega_phi receipt"
        ∷ "the density receipt records pi_phi(A(O)) Omega_phi dense in H_phi as a target"
        ∷ "cyclicity and density remain theorem obligations rather than promoted Reeh-Schlieder or GNS density proofs"
        ∷ []
    }

canonicalGNSVonNeumannClosureReceipt :
  GNSVonNeumannClosureReceipt
    abstractRegion
    abstractGNSHilbertSpace
    abstractGNSRepresentation
    abstractGNSCyclicVector
canonicalGNSVonNeumannClosureReceipt =
  record
    { cyclicVectorDensityReceipt =
        canonicalGNSCyclicVectorDensityReceipt
    ; cyclicVectorReceiptMatches =
        refl
    ; vonNeumannClosure =
        abstractVonNeumannClosure
    ; weakClosureTarget =
        abstractGNSVonNeumannWeakClosureTarget
    ; vonNeumannClosureLabel =
        "pi_phi(A(O))''"
    ; vonNeumannClosureLabel-v =
        refl
    ; vonNeumannClosureCurrentlyInhabitedAsReceipt =
        true
    ; vonNeumannClosureCurrentlyInhabitedAsReceiptIsTrue =
        refl
    ; vonNeumannClosurePromoted =
        false
    ; vonNeumannClosurePromotedIsFalse =
        refl
    ; vonNeumannClosureBoundary =
        "missingVonNeumannClosure is advanced to an explicit weak-closure receipt"
        ∷ "the closure target is pi_phi(A(O))'' over the staged GNS representation"
        ∷ "weak closure is not promoted to a constructed von Neumann algebra without the concrete representation input"
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
    ; l5DependencySurface =
        canonicalL5GNSDependencySurface
    ; gnsStateFunctionalReceipt =
        canonicalGNSStateFunctionalReceipt
    ; stateFunctional =
        abstractStateFunctional
    ; stateFunctionalMatchesReceipt =
        refl
    ; gnsNullIdealPreHilbertQuotientReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; nullIdeal =
        abstractGNSNullIdeal
    ; nullIdealMatchesReceipt =
        refl
    ; preHilbertQuotient =
        abstractGNSPreHilbertQuotient
    ; preHilbertQuotientMatchesReceipt =
        refl
    ; gnsHilbertRepresentationReceipt =
        canonicalGNSHilbertRepresentationReceipt
    ; hilbertSpace =
        abstractGNSHilbertSpace
    ; hilbertSpaceMatchesReceipt =
        refl
    ; representation =
        abstractGNSRepresentation
    ; representationMatchesReceipt =
        refl
    ; gnsUniversalPropertyReceipt =
        canonicalGNSUniversalPropertyReceipt
    ; gnsCyclicVectorDensityReceipt =
        canonicalGNSCyclicVectorDensityReceipt
    ; cyclicVector =
        abstractGNSCyclicVector
    ; cyclicVectorMatchesReceipt =
        refl
    ; gnsVonNeumannClosureReceipt =
        canonicalGNSVonNeumannClosureReceipt
    ; vonNeumannClosure =
        abstractVonNeumannClosure
    ; vonNeumannClosureMatchesReceipt =
        refl
    ; localAlgebraRepresentationTarget =
        abstractLocalAlgebraRepresentationTarget
    ; weakClosureTarget =
        abstractWeakClosureTarget
    ; gnsBoundary =
        "GNS/von-Neumann closure is now decomposed into selected state, null ideal, pre-Hilbert quotient, Hilbert representation, cyclic density, and weak-closure receipts"
        ∷ "the receipt fields are inhabited abstractly and keep promotion bits false"
        ∷ "the concrete DepthFilteredLocalAlgebraSurface and C*-completion inputs remain the first l5 blockers"
        ∷ "this surface does not select a vacuum, Born-rule adapter, or interacting AQFT net"
        ∷ []
    }

record GNSAQFTWave2ProgressReceipt : Setω where
  field
    l5DependencySurface :
      L5GNSDependencySurface

    depthFilteredLocalAlgebraConsumed :
      L5GNSDependencySurface.depthFilteredLocalAlgebraSupplied
        l5DependencySurface
      ≡
      true

    cstarAuthorityConsumed :
      L5GNSDependencySurface.cstarCompletionAuthorityConsumed
        l5DependencySurface
      ≡
      true

    stateFunctionalReceipt :
      GNSStateFunctionalReceipt abstractRegion

    nullIdealPreHilbertQuotientReceipt :
      GNSNullIdealPreHilbertQuotientReceipt
        abstractRegion
        abstractStateFunctional

    hilbertRepresentationReceipt :
      GNSHilbertRepresentationReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient

    universalPropertyReceipt :
      GNSUniversalPropertyReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    cyclicDensityReceipt :
      GNSCyclicVectorDensityReceipt
        abstractRegion
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    nullIdealPreHilbertQuotientTheoremAdvanced :
      Bool

    nullIdealPreHilbertQuotientTheoremAdvancedIsTrue :
      nullIdealPreHilbertQuotientTheoremAdvanced ≡ true

    gnsUniversalPropertyAdvanced :
      Bool

    gnsUniversalPropertyAdvancedIsTrue :
      gnsUniversalPropertyAdvanced ≡ true

    gnsDensityTheoremAdvanced :
      Bool

    gnsDensityTheoremAdvancedIsTrue :
      gnsDensityTheoremAdvanced ≡ true

    gnsRepresentationPromoted :
      Bool

    gnsRepresentationPromotedIsFalse :
      gnsRepresentationPromoted ≡ false

    firstRemainingAfterGNSWave2 :
      ModularTheoryOpenObligation

    firstRemainingAfterGNSWave2IsMissingCyclicSeparatingVector :
      firstRemainingAfterGNSWave2
      ≡
      missingCyclicSeparatingVector

    remainingAfterGNSWave2 :
      List ModularTheoryOpenObligation

    remainingAfterGNSWave2AreCanonical :
      remainingAfterGNSWave2
      ≡
      canonicalModularTheoryOpenObligations

    gnsWave2Boundary :
      List String

open GNSAQFTWave2ProgressReceipt public

canonicalGNSAQFTWave2ProgressReceipt :
  GNSAQFTWave2ProgressReceipt
canonicalGNSAQFTWave2ProgressReceipt =
  record
    { l5DependencySurface =
        canonicalL5GNSDependencySurface
    ; depthFilteredLocalAlgebraConsumed =
        refl
    ; cstarAuthorityConsumed =
        refl
    ; stateFunctionalReceipt =
        canonicalGNSStateFunctionalReceipt
    ; nullIdealPreHilbertQuotientReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; hilbertRepresentationReceipt =
        canonicalGNSHilbertRepresentationReceipt
    ; universalPropertyReceipt =
        canonicalGNSUniversalPropertyReceipt
    ; cyclicDensityReceipt =
        canonicalGNSCyclicVectorDensityReceipt
    ; nullIdealPreHilbertQuotientTheoremAdvanced =
        true
    ; nullIdealPreHilbertQuotientTheoremAdvancedIsTrue =
        refl
    ; gnsUniversalPropertyAdvanced =
        true
    ; gnsUniversalPropertyAdvancedIsTrue =
        refl
    ; gnsDensityTheoremAdvanced =
        true
    ; gnsDensityTheoremAdvancedIsTrue =
        refl
    ; gnsRepresentationPromoted =
        false
    ; gnsRepresentationPromotedIsFalse =
        refl
    ; firstRemainingAfterGNSWave2 =
        missingCyclicSeparatingVector
    ; firstRemainingAfterGNSWave2IsMissingCyclicSeparatingVector =
        refl
    ; remainingAfterGNSWave2 =
        canonicalModularTheoryOpenObligations
    ; remainingAfterGNSWave2AreCanonical =
        refl
    ; gnsWave2Boundary =
        "l5 DepthFilteredLocalAlgebraSurface and safe C-star authority are consumed as labeled dependency receipts"
        ∷ "null ideal, pre-Hilbert quotient, GNS universal property, and cyclic-density targets are all tied to explicit receipts"
        ∷ "the GNS representation and density theorem remain non-promoting receipts rather than a constructed represented operator algebra"
        ∷ "the next modular blocker is the cyclic-separating vector needed before Tomita-Takesaki modular data"
        ∷ []
    }

record GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt : Setω where
  field
    wave2Progress :
      GNSAQFTWave2ProgressReceipt

    gnsUniversalPropertyReceipt :
      GNSUniversalPropertyReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    cyclicDensityReceipt :
      GNSCyclicVectorDensityReceipt
        abstractRegion
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    cyclicVector :
      GNSCyclicVector abstractRegion abstractGNSHilbertSpace

    cyclicVectorMatchesDensityReceipt :
      cyclicVector
      ≡
      GNSCyclicVectorDensityReceipt.cyclicVector cyclicDensityReceipt

    cyclicOrbitDenseTarget :
      GNSCyclicOrbitDenseTarget
        abstractRegion
        abstractGNSHilbertSpace
        abstractGNSRepresentation
        cyclicVector

    separatingVectorTarget :
      Set

    separatingVectorTargetMatchesBWVacuumStandardness :
      separatingVectorTarget
      ≡
      abstractVacuumCyclicSeparatingTarget

    tomitaCyclicSeparatingTarget :
      Set

    tomitaCyclicSeparatingTargetMatchesSurface :
      tomitaCyclicSeparatingTarget
      ≡
      abstractCyclicSeparatingVectorTarget

    gnsUniversalPropertyAdvanced :
      Bool

    gnsUniversalPropertyAdvancedIsTrue :
      gnsUniversalPropertyAdvanced ≡ true

    cyclicSeparatingVectorAdvanced :
      Bool

    cyclicSeparatingVectorAdvancedIsTrue :
      cyclicSeparatingVectorAdvanced ≡ true

    cyclicSeparatingVectorPromoted :
      Bool

    cyclicSeparatingVectorPromotedIsFalse :
      cyclicSeparatingVectorPromoted ≡ false

    firstRemainingAfterGNSWave3 :
      ModularTheoryOpenObligation

    firstRemainingAfterGNSWave3IsMissingTomitaOperator :
      firstRemainingAfterGNSWave3
      ≡
      missingTomitaOperator

    remainingAfterGNSWave3 :
      List ModularTheoryOpenObligation

    remainingAfterGNSWave3AreCanonical :
      remainingAfterGNSWave3
      ≡
      canonicalModularTheoryOpenObligations

    cstarCompletionHardHalt :
      String

    cstarCompletionHardHalt-v :
      cstarCompletionHardHalt
      ≡
      "cStarCompletion-authority-only-no-represented-C-star-algebra-promotion"

    bisognanoWichmannHardHalt :
      String

    bisognanoWichmannHardHalt-v :
      bisognanoWichmannHardHalt
      ≡
      "BisognanoWichmann-citation-only-before-wedge-modular-proof"

    gnsWave3Boundary :
      List String

open GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt public

canonicalGNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt :
  GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt
canonicalGNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt =
  record
    { wave2Progress =
        canonicalGNSAQFTWave2ProgressReceipt
    ; gnsUniversalPropertyReceipt =
        canonicalGNSUniversalPropertyReceipt
    ; cyclicDensityReceipt =
        canonicalGNSCyclicVectorDensityReceipt
    ; cyclicVector =
        abstractGNSCyclicVector
    ; cyclicVectorMatchesDensityReceipt =
        refl
    ; cyclicOrbitDenseTarget =
        abstractGNSCyclicOrbitDenseTarget
    ; separatingVectorTarget =
        abstractVacuumCyclicSeparatingTarget
    ; separatingVectorTargetMatchesBWVacuumStandardness =
        refl
    ; tomitaCyclicSeparatingTarget =
        abstractCyclicSeparatingVectorTarget
    ; tomitaCyclicSeparatingTargetMatchesSurface =
        refl
    ; gnsUniversalPropertyAdvanced =
        true
    ; gnsUniversalPropertyAdvancedIsTrue =
        refl
    ; cyclicSeparatingVectorAdvanced =
        true
    ; cyclicSeparatingVectorAdvancedIsTrue =
        refl
    ; cyclicSeparatingVectorPromoted =
        false
    ; cyclicSeparatingVectorPromotedIsFalse =
        refl
    ; firstRemainingAfterGNSWave3 =
        missingTomitaOperator
    ; firstRemainingAfterGNSWave3IsMissingTomitaOperator =
        refl
    ; remainingAfterGNSWave3 =
        canonicalModularTheoryOpenObligations
    ; remainingAfterGNSWave3AreCanonical =
        refl
    ; cstarCompletionHardHalt =
        "cStarCompletion-authority-only-no-represented-C-star-algebra-promotion"
    ; cstarCompletionHardHalt-v =
        refl
    ; bisognanoWichmannHardHalt =
        "BisognanoWichmann-citation-only-before-wedge-modular-proof"
    ; bisognanoWichmannHardHalt-v =
        refl
    ; gnsWave3Boundary =
        "Wave 3 keeps the GNS universal property receipt tied to the selected null-ideal quotient and Hilbert representation"
        ∷ "the cyclic vector and dense cyclic orbit are consumed from canonicalGNSCyclicVectorDensityReceipt"
        ∷ "separating/standardness is advanced as the BW vacuum cyclic-separating target, not as a promoted local theorem"
        ∷ "Tomita operator, modular operator, conjugation, modular flow, and KMS data remain the next modular obligations"
        ∷ []
    }

record TomitaOperatorFrontierReceipt : Setω where
  field
    gnsWave3Progress :
      GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt

    gnsVonNeumannSurface :
      GNSVonNeumannClosureSurface

    cyclicDensityReceipt :
      GNSCyclicVectorDensityReceipt
        abstractRegion
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    vonNeumannClosureReceipt :
      GNSVonNeumannClosureReceipt
        abstractRegion
        abstractGNSHilbertSpace
        abstractGNSRepresentation
        abstractGNSCyclicVector

    cyclicSeparatingTarget :
      Set

    cyclicSeparatingTargetMatchesWave3 :
      cyclicSeparatingTarget
      ≡
      GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt.tomitaCyclicSeparatingTarget
        gnsWave3Progress

    stagedTomitaOperatorTarget :
      TomitaOperator abstractRegion

    stagedTomitaOperatorTargetMatchesSurface :
      stagedTomitaOperatorTarget
      ≡
      abstractTomitaOperator

    tomitaOperatorReceiptInhabited :
      Bool

    tomitaOperatorReceiptInhabitedIsTrue :
      tomitaOperatorReceiptInhabited ≡ true

    tomitaOperatorPromoted :
      Bool

    tomitaOperatorPromotedIsFalse :
      tomitaOperatorPromoted ≡ false

    tomitaPolarDecompositionPromoted :
      Bool

    tomitaPolarDecompositionPromotedIsFalse :
      tomitaPolarDecompositionPromoted ≡ false

    firstResidualTomitaBlocker :
      ModularTheoryOpenObligation

    firstResidualTomitaBlockerIsMissingTomitaOperator :
      firstResidualTomitaBlocker
      ≡
      missingTomitaOperator

    residualTomitaBlockers :
      List ModularTheoryOpenObligation

    residualTomitaBlockersAreCanonical :
      residualTomitaBlockers
      ≡
      canonicalModularTheoryOpenObligations

    tomitaFrontierBoundary :
      List String

open TomitaOperatorFrontierReceipt public

canonicalTomitaOperatorFrontierReceipt :
  TomitaOperatorFrontierReceipt
canonicalTomitaOperatorFrontierReceipt =
  record
    { gnsWave3Progress =
        canonicalGNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt
    ; gnsVonNeumannSurface =
        canonicalGNSVonNeumannClosureSurface
    ; cyclicDensityReceipt =
        canonicalGNSCyclicVectorDensityReceipt
    ; vonNeumannClosureReceipt =
        canonicalGNSVonNeumannClosureReceipt
    ; cyclicSeparatingTarget =
        abstractCyclicSeparatingVectorTarget
    ; cyclicSeparatingTargetMatchesWave3 =
        refl
    ; stagedTomitaOperatorTarget =
        abstractTomitaOperator
    ; stagedTomitaOperatorTargetMatchesSurface =
        refl
    ; tomitaOperatorReceiptInhabited =
        true
    ; tomitaOperatorReceiptInhabitedIsTrue =
        refl
    ; tomitaOperatorPromoted =
        false
    ; tomitaOperatorPromotedIsFalse =
        refl
    ; tomitaPolarDecompositionPromoted =
        false
    ; tomitaPolarDecompositionPromotedIsFalse =
        refl
    ; firstResidualTomitaBlocker =
        missingTomitaOperator
    ; firstResidualTomitaBlockerIsMissingTomitaOperator =
        refl
    ; residualTomitaBlockers =
        canonicalModularTheoryOpenObligations
    ; residualTomitaBlockersAreCanonical =
        refl
    ; tomitaFrontierBoundary =
        "Tomita frontier consumes wave-3 GNS receipts, cyclic density, and von-Neumann weak-closure receipts"
        ∷ "the Tomita operator is only staged as abstractTomitaOperator over the abstract cyclic-separating target"
        ∷ "no closable antilinear S0, polar decomposition, modular operator, conjugation, flow, or KMS theorem is promoted"
        ∷ "the first residual modular blocker remains missingTomitaOperator"
        ∷ []
    }

record Gate5TomitaPolarDecompositionAuthorityTargetReceipt : Setω where
  field
    gnsUniversalPropertyReceipt :
      GNSUniversalPropertyReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    gnsUniversalPropertyThreaded :
      Bool

    gnsUniversalPropertyThreadedIsTrue :
      gnsUniversalPropertyThreaded ≡ true

    gnsUniversalPropertyPromoted :
      GNSUniversalPropertyReceipt.universalPropertyPromoted
        gnsUniversalPropertyReceipt
      ≡
      false

    tomitaFrontier :
      TomitaOperatorFrontierReceipt

    bratteliRobinsonModularAuthority :
      BratteliRobinsonModularAuthorityCitationSurface

    bratteliRobinsonCitationOnly :
      BratteliRobinsonModularAuthorityCitationSurface.citationAuthorityOnly
        bratteliRobinsonModularAuthority
      ≡
      true

    bratteliRobinsonConstructsLocalProof :
      BratteliRobinsonModularAuthorityCitationSurface.constructsLocalTomitaTakesakiProof
        bratteliRobinsonModularAuthority
      ≡
      false

    bwReceiptTarget :
      BisognanoWichmannReceiptTarget

    bisognanoWichmannCitationOnly :
      BisognanoWichmannReceiptTarget.bwPromoted bwReceiptTarget
      ≡
      false

    tomitaOperatorAuthorityTarget :
      TomitaOperator abstractRegion

    tomitaOperatorAuthorityTargetMatchesFrontier :
      tomitaOperatorAuthorityTarget
      ≡
      TomitaOperatorFrontierReceipt.stagedTomitaOperatorTarget
        tomitaFrontier

    polarDecompositionAuthorityTarget :
      Set

    polarDecompositionAuthorityTargetMatchesSurface :
      polarDecompositionAuthorityTarget
      ≡
      abstractTomitaPolarDecompositionTarget

    tomitaOperatorAuthorityTargetRecorded :
      Bool

    tomitaOperatorAuthorityTargetRecordedIsTrue :
      tomitaOperatorAuthorityTargetRecorded ≡ true

    polarDecompositionAuthorityTargetRecorded :
      Bool

    polarDecompositionAuthorityTargetRecordedIsTrue :
      polarDecompositionAuthorityTargetRecorded ≡ true

    tomitaOperatorPromoted :
      TomitaOperatorFrontierReceipt.tomitaOperatorPromoted tomitaFrontier
      ≡
      false

    tomitaPolarDecompositionPromoted :
      TomitaOperatorFrontierReceipt.tomitaPolarDecompositionPromoted
        tomitaFrontier
      ≡
      false

    gate5TomitaAuthorityPromoted :
      Bool

    gate5TomitaAuthorityPromotedIsFalse :
      gate5TomitaAuthorityPromoted ≡ false

    firstGate5TomitaResidual :
      ModularTheoryOpenObligation

    firstGate5TomitaResidualIsMissingTomitaOperator :
      firstGate5TomitaResidual
      ≡
      missingTomitaOperator

    gate5TomitaAuthorityBoundary :
      List String

open Gate5TomitaPolarDecompositionAuthorityTargetReceipt public

record M4GNSNullIdealHilbertUniversalFailClosedReceipt : Setω where
  field
    l5FirstMissingChainModuleLabel :
      String

    l5FirstMissingChainModuleLabel-v :
      l5FirstMissingChainModuleLabel
      ≡
      "AQFTCarrierAlgebraQuotientSurface.AQFTFirstMissingChainReceipt"

    l5AQFTFirstMissingChainDirectlyImportedHere :
      Bool

    l5AQFTFirstMissingChainDirectlyImportedHere-v :
      l5AQFTFirstMissingChainDirectlyImportedHere ≡ false

    directImportBlockerLabel :
      String

    directImportBlockerLabel-v :
      directImportBlockerLabel
      ≡
      "AQFTCarrierAlgebraQuotientSurface imports ModularTheoryReceiptSurface"

    gnsWave3Progress :
      GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt

    nullIdealPreHilbertQuotientReceipt :
      GNSNullIdealPreHilbertQuotientReceipt
        abstractRegion
        abstractStateFunctional

    hilbertRepresentationReceipt :
      GNSHilbertRepresentationReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient

    universalPropertyReceipt :
      GNSUniversalPropertyReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    tomitaFrontier :
      TomitaOperatorFrontierReceipt

    bwTarget :
      BisognanoWichmannReceiptTarget

    geometricBWNetReceipt :
      GeometricBisognanoWichmannNetReceipt

    nullIdealQuotientReceiptInhabited :
      GNSNullIdealPreHilbertQuotientReceipt.quotientCurrentlyInhabitedAsReceipt
        nullIdealPreHilbertQuotientReceipt
      ≡
      true

    nullIdealQuotientTheoremPromoted :
      GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromoted
        nullIdealPreHilbertQuotientReceipt
      ≡
      false

    hilbertRepresentationReceiptInhabited :
      GNSHilbertRepresentationReceipt.hilbertRepresentationCurrentlyInhabitedAsReceipt
        hilbertRepresentationReceipt
      ≡
      true

    hilbertRepresentationPromoted :
      GNSHilbertRepresentationReceipt.hilbertRepresentationPromoted
        hilbertRepresentationReceipt
      ≡
      false

    universalPropertyReceiptInhabited :
      GNSUniversalPropertyReceipt.universalPropertyReceiptInhabited
        universalPropertyReceipt
      ≡
      true

    universalPropertyPromoted :
      GNSUniversalPropertyReceipt.universalPropertyPromoted
        universalPropertyReceipt
      ≡
      false

    tomitaOperatorPromoted :
      TomitaOperatorFrontierReceipt.tomitaOperatorPromoted tomitaFrontier
      ≡
      false

    bwPromoted :
      BisognanoWichmannReceiptTarget.bwPromoted bwTarget
      ≡
      false

    geometricBWNetPromoted :
      GeometricBisognanoWichmannNetReceipt.geometricBWNetAuthorityPromoted
        geometricBWNetReceipt
      ≡
      false

    missingDASHILocalAlgebraBlocksActualPromotion :
      Bool

    missingDASHILocalAlgebraBlocksActualPromotion-v :
      missingDASHILocalAlgebraBlocksActualPromotion ≡ true

    cstarCompletionBlocksActualPromotion :
      Bool

    cstarCompletionBlocksActualPromotion-v :
      cstarCompletionBlocksActualPromotion ≡ true

    tomitaBWBlocksActualPromotion :
      Bool

    tomitaBWBlocksActualPromotion-v :
      tomitaBWBlocksActualPromotion ≡ true

    m4GNSActualPromotion :
      Bool

    m4GNSActualPromotion-v :
      m4GNSActualPromotion ≡ false

    firstResidualModularBlocker :
      ModularTheoryOpenObligation

    firstResidualModularBlocker-v :
      firstResidualModularBlocker
      ≡
      missingTomitaOperator

    receiptBoundary :
      List String

open M4GNSNullIdealHilbertUniversalFailClosedReceipt public

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
        ∷ "cyclic-separating standardness is a wave-3 target receipt, while polar-decomposition and modular-operator laws are not discharged here"
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

canonicalGate5TomitaPolarDecompositionAuthorityTargetReceipt :
  Gate5TomitaPolarDecompositionAuthorityTargetReceipt
canonicalGate5TomitaPolarDecompositionAuthorityTargetReceipt =
  record
    { gnsUniversalPropertyReceipt =
        canonicalGNSUniversalPropertyReceipt
    ; gnsUniversalPropertyThreaded =
        true
    ; gnsUniversalPropertyThreadedIsTrue =
        refl
    ; gnsUniversalPropertyPromoted =
        GNSUniversalPropertyReceipt.universalPropertyPromotedIsFalse
          canonicalGNSUniversalPropertyReceipt
    ; tomitaFrontier =
        canonicalTomitaOperatorFrontierReceipt
    ; bratteliRobinsonModularAuthority =
        canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bratteliRobinsonCitationOnly =
        BratteliRobinsonModularAuthorityCitationSurface.citationAuthorityOnlyIsTrue
          canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bratteliRobinsonConstructsLocalProof =
        BratteliRobinsonModularAuthorityCitationSurface.constructsLocalTomitaTakesakiProofIsFalse
          canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; bwReceiptTarget =
        canonicalBisognanoWichmannReceiptTarget
    ; bisognanoWichmannCitationOnly =
        BisognanoWichmannReceiptTarget.bwPromotedIsFalse
          canonicalBisognanoWichmannReceiptTarget
    ; tomitaOperatorAuthorityTarget =
        abstractTomitaOperator
    ; tomitaOperatorAuthorityTargetMatchesFrontier =
        refl
    ; polarDecompositionAuthorityTarget =
        abstractTomitaPolarDecompositionTarget
    ; polarDecompositionAuthorityTargetMatchesSurface =
        refl
    ; tomitaOperatorAuthorityTargetRecorded =
        true
    ; tomitaOperatorAuthorityTargetRecordedIsTrue =
        refl
    ; polarDecompositionAuthorityTargetRecorded =
        true
    ; polarDecompositionAuthorityTargetRecordedIsTrue =
        refl
    ; tomitaOperatorPromoted =
        TomitaOperatorFrontierReceipt.tomitaOperatorPromotedIsFalse
          canonicalTomitaOperatorFrontierReceipt
    ; tomitaPolarDecompositionPromoted =
        TomitaOperatorFrontierReceipt.tomitaPolarDecompositionPromotedIsFalse
          canonicalTomitaOperatorFrontierReceipt
    ; gate5TomitaAuthorityPromoted =
        false
    ; gate5TomitaAuthorityPromotedIsFalse =
        refl
    ; firstGate5TomitaResidual =
        missingTomitaOperator
    ; firstGate5TomitaResidualIsMissingTomitaOperator =
        refl
    ; gate5TomitaAuthorityBoundary =
        "Gate 5 threads the GNS universal-property receipt before naming the Tomita operator and polar-decomposition authority targets"
        ∷ "Bratteli-Robinson modular authority is citation-only and does not construct the local Tomita-Takesaki theorem"
        ∷ "Bisognano-Wichmann remains a citation/dependency target with promotion fixed false"
        ∷ "Tomita operator and polar decomposition are recorded targets only; the first residual remains missingTomitaOperator"
        ∷ []
    }

canonicalPostPaper7BisognanoWichmannInternalProofTargetSurface :
  PostPaper7BisognanoWichmannInternalProofTargetSurface
canonicalPostPaper7BisognanoWichmannInternalProofTargetSurface =
  record
    { citationAuthority =
        canonicalBorchersBGLAuthorityCitationSurface
    ; bwReceiptTarget =
        canonicalBisognanoWichmannReceiptTarget
    ; geometricBWNetReceipt =
        canonicalGeometricBisognanoWichmannNetReceipt
    ; wedgeRegion =
        abstractRegion
    ; wedgeAlgebra =
        abstractPostPaper7WedgeAlgebra
    ; wedgeModularFlow =
        abstractModularFlow
    ; lorentzBoostFlow =
        abstractLorentzBoostFlow
    ; equalityTargetLabel =
        "Delta_W^it A(W) Delta_W^-it = U(Lambda_W(2*pi*t)) A(W) U(Lambda_W(2*pi*t))^-1"
    ; equalityTargetLabel-v =
        refl
    ; haagDualityDependency =
        abstractPostPaper7BWHaagDualityDependency
    ; reehSchliederDependency =
        abstractPostPaper7BWReehSchliederDependency
    ; poincareCovarianceDependency =
        abstractPostPaper7BWPoincareCovarianceDependency
    ; positiveEnergyDependency =
        abstractPostPaper7BWPositiveEnergyDependency
    ; modularFlowEqualsLorentzBoostTarget =
        abstractPostPaper7BWModularFlowEqualsLorentzBoostTarget
    ; dependenciesThreaded =
        true
    ; dependenciesThreadedIsTrue =
        refl
    ; citationAuthorityOnly =
        true
    ; citationAuthorityOnlyIsTrue =
        refl
    ; citationAuthorityConstructsLocalProof =
        BorchersBGLAuthorityCitationSurface.constructsLocalModularTheoremIsFalse
          canonicalBorchersBGLAuthorityCitationSurface
    ; bwReceiptPromotionStillFalse =
        BisognanoWichmannReceiptTarget.bwPromotedIsFalse
          canonicalBisognanoWichmannReceiptTarget
    ; geometricAuthorityPromotionStillFalse =
        GeometricBisognanoWichmannNetReceipt.geometricBWNetAuthorityPromotedIsFalse
          canonicalGeometricBisognanoWichmannNetReceipt
    ; internalBWProofConstructed =
        false
    ; internalBWProofConstructedIsFalse =
        refl
    ; postPaper7BWPromoted =
        false
    ; postPaper7BWPromotedIsFalse =
        refl
    ; postPaper7BWBoundary =
        "post-Paper7 BW internal-proof target names the wedge algebra, wedge modular flow, Lorentz boost flow, and their equality target"
        ∷ "Haag duality, Reeh-Schlieder, Poincare covariance, and positive energy are explicit dependencies of the equality target"
        ∷ "Borchers/BGL/geometric-net authority remains citation-only and does not construct the internal proof"
        ∷ "the BW receipt, geometric authority, internal proof, and post-Paper7 BW promotion flags remain false"
        ∷ []
    }

canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt :
  M4GNSNullIdealHilbertUniversalFailClosedReceipt
canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt =
  record
    { l5FirstMissingChainModuleLabel =
        "AQFTCarrierAlgebraQuotientSurface.AQFTFirstMissingChainReceipt"
    ; l5FirstMissingChainModuleLabel-v =
        refl
    ; l5AQFTFirstMissingChainDirectlyImportedHere =
        false
    ; l5AQFTFirstMissingChainDirectlyImportedHere-v =
        refl
    ; directImportBlockerLabel =
        "AQFTCarrierAlgebraQuotientSurface imports ModularTheoryReceiptSurface"
    ; directImportBlockerLabel-v =
        refl
    ; gnsWave3Progress =
        canonicalGNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt
    ; nullIdealPreHilbertQuotientReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; hilbertRepresentationReceipt =
        canonicalGNSHilbertRepresentationReceipt
    ; universalPropertyReceipt =
        canonicalGNSUniversalPropertyReceipt
    ; tomitaFrontier =
        canonicalTomitaOperatorFrontierReceipt
    ; bwTarget =
        canonicalBisognanoWichmannReceiptTarget
    ; geometricBWNetReceipt =
        canonicalGeometricBisognanoWichmannNetReceipt
    ; nullIdealQuotientReceiptInhabited =
        refl
    ; nullIdealQuotientTheoremPromoted =
        refl
    ; hilbertRepresentationReceiptInhabited =
        refl
    ; hilbertRepresentationPromoted =
        refl
    ; universalPropertyReceiptInhabited =
        refl
    ; universalPropertyPromoted =
        refl
    ; tomitaOperatorPromoted =
        refl
    ; bwPromoted =
        refl
    ; geometricBWNetPromoted =
        refl
    ; missingDASHILocalAlgebraBlocksActualPromotion =
        true
    ; missingDASHILocalAlgebraBlocksActualPromotion-v =
        refl
    ; cstarCompletionBlocksActualPromotion =
        true
    ; cstarCompletionBlocksActualPromotion-v =
        refl
    ; tomitaBWBlocksActualPromotion =
        true
    ; tomitaBWBlocksActualPromotion-v =
        refl
    ; m4GNSActualPromotion =
        false
    ; m4GNSActualPromotion-v =
        refl
    ; firstResidualModularBlocker =
        missingTomitaOperator
    ; firstResidualModularBlocker-v =
        refl
    ; receiptBoundary =
        "Modular cannot directly import the l5 AQFTFirstMissingChainReceipt because the l5 carrier quotient surface imports ModularTheoryReceiptSurface"
        ∷ "the null ideal, pre-Hilbert quotient, Hilbert representation, and GNS universal-property receipts are nevertheless threaded locally"
        ∷ "missingDASHILocalAlgebra and C-star completion remain actual-promotion blockers upstream"
        ∷ "Tomita and Bisognano-Wichmann surfaces remain non-promoting; the first modular residual is missingTomitaOperator"
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

    gnsAQFTWave2Progress :
      GNSAQFTWave2ProgressReceipt

    gnsAQFTWave3Progress :
      GNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt

    tomitaOperatorFrontier :
      TomitaOperatorFrontierReceipt

    m4GNSFailClosedBlockerReceipt :
      M4GNSNullIdealHilbertUniversalFailClosedReceipt

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

    bratteliRobinsonModularAuthority :
      BratteliRobinsonModularAuthorityCitationSurface

    gate5TomitaPolarDecompositionAuthorityTarget :
      Gate5TomitaPolarDecompositionAuthorityTargetReceipt

    bisognanoWichmannAuthority :
      BisognanoWichmannAuthorityReceipt

    geometricBisognanoWichmannNetReceipt :
      GeometricBisognanoWichmannNetReceipt

    postPaper7BWInternalProofTarget :
      PostPaper7BisognanoWichmannInternalProofTargetSurface

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
    ; gnsAQFTWave2Progress =
        canonicalGNSAQFTWave2ProgressReceipt
    ; gnsAQFTWave3Progress =
        canonicalGNSAQFTWave3CyclicSeparatingUniversalPropertyReceipt
    ; tomitaOperatorFrontier =
        canonicalTomitaOperatorFrontierReceipt
    ; m4GNSFailClosedBlockerReceipt =
        canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt
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
    ; bratteliRobinsonModularAuthority =
        canonicalBratteliRobinsonModularAuthorityCitationSurface
    ; gate5TomitaPolarDecompositionAuthorityTarget =
        canonicalGate5TomitaPolarDecompositionAuthorityTargetReceipt
    ; bisognanoWichmannAuthority =
        canonicalBisognanoWichmannAuthorityReceipt
    ; geometricBisognanoWichmannNetReceipt =
        canonicalGeometricBisognanoWichmannNetReceipt
    ; postPaper7BWInternalProofTarget =
        canonicalPostPaper7BisognanoWichmannInternalProofTargetSurface
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
        ∷ "GNS state, null ideal, pre-Hilbert quotient, Hilbert representation, cyclic density, and weak-closure receipts are now inhabited abstractly"
        ∷ "the Gate5-AQFT/GNS wave consumes the l5 DepthFilteredLocalAlgebraSurface and safe C*-completion authority by label, with null-ideal quotient, universal-property, and density receipts tied together"
        ∷ "wave 3 advances the cyclic-separating target as a non-promoting BW standardness receipt"
        ∷ "TomitaOperatorFrontierReceipt consumes the strongest GNS/von-Neumann staging and still halts at missingTomitaOperator"
        ∷ "Gate5TomitaPolarDecompositionAuthorityTargetReceipt threads the GNS universal property into Bratteli-Robinson citation-only Tomita/polar-decomposition targets"
        ∷ "M4GNSNullIdealHilbertUniversalFailClosedReceipt records that Modular cannot import the l5 chain directly, while GNS quotient, Hilbert representation, and universal-property receipts remain non-promoting"
        ∷ "the canonical GNS frontier now first-misses at missingTomitaOperator before modular operator, conjugation, flow, and KMS data"
        ∷ "Borchers/BGL/geometric-net authority is cited only as a non-promoting postulate-shaped receipt for wedge modular flow equals boost flow"
        ∷ "GeometricBisognanoWichmannNetReceipt records W_R, boost flow, sigma^omega = boost, and the Haag-duality/covariance/energy/standardness hypotheses"
        ∷ "PostPaper7BisognanoWichmannInternalProofTargetSurface adds the wedge-algebra/modular-flow/Lorentz-boost equality target with Haag-duality, Reeh-Schlieder, Poincare-covariance, and positive-energy dependencies"
        ∷ "Tomita-Takesaki, wedge, covariance, and spectrum-condition data remain abstract obligations"
        ∷ "this module does not construct a C-star algebra representation, thermal state, vacuum, interacting QFT, Standard Model, or GRQFT receipt"
        ∷ []
    }

record M4GNSNullIdealPreHilbertHilbertBridgeReceipt : Setω where
  field
    modularSurface :
      ModularTheoryReceiptSurface

    nullIdealPreHilbertQuotientReceipt :
      GNSNullIdealPreHilbertQuotientReceipt
        abstractRegion
        abstractStateFunctional

    hilbertRepresentationReceipt :
      GNSHilbertRepresentationReceipt
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient

    nullIdealMatches :
      GNSNullIdealPreHilbertQuotientReceipt.nullIdeal
        nullIdealPreHilbertQuotientReceipt
      ≡
      abstractGNSNullIdeal

    preHilbertQuotientMatches :
      subst
        (λ ideal →
          GNSPreHilbertQuotient abstractRegion abstractStateFunctional ideal)
        nullIdealMatches
        (GNSNullIdealPreHilbertQuotientReceipt.preHilbertQuotient
          nullIdealPreHilbertQuotientReceipt)
      ≡
      abstractGNSPreHilbertQuotient

    hilbertSpaceMatches :
      GNSHilbertRepresentationReceipt.hilbertSpace
        hilbertRepresentationReceipt
      ≡
      abstractGNSHilbertSpace

    representationMatches :
      subst
        (λ hilbert →
          GNSRepresentation abstractRegion hilbert)
        hilbertSpaceMatches
        (GNSHilbertRepresentationReceipt.representation
          hilbertRepresentationReceipt)
      ≡
      abstractGNSRepresentation

    nullIdealLeftIdealTargetThreaded :
      Bool

    nullIdealLeftIdealTargetThreadedIsTrue :
      nullIdealLeftIdealTargetThreaded ≡ true

    innerProductDescendsTargetThreaded :
      Bool

    innerProductDescendsTargetThreadedIsTrue :
      innerProductDescendsTargetThreaded ≡ true

    hilbertCompletionTargetThreaded :
      Bool

    hilbertCompletionTargetThreadedIsTrue :
      hilbertCompletionTargetThreaded ≡ true

    quotientTheoremPromoted :
      GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromoted
        nullIdealPreHilbertQuotientReceipt
      ≡
      false

    hilbertRepresentationPromoted :
      GNSHilbertRepresentationReceipt.hilbertRepresentationPromoted
        hilbertRepresentationReceipt
      ≡
      false

    gnsHilbertBridgePromoted :
      Bool

    gnsHilbertBridgePromotedIsFalse :
      gnsHilbertBridgePromoted ≡ false

    receiptBoundary :
      List String

open M4GNSNullIdealPreHilbertHilbertBridgeReceipt public

canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt :
  M4GNSNullIdealPreHilbertHilbertBridgeReceipt
canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt =
  record
    { modularSurface =
        canonicalModularTheoryReceiptSurface
    ; nullIdealPreHilbertQuotientReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; hilbertRepresentationReceipt =
        canonicalGNSHilbertRepresentationReceipt
    ; nullIdealMatches =
        refl
    ; preHilbertQuotientMatches =
        refl
    ; hilbertSpaceMatches =
        refl
    ; representationMatches =
        refl
    ; nullIdealLeftIdealTargetThreaded =
        true
    ; nullIdealLeftIdealTargetThreadedIsTrue =
        refl
    ; innerProductDescendsTargetThreaded =
        true
    ; innerProductDescendsTargetThreadedIsTrue =
        refl
    ; hilbertCompletionTargetThreaded =
        true
    ; hilbertCompletionTargetThreadedIsTrue =
        refl
    ; quotientTheoremPromoted =
        GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromotedIsFalse
          canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; hilbertRepresentationPromoted =
        GNSHilbertRepresentationReceipt.hilbertRepresentationPromotedIsFalse
          canonicalGNSHilbertRepresentationReceipt
    ; gnsHilbertBridgePromoted =
        false
    ; gnsHilbertBridgePromotedIsFalse =
        refl
    ; receiptBoundary =
        "The GNS null ideal, pre-Hilbert quotient, Hilbert completion target, and representation target are threaded together"
        ∷ "left-ideal, inner-product descent, Hilbert completion, and representation well-definedness remain target fields"
        ∷ "the null-ideal quotient theorem and Hilbert representation are inhabited receipts only, with promotion fixed false"
        ∷ "no C-star representation, Tomita operator, Bisognano-Wichmann theorem, or DASHI Hilbert bridge is constructed here"
        ∷ []
    }

record Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt : Setω where
  field
    modularFailClosedReceipt :
      M4GNSNullIdealHilbertUniversalFailClosedReceipt

    hilbertBridgeReceipt :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt

    parametricRegion :
      AQFT.Region

    parametricRegionMatchesAbstract :
      parametricRegion
      ≡
      abstractRegion

    parametricStateFunctional :
      StateFunctional parametricRegion

    parametricNullIdeal :
      GNSNullIdeal abstractRegion abstractStateFunctional

    parametricPreHilbertQuotient :
      GNSPreHilbertQuotient
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal

    nullIdealLeftIdealTargetThreaded :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealLeftIdealTargetThreaded
        hilbertBridgeReceipt
      ≡
      true

    innerProductDescendsTargetThreaded :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt.innerProductDescendsTargetThreaded
        hilbertBridgeReceipt
      ≡
      true

    quotientTheoremPromotedStillFalse :
      GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromoted
        (M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealPreHilbertQuotientReceipt
          hilbertBridgeReceipt)
      ≡
      false

    hilbertRepresentationPromotedStillFalse :
      GNSHilbertRepresentationReceipt.hilbertRepresentationPromoted
        (M4GNSNullIdealPreHilbertHilbertBridgeReceipt.hilbertRepresentationReceipt
          hilbertBridgeReceipt)
      ≡
      false

    universalPropertyReceiptInhabited :
      GNSUniversalPropertyReceipt.universalPropertyReceiptInhabited
        (M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyReceipt
          modularFailClosedReceipt)
      ≡
      true

    universalPropertyPromoted :
      GNSUniversalPropertyReceipt.universalPropertyPromoted
        (M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyReceipt
          modularFailClosedReceipt)
      ≡
      false

    cauchySchwarzStateInequalityBlocker :
      String

    cauchySchwarzStateInequalityBlocker-v :
      cauchySchwarzStateInequalityBlocker
      ≡
      "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"

    missingCauchySchwarzLaws :
      List GNSCauchySchwarzMissingLaw

    missingCauchySchwarzLawsAreCanonical :
      missingCauchySchwarzLaws
      ≡
      canonicalGNSCauchySchwarzMissingLaws

    gnsActualPromotion :
      Bool

    gnsActualPromotionIsFalse :
      gnsActualPromotion ≡ false

    receiptBoundary :
      List String

open Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt public

canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt :
  Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt =
  record
    { modularFailClosedReceipt =
        canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt
    ; hilbertBridgeReceipt =
        canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; parametricRegion =
        abstractRegion
    ; parametricRegionMatchesAbstract =
        refl
    ; parametricStateFunctional =
        abstractStateFunctional
    ; parametricNullIdeal =
        abstractGNSNullIdeal
    ; parametricPreHilbertQuotient =
        abstractGNSPreHilbertQuotient
    ; nullIdealLeftIdealTargetThreaded =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealLeftIdealTargetThreadedIsTrue
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; innerProductDescendsTargetThreaded =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.innerProductDescendsTargetThreadedIsTrue
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; quotientTheoremPromotedStillFalse =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.quotientTheoremPromoted
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; hilbertRepresentationPromotedStillFalse =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.hilbertRepresentationPromoted
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; universalPropertyReceiptInhabited =
        M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyReceiptInhabited
          canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt
    ; universalPropertyPromoted =
        M4GNSNullIdealHilbertUniversalFailClosedReceipt.universalPropertyPromoted
          canonicalM4GNSNullIdealHilbertUniversalFailClosedReceipt
    ; cauchySchwarzStateInequalityBlocker =
        "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"
    ; cauchySchwarzStateInequalityBlocker-v =
        refl
    ; missingCauchySchwarzLaws =
        canonicalGNSCauchySchwarzMissingLaws
    ; missingCauchySchwarzLawsAreCanonical =
        refl
    ; gnsActualPromotion =
        false
    ; gnsActualPromotionIsFalse =
        refl
    ; receiptBoundary =
        "middle6 modular GNS records the parametric state functional, null ideal, and pre-Hilbert quotient as threaded receipt data"
        ∷ "left-ideal and inner-product descent targets are threaded, but the quotient theorem and Hilbert representation remain unpromoted"
        ∷ "the blocker for a real parametric null ideal is the missing state Cauchy-Schwarz inequality over the pre-C-star algebra surface"
        ∷ "the universal-property receipt is inhabited as a target only and remains promoted false"
        ∷ []
    }

record M4GNSInnerProductNullIdealWellDefinednessReceipt : Setω where
  field
    nullIdealHilbertBridge :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt

    nullIdealReceipt :
      GNSNullIdealPreHilbertQuotientReceipt
        abstractRegion
        abstractStateFunctional

    nullIdealReceiptMatchesBridge :
      Bool

    nullIdealReceiptMatchesBridgeIsTrue :
      nullIdealReceiptMatchesBridge ≡ true

    nullIdealLeftIdealTarget :
      GNSNullIdealLeftIdealTarget
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal

    innerProductDescendsTarget :
      GNSInnerProductDescendsTarget
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient

    quotientRepresentationWellDefinedTarget :
      GNSQuotientRepresentationWellDefinedTarget
        abstractRegion
        abstractStateFunctional
        abstractGNSNullIdeal
        abstractGNSPreHilbertQuotient
        abstractGNSHilbertSpace
        abstractGNSRepresentation

    nullIdealLeftIdealThreaded :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealLeftIdealTargetThreaded
        nullIdealHilbertBridge
      ≡
      true

    innerProductDescendsThreaded :
      M4GNSNullIdealPreHilbertHilbertBridgeReceipt.innerProductDescendsTargetThreaded
        nullIdealHilbertBridge
      ≡
      true

    quotientTheoremPromoted :
      GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromoted
        nullIdealReceipt
      ≡
      false

    cauchySchwarzBlocker :
      String

    cauchySchwarzBlocker-v :
      cauchySchwarzBlocker
      ≡
      "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"

    missingCauchySchwarzLaws :
      List GNSCauchySchwarzMissingLaw

    missingCauchySchwarzLawsAreCanonical :
      missingCauchySchwarzLaws
      ≡
      canonicalGNSCauchySchwarzMissingLaws

    leftIdealClosureLawBlocker :
      GNSCauchySchwarzMissingLaw

    leftIdealClosureLawBlockerIsMissing :
      leftIdealClosureLawBlocker
      ≡
      missingNullIdealLeftMultiplicationClosureLaw

    wellDefinednessPromoted :
      Bool

    wellDefinednessPromotedIsFalse :
      wellDefinednessPromoted ≡ false

    receiptBoundary :
      List String

open M4GNSInnerProductNullIdealWellDefinednessReceipt public

canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt :
  M4GNSInnerProductNullIdealWellDefinednessReceipt
canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt =
  record
    { nullIdealHilbertBridge =
        canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; nullIdealReceipt =
        canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; nullIdealReceiptMatchesBridge =
        true
    ; nullIdealReceiptMatchesBridgeIsTrue =
        refl
    ; nullIdealLeftIdealTarget =
        abstractGNSNullIdealLeftIdealTarget
    ; innerProductDescendsTarget =
        abstractGNSInnerProductDescendsTarget
    ; quotientRepresentationWellDefinedTarget =
        abstractGNSQuotientRepresentationWellDefinedTarget
    ; nullIdealLeftIdealThreaded =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealLeftIdealTargetThreadedIsTrue
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; innerProductDescendsThreaded =
        M4GNSNullIdealPreHilbertHilbertBridgeReceipt.innerProductDescendsTargetThreadedIsTrue
          canonicalM4GNSNullIdealPreHilbertHilbertBridgeReceipt
    ; quotientTheoremPromoted =
        GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromotedIsFalse
          canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; cauchySchwarzBlocker =
        "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"
    ; cauchySchwarzBlocker-v =
        refl
    ; missingCauchySchwarzLaws =
        canonicalGNSCauchySchwarzMissingLaws
    ; missingCauchySchwarzLawsAreCanonical =
        refl
    ; leftIdealClosureLawBlocker =
        missingNullIdealLeftMultiplicationClosureLaw
    ; leftIdealClosureLawBlockerIsMissing =
        refl
    ; wellDefinednessPromoted =
        false
    ; wellDefinednessPromotedIsFalse =
        refl
    ; receiptBoundary =
        "m4 records the GNS null ideal as a left-ideal target and the inner product as a descent target on A/N_phi"
        ∷ "representation well-definedness is threaded through the Hilbert representation receipt"
        ∷ "these are inhabited receipt sockets only; the quotient theorem is still promoted false"
        ∷ "the remaining blocker is the state Cauchy-Schwarz inequality over the parametric pre-C-star algebra"
        ∷ []
    }

record M4FiniteTraceStateCauchySchwarzDescentReceipt : Setω where
  field
    parametricGNSReceipt :
      Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt

    wellDefinednessReceipt :
      M4GNSInnerProductNullIdealWellDefinednessReceipt

    finiteTraceStateSurface :
      Set

    finiteTraceStateSurfaceLabel :
      String

    finiteTraceStateSurfaceLabel-v :
      finiteTraceStateSurfaceLabel
      ≡
      "finite-trace-state-on-parametric-pre-C-star-algebra"

    traceStateCauchySchwarzTarget :
      finiteTraceStateSurface →
      Set

    traceStateCauchySchwarzAttempted :
      Bool

    traceStateCauchySchwarzAttemptedIsTrue :
      traceStateCauchySchwarzAttempted ≡ true

    traceStateCauchySchwarzProved :
      Bool

    traceStateCauchySchwarzProvedIsFalse :
      traceStateCauchySchwarzProved ≡ false

    nullIdealLeftIdealTargetThreaded :
      Bool

    nullIdealLeftIdealTargetThreadedIsTrue :
      nullIdealLeftIdealTargetThreaded ≡ true

    innerProductDescendsTargetThreaded :
      Bool

    innerProductDescendsTargetThreadedIsTrue :
      innerProductDescendsTargetThreaded ≡ true

    quotientInnerProductDescentAttempted :
      Bool

    quotientInnerProductDescentAttemptedIsTrue :
      quotientInnerProductDescentAttempted ≡ true

    quotientInnerProductDescentPromoted :
      Bool

    quotientInnerProductDescentPromotedIsFalse :
      quotientInnerProductDescentPromoted ≡ false

    quotientTheoremPromoted :
      Bool

    quotientTheoremPromotedIsFalse :
      quotientTheoremPromoted ≡ false

    exactAnalyticBlocker :
      String

    exactAnalyticBlocker-v :
      exactAnalyticBlocker
      ≡
      "missingFiniteTraceStateCauchySchwarzForParametricPreCStarAlgebra"

    exactMissingLaws :
      List GNSCauchySchwarzMissingLaw

    exactMissingLawsAreCanonical :
      exactMissingLaws
      ≡
      canonicalGNSCauchySchwarzMissingLaws

    firstFiniteTraceMissingLaw :
      GNSCauchySchwarzMissingLaw

    firstFiniteTraceMissingLawIsPositiveFunctional :
      firstFiniteTraceMissingLaw
      ≡
      missingPositiveFiniteTraceStateFunctional

    inheritedParametricBlocker :
      Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.cauchySchwarzStateInequalityBlocker
        parametricGNSReceipt
      ≡
      "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"

    finiteTraceStateAPIAvailable :
      Bool

    finiteTraceStateAPIAvailableIsFalse :
      finiteTraceStateAPIAvailable ≡ false

    finiteTracePrimitiveAuditAdvanced :
      Bool

    finiteTracePrimitiveAuditAdvancedIsTrue :
      finiteTracePrimitiveAuditAdvanced ≡ true

    finiteTraceDescentPromoted :
      Bool

    finiteTraceDescentPromotedIsFalse :
      finiteTraceDescentPromoted ≡ false

    receiptBoundary :
      List String

open M4FiniteTraceStateCauchySchwarzDescentReceipt public

canonicalM4FiniteTraceStateCauchySchwarzDescentReceipt :
  M4FiniteTraceStateCauchySchwarzDescentReceipt
canonicalM4FiniteTraceStateCauchySchwarzDescentReceipt =
  record
    { parametricGNSReceipt =
        canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
    ; wellDefinednessReceipt =
        canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; finiteTraceStateSurface =
        Bool
    ; finiteTraceStateSurfaceLabel =
        "finite-trace-state-on-parametric-pre-C-star-algebra"
    ; finiteTraceStateSurfaceLabel-v =
        refl
    ; traceStateCauchySchwarzTarget =
        λ _ →
          Bool
    ; traceStateCauchySchwarzAttempted =
        true
    ; traceStateCauchySchwarzAttemptedIsTrue =
        refl
    ; traceStateCauchySchwarzProved =
        false
    ; traceStateCauchySchwarzProvedIsFalse =
        refl
    ; nullIdealLeftIdealTargetThreaded =
        true
    ; nullIdealLeftIdealTargetThreadedIsTrue =
        refl
    ; innerProductDescendsTargetThreaded =
        true
    ; innerProductDescendsTargetThreadedIsTrue =
        refl
    ; quotientInnerProductDescentAttempted =
        true
    ; quotientInnerProductDescentAttemptedIsTrue =
        refl
    ; quotientInnerProductDescentPromoted =
        false
    ; quotientInnerProductDescentPromotedIsFalse =
        refl
    ; quotientTheoremPromoted =
        false
    ; quotientTheoremPromotedIsFalse =
        refl
    ; exactAnalyticBlocker =
        "missingFiniteTraceStateCauchySchwarzForParametricPreCStarAlgebra"
    ; exactAnalyticBlocker-v =
        refl
    ; exactMissingLaws =
        canonicalGNSCauchySchwarzMissingLaws
    ; exactMissingLawsAreCanonical =
        refl
    ; firstFiniteTraceMissingLaw =
        missingPositiveFiniteTraceStateFunctional
    ; firstFiniteTraceMissingLawIsPositiveFunctional =
        refl
    ; inheritedParametricBlocker =
        Middle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt.cauchySchwarzStateInequalityBlocker-v
          canonicalMiddle6ParametricGNSNullIdealUniversalPropertyFailClosedReceipt
    ; finiteTraceStateAPIAvailable =
        false
    ; finiteTraceStateAPIAvailableIsFalse =
        refl
    ; finiteTracePrimitiveAuditAdvanced =
        true
    ; finiteTracePrimitiveAuditAdvancedIsTrue =
        refl
    ; finiteTraceDescentPromoted =
        false
    ; finiteTraceDescentPromotedIsFalse =
        refl
    ; receiptBoundary =
        "m4 finite trace-state lane stages Cauchy-Schwarz as a target over the parametric pre-C-star algebra"
        ∷ "null-ideal left-ideal and inner-product descent targets are threaded from M4GNSInnerProductNullIdealWellDefinednessReceipt"
        ∷ "finite trace-state API is not available here; the exact missing primitive audit is canonicalGNSCauchySchwarzMissingLaws"
        ∷ "quotient inner-product descent is attempted but remains non-promoting because finite trace-state positivity, star/order laws, Cauchy-Schwarz, and null-ideal left multiplication closure are not supplied"
        ∷ "this does not construct a GNS Hilbert representation theorem, Tomita operator, BW theorem, or represented C-star algebra"
        ∷ []
    }
