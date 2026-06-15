module DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as GRBianchi
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NFScalar
import DASHI.Physics.Closure.GRSelectedNonFlatMetricInstance as SelectedMetric
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild

------------------------------------------------------------------------
-- GR discrete Ricci candidate from curvature.
--
-- This is the C2 follow-on to DiscreteConnectionCandidateFromCRT.  It consumes
-- the expected C1 diagnostic surface and records the smallest typed Ricci
-- shape available from a curvature/Riemann contraction interface.  It does not
-- promote GR, finite-r Bianchi, a non-flat connection, or an Einstein equation.

data GRDiscreteRicciCandidateStatus : Set where
  candidateShapeOnly :
    GRDiscreteRicciCandidateStatus

data GRDiscreteRicciFieldEquationStatus : Set where
  candidateShape :
    GRDiscreteRicciFieldEquationStatus

data GRDiscreteRicciCandidateFirstMissing : Set where
  missingBianchiIdentityProof :
    GRDiscreteRicciCandidateFirstMissing

data GRDiscreteRicciCandidateUnsupportedClaim : Set where
  unsupportedNonFlatConnectionClaim :
    GRDiscreteRicciCandidateUnsupportedClaim
  unsupportedFiniteRBianchiClaim :
    GRDiscreteRicciCandidateUnsupportedClaim
  unsupportedRicciTheoremClaim :
    GRDiscreteRicciCandidateUnsupportedClaim
  unsupportedEinsteinEquationClaim :
    GRDiscreteRicciCandidateUnsupportedClaim
  unsupportedGRPromotionClaim :
    GRDiscreteRicciCandidateUnsupportedClaim

canonicalGRDiscreteRicciCandidateUnsupportedClaims :
  List GRDiscreteRicciCandidateUnsupportedClaim
canonicalGRDiscreteRicciCandidateUnsupportedClaims =
  unsupportedNonFlatConnectionClaim
  ∷ unsupportedFiniteRBianchiClaim
  ∷ unsupportedRicciTheoremClaim
  ∷ unsupportedEinsteinEquationClaim
  ∷ unsupportedGRPromotionClaim
  ∷ []

private
  flatEinsteinCandidate :
    DET.DiscreteEinsteinTensorCandidateSurface
  flatEinsteinCandidate =
    DET.flatOnlyDiscreteEinsteinTensorCandidateSurface

  FlatCarrier : Set
  FlatCarrier =
    DET.DiscreteEinsteinTensorCandidateSurface.Carrier flatEinsteinCandidate

  flatRiemannFromCurvature :
    FlatCarrier →
    FlatCarrier
  flatRiemannFromCurvature curvature = curvature

  flatRicciContraction :
    FlatCarrier →
    FlatCarrier
  flatRicciContraction riemann = riemann

  selectedLocalRiemannFromCurvature :
    SelectedMetric.GRSelectedFiniteRBase →
    NFScalar.GRFiniteRScalar →
    NFScalar.GRFiniteRScalar
  selectedLocalRiemannFromCurvature _ curvature = curvature

  selectedLocalRicci :
    SelectedMetric.GRSelectedFiniteRBase →
    NFScalar.GRFiniteRScalar →
    NFScalar.GRFiniteRScalar
  selectedLocalRicci _ riemann = riemann

  selectedLocalScalar :
    SelectedMetric.GRSelectedFiniteRBase →
    NFScalar.GRFiniteRScalar →
    NFScalar.GRFiniteRScalar
  selectedLocalScalar _ ricci = ricci

  selectedLocalEinstein :
    SelectedMetric.GRSelectedFiniteRBase →
    NFScalar.GRFiniteRScalar →
    NFScalar.GRFiniteRScalar →
    NFScalar.GRFiniteRScalar
  selectedLocalEinstein _ ricci _ = ricci

  selectedContractLocalRicciFibre :
    ((site : SelectedMetric.GRSelectedFiniteRBase) →
      NFScalar.GRFiniteRScalar) →
    NFScalar.GRFiniteRScalar
  selectedContractLocalRicciFibre localRicciFibre =
    localRicciFibre SelectedMetric.selectedBase0

record GRDiscreteRicciCandidateFromCurvature : Set₁ where
  field
    status :
      GRDiscreteRicciCandidateStatus

    expectedC1DiscreteConnectionCandidate :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    expectedC1IsCanonicalCRTDiagnostic :
      expectedC1DiscreteConnectionCandidate
      ≡
      DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    inheritedConnectionFirstMissing :
      DET.DiscreteEinsteinTensorFirstMissingCondition

    inheritedConnectionFirstMissingIsCRTConnection :
      inheritedConnectionFirstMissing
      ≡
      DET.missingCarrierInternalNonFlatConnectionFromCRT

    finiteRBianchiMissingIngredients :
      List GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    expectedDownstreamBianchiMissing :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    expectedDownstreamBianchiMissingIsFiniteRBianchiLaw :
      expectedDownstreamBianchiMissing
      ≡
      GRBianchi.missingFiniteRBianchiLaw

    CurvatureCarrier :
      Set

    RiemannCarrier :
      Set

    RicciCarrier :
      Set

    riemannFromCurvature :
      CurvatureCarrier →
      RiemannCarrier

    ricciContraction :
      RiemannCarrier →
      RicciCarrier

    LocalSite :
      Set

    LocalCurvatureFibre :
      LocalSite →
      Set

    LocalRiemannFibre :
      LocalSite →
      Set

    LocalRicciFibre :
      LocalSite →
      Set

    LocalScalarFibre :
      LocalSite →
      Set

    LocalEinsteinFibre :
      LocalSite →
      Set

    localRiemannFromCurvature :
      (site : LocalSite) →
      LocalCurvatureFibre site →
      LocalRiemannFibre site

    localRicci :
      (site : LocalSite) →
      LocalRiemannFibre site →
      LocalRicciFibre site

    localScalar :
      (site : LocalSite) →
      LocalRicciFibre site →
      LocalScalarFibre site

    localEinstein :
      (site : LocalSite) →
      LocalRicciFibre site →
      LocalScalarFibre site →
      LocalEinsteinFibre site

    ContractedRicciCarrier :
      Set

    contractLocalRicciFibre :
      ((site : LocalSite) → LocalRicciFibre site) →
      ContractedRicciCarrier

    localRicciContractionBoundaryOnly :
      Bool

    localRicciContractionBoundaryOnlyIsTrue :
      localRicciContractionBoundaryOnly
      ≡
      true

    localFibreDecompositionAvailable :
      Bool

    localFibreDecompositionAvailableIsTrue :
      localFibreDecompositionAvailable
      ≡
      true

    globalEagerRicciSweepRequired :
      Bool

    globalEagerRicciSweepRequiredIsFalse :
      globalEagerRicciSweepRequired
      ≡
      false

    fieldEquationStatus :
      GRDiscreteRicciFieldEquationStatus

    firstMissing :
      GRDiscreteRicciCandidateFirstMissing

    firstMissingIsBianchiIdentityProof :
      firstMissing
      ≡
      missingBianchiIdentityProof

    suppliedSurface :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List GRDiscreteRicciCandidateUnsupportedClaim

    unsupportedClaimsAreCanonical :
      unsupportedClaims
      ≡
      canonicalGRDiscreteRicciCandidateUnsupportedClaims

    nonPromotionBoundary :
      List String

canonicalGRDiscreteRicciCandidateFromCurvature :
  GRDiscreteRicciCandidateFromCurvature
canonicalGRDiscreteRicciCandidateFromCurvature =
  record
    { status =
        candidateShapeOnly
    ; expectedC1DiscreteConnectionCandidate =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; expectedC1IsCanonicalCRTDiagnostic =
        refl
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; inheritedConnectionFirstMissing =
        DCRT.DiscreteConnectionCandidateFromCRTDiagnostic.firstMissing
          DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; inheritedConnectionFirstMissingIsCRTConnection =
        refl
    ; finiteRBianchiMissingIngredients =
        GRBianchi.canonicalGRDiscreteBianchiFiniteRMissingIngredients
    ; expectedDownstreamBianchiMissing =
        GRBianchi.missingFiniteRBianchiLaw
    ; expectedDownstreamBianchiMissingIsFiniteRBianchiLaw =
        refl
    ; CurvatureCarrier =
        FlatCarrier
    ; RiemannCarrier =
        FlatCarrier
    ; RicciCarrier =
        FlatCarrier
    ; riemannFromCurvature =
        flatRiemannFromCurvature
    ; ricciContraction =
        flatRicciContraction
    ; LocalSite =
        SelectedMetric.GRSelectedFiniteRBase
    ; LocalCurvatureFibre =
        λ _ → NFScalar.GRFiniteRScalar
    ; LocalRiemannFibre =
        λ _ → NFScalar.GRFiniteRScalar
    ; LocalRicciFibre =
        λ _ → NFScalar.GRFiniteRScalar
    ; LocalScalarFibre =
        λ _ → NFScalar.GRFiniteRScalar
    ; LocalEinsteinFibre =
        λ _ → NFScalar.GRFiniteRScalar
    ; localRiemannFromCurvature =
        selectedLocalRiemannFromCurvature
    ; localRicci =
        selectedLocalRicci
    ; localScalar =
        selectedLocalScalar
    ; localEinstein =
        selectedLocalEinstein
    ; ContractedRicciCarrier =
        NFScalar.GRFiniteRScalar
    ; contractLocalRicciFibre =
        selectedContractLocalRicciFibre
    ; localRicciContractionBoundaryOnly =
        true
    ; localRicciContractionBoundaryOnlyIsTrue =
        refl
    ; localFibreDecompositionAvailable =
        true
    ; localFibreDecompositionAvailableIsTrue =
        refl
    ; globalEagerRicciSweepRequired =
        false
    ; globalEagerRicciSweepRequiredIsFalse =
        refl
    ; fieldEquationStatus =
        candidateShape
    ; firstMissing =
        missingBianchiIdentityProof
    ; firstMissingIsBianchiIdentityProof =
        refl
    ; suppliedSurface =
        "C1 DiscreteConnectionCandidateFromCRT diagnostic is present"
        ∷ "DiscreteEinsteinTensorCandidate supplies a flat carrier and tensor-shape fields"
        ∷ "GRDiscreteBianchiFiniteR supplies the finite-r Bianchi missing-ingredient index"
        ∷ "This C2 surface packages Riemann-from-curvature and Ricci-contraction interfaces"
        ∷ "This C2 surface exposes a lazy LocalSite-indexed curvature/Riemann/Ricci/scalar/Einstein fibre decomposition"
        ∷ "The contracted Ricci carrier is reached through contractLocalRicciFibre at the boundary, not by a monolithic global Ricci normal form"
        ∷ []
    ; missingSurface =
        "No promoted non-flat CRT/J connection is supplied by C1"
        ∷ "No finite-r Bianchi identity proof is supplied"
        ∷ "No theorem identifies the contraction with physical Ricci curvature"
        ∷ "No global eager Ricci sweep is required or promoted by the local-fibre candidate shape"
        ∷ "No global scalar contraction theorem is supplied before the local fibre family is explicitly observed"
        ∷ "No scalar trace, Einstein tensor law, source term, or continuum GR theorem is supplied"
        ∷ []
    ; unsupportedClaims =
        canonicalGRDiscreteRicciCandidateUnsupportedClaims
    ; unsupportedClaimsAreCanonical =
        refl
    ; nonPromotionBoundary =
        "This surface is a candidate-shape receipt, not a GR recovery theorem"
        ∷ "The first missing proof after the typed Ricci shape is missingBianchiIdentityProof"
        ∷ "The inherited C1 boundary remains diagnostic-only before a carrier-internal non-flat connection"
        ∷ "The localRicci/localScalar/localEinstein fibres and boundary contraction are typed staging sockets, not sourced Einstein evidence"
        ∷ "The finite-r Bianchi and Einstein-equation routes remain separate downstream obligations"
        ∷ []
    }

grDiscreteRicciCandidateStatusIsShapeOnly :
  GRDiscreteRicciCandidateFromCurvature.status
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  candidateShapeOnly
grDiscreteRicciCandidateStatusIsShapeOnly = refl

grDiscreteRicciCandidateConsumesC1 :
  GRDiscreteRicciCandidateFromCurvature.expectedC1DiscreteConnectionCandidate
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
grDiscreteRicciCandidateConsumesC1 = refl

grDiscreteRicciCandidateFirstMissing :
  GRDiscreteRicciCandidateFromCurvature.firstMissing
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  missingBianchiIdentityProof
grDiscreteRicciCandidateFirstMissing = refl

grDiscreteRicciCandidateFieldEquationStatus :
  GRDiscreteRicciCandidateFromCurvature.fieldEquationStatus
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  candidateShape
grDiscreteRicciCandidateFieldEquationStatus = refl

grDiscreteRicciCandidateLocalFibreDecompositionAvailable :
  GRDiscreteRicciCandidateFromCurvature.localFibreDecompositionAvailable
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  true
grDiscreteRicciCandidateLocalFibreDecompositionAvailable = refl

grDiscreteRicciCandidateNoGlobalEagerRicciSweep :
  GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  false
grDiscreteRicciCandidateNoGlobalEagerRicciSweep = refl

grDiscreteRicciCandidateAvoidsGlobalEagerSweep :
  GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  false
grDiscreteRicciCandidateAvoidsGlobalEagerSweep =
  grDiscreteRicciCandidateNoGlobalEagerRicciSweep

grDiscreteRicciCandidateContractionBoundaryOnly :
  GRDiscreteRicciCandidateFromCurvature.localRicciContractionBoundaryOnly
    canonicalGRDiscreteRicciCandidateFromCurvature
  ≡
  true
grDiscreteRicciCandidateContractionBoundaryOnly = refl

grDiscreteRicciCandidateContractLocalRicciFibre :
  ((site :
    GRDiscreteRicciCandidateFromCurvature.LocalSite
      canonicalGRDiscreteRicciCandidateFromCurvature) →
    GRDiscreteRicciCandidateFromCurvature.LocalRicciFibre
      canonicalGRDiscreteRicciCandidateFromCurvature site) →
  GRDiscreteRicciCandidateFromCurvature.ContractedRicciCarrier
    canonicalGRDiscreteRicciCandidateFromCurvature
grDiscreteRicciCandidateContractLocalRicciFibre =
  GRDiscreteRicciCandidateFromCurvature.contractLocalRicciFibre
    canonicalGRDiscreteRicciCandidateFromCurvature

grDiscreteRicciCandidateLocalRicci :
  (site :
    GRDiscreteRicciCandidateFromCurvature.LocalSite
      canonicalGRDiscreteRicciCandidateFromCurvature) →
  GRDiscreteRicciCandidateFromCurvature.LocalRiemannFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site →
  GRDiscreteRicciCandidateFromCurvature.LocalRicciFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site
grDiscreteRicciCandidateLocalRicci =
  GRDiscreteRicciCandidateFromCurvature.localRicci
    canonicalGRDiscreteRicciCandidateFromCurvature

grDiscreteRicciCandidateLocalScalar :
  (site :
    GRDiscreteRicciCandidateFromCurvature.LocalSite
      canonicalGRDiscreteRicciCandidateFromCurvature) →
  GRDiscreteRicciCandidateFromCurvature.LocalRicciFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site →
  GRDiscreteRicciCandidateFromCurvature.LocalScalarFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site
grDiscreteRicciCandidateLocalScalar =
  GRDiscreteRicciCandidateFromCurvature.localScalar
    canonicalGRDiscreteRicciCandidateFromCurvature

grDiscreteRicciCandidateLocalEinstein :
  (site :
    GRDiscreteRicciCandidateFromCurvature.LocalSite
      canonicalGRDiscreteRicciCandidateFromCurvature) →
  GRDiscreteRicciCandidateFromCurvature.LocalRicciFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site →
  GRDiscreteRicciCandidateFromCurvature.LocalScalarFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site →
  GRDiscreteRicciCandidateFromCurvature.LocalEinsteinFibre
    canonicalGRDiscreteRicciCandidateFromCurvature site
grDiscreteRicciCandidateLocalEinstein =
  GRDiscreteRicciCandidateFromCurvature.localEinstein
    canonicalGRDiscreteRicciCandidateFromCurvature

------------------------------------------------------------------------
-- Gate 4 selected-chain Ricci handoff.
--
-- GRDiscreteBianchiFiniteR now carries a stronger local Gate 4 attempt
-- receipt than the generic C2 Ricci candidate above.  This handoff records
-- exactly what can be consumed honestly from that attempt: local four-chart
-- zero-table Ricci/scalar/Einstein staging is present, but selected non-flat
-- promotion still fails at metric compatibility and the sourced equation
-- remains W4 authority-boundary blocked.

data GRDiscreteRicciGate4SelectedChainStatus : Set where
  gate4SelectedChainRicciLocallyStagedFailClosed :
    GRDiscreteRicciGate4SelectedChainStatus

data GRDiscreteRicciGate4LocalFibreContractionStatus : Set where
  gate4LocalFibreContractionZeroTableNoPromotion :
    GRDiscreteRicciGate4LocalFibreContractionStatus

record GRDiscreteRicciGate4LocalFibreContractionReceipt : Setω where
  field
    status :
      GRDiscreteRicciGate4LocalFibreContractionStatus

    selectedRiemannComponent :
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRScalar

    selectedRiemannComponentIsCanonicalZeroTable :
      selectedRiemannComponent
      ≡
      NFScalar.grSelectedFiniteRCurvatureAction

    selectedRicciComponent :
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRScalar

    selectedRicciComponentIsCanonicalZeroTable :
      selectedRicciComponent
      ≡
      NFScalar.grSelectedFiniteRRicciComponent

    selectedRicciFromCurvatureContraction :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      selectedRicciComponent mu nu
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          selectedRiemannComponent rho mu rho nu)

    selectedScalarCurvatureComponent :
      NFScalar.GRFiniteRScalar

    selectedScalarCurvatureComponentIsCanonicalZeroTable :
      selectedScalarCurvatureComponent
      ≡
      NFScalar.grSelectedFiniteRScalarCurvatureComponent

    selectedScalarCurvatureFromRicciTrace :
      selectedScalarCurvatureComponent
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              rho
              rho)
            (selectedRicciComponent rho rho))

    selectedEinsteinTensorComponent :
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRCoordinateIndex →
      NFScalar.GRFiniteRScalar

    selectedEinsteinTensorComponentIsCanonicalZeroTable :
      selectedEinsteinTensorComponent
      ≡
      NFScalar.grSelectedFiniteREinsteinTensorComponent

    selectedEinsteinTensorFromRicciScalar :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      selectedEinsteinTensorComponent mu nu
      ≡
      NFScalar.grFiniteRScalarSub
        (selectedRicciComponent mu nu)
        (NFScalar.grFiniteRScalarMul
          NFScalar.r2
          (NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              mu
              nu)
            selectedScalarCurvatureComponent))

    selectedContractedBianchiDivergenceZero :
      (nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRContract
        (λ mu →
          selectedEinsteinTensorComponent mu nu)
      ≡
      NFScalar.r0

    factorVecSSPAllLaneZeroTableLaw :
      DET.FactorVecSSPAllLaneContractionEinsteinTensorLaw

    factorVecSSPAllLaneZeroTableLawIsCanonical :
      factorVecSSPAllLaneZeroTableLaw
      ≡
      DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw

    doubledChristoffelInputStaged :
      Bool

    doubledChristoffelInputStagedIsTrue :
      doubledChristoffelInputStaged
      ≡
      true

    localFourRFibreShapeStaged :
      Bool

    localFourRFibreShapeStagedIsTrue :
      localFourRFibreShapeStaged
      ≡
      true

    localRicciFibreShapeStaged :
      Bool

    localRicciFibreShapeStagedIsTrue :
      localRicciFibreShapeStaged
      ≡
      true

    localScalarFibreShapeStaged :
      Bool

    localScalarFibreShapeStagedIsTrue :
      localScalarFibreShapeStaged
      ≡
      true

    localTwoTimesEinsteinFibreShapeStaged :
      Bool

    localTwoTimesEinsteinFibreShapeStagedIsTrue :
      localTwoTimesEinsteinFibreShapeStaged
      ≡
      true

    selectedFiniteNonFlatLocalCompatibilityReceipt :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt

    selectedFiniteNonFlatMetricCompatibilityPromoted :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromoted
        selectedFiniteNonFlatLocalCompatibilityReceipt
      ≡
      true

    selectedFiniteNonFlatTorsionFreePromoted :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFreePromoted
        selectedFiniteNonFlatLocalCompatibilityReceipt
      ≡
      true

    localZeroTableFibreShapeStaged :
      Bool

    localZeroTableFibreShapeStagedIsTrue :
      localZeroTableFibreShapeStaged
      ≡
      true

    localZeroTableFibreProofConstructed :
      Bool

    localZeroTableFibreProofConstructedIsFalse :
      localZeroTableFibreProofConstructed
      ≡
      false

    localFibreContractionOnly :
      Bool

    localFibreContractionOnlyIsTrue :
      localFibreContractionOnly
      ≡
      true

    r1ConcreteSiteSplitCanInhabitMetricCompatibility :
      Bool

    r1ConcreteSiteSplitCanInhabitMetricCompatibilityIsFalse :
      r1ConcreteSiteSplitCanInhabitMetricCompatibility
      ≡
      false

    selectedMetricCompatibilityPromoted :
      Bool

    selectedMetricCompatibilityPromotedIsFalse :
      selectedMetricCompatibilityPromoted
      ≡
      false

    selectedLeviCivitaPromoted :
      Bool

    selectedLeviCivitaPromotedIsFalse :
      selectedLeviCivitaPromoted
      ≡
      false

    selectedRicciEinsteinTowerPromoted :
      Bool

    selectedRicciEinsteinTowerPromotedIsFalse :
      selectedRicciEinsteinTowerPromoted
      ≡
      false

    exactFirstSelectedNonFlatMetricBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility :
      exactFirstSelectedNonFlatMetricBlocker
      ≡
      GRBianchi.missingMetricCompatibility

    selectedMetricCompatibilityAfterDoubledInputPromoted :
      Bool

    selectedMetricCompatibilityAfterDoubledInputPromotedIsTrue :
      selectedMetricCompatibilityAfterDoubledInputPromoted
      ≡
      true

    exactPostCompatibilitySelectedConnectionBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactPostCompatibilitySelectedConnectionBlockerIsCarrierConnection :
      exactPostCompatibilitySelectedConnectionBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    selectedConnectionDependencyName :
      String

    fibreBoundary :
      List String

canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt :
  GRDiscreteRicciGate4LocalFibreContractionReceipt
canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt =
  record
    { status =
        gate4LocalFibreContractionZeroTableNoPromotion
    ; selectedRiemannComponent =
        NFScalar.grSelectedFiniteRCurvatureAction
    ; selectedRiemannComponentIsCanonicalZeroTable =
        refl
    ; selectedRicciComponent =
        NFScalar.grSelectedFiniteRRicciComponent
    ; selectedRicciComponentIsCanonicalZeroTable =
        refl
    ; selectedRicciFromCurvatureContraction =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.ricciFromCurvatureContraction
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; selectedScalarCurvatureComponent =
        NFScalar.grSelectedFiniteRScalarCurvatureComponent
    ; selectedScalarCurvatureComponentIsCanonicalZeroTable =
        refl
    ; selectedScalarCurvatureFromRicciTrace =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.scalarCurvatureFromRicciTrace
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; selectedEinsteinTensorComponent =
        NFScalar.grSelectedFiniteREinsteinTensorComponent
    ; selectedEinsteinTensorComponentIsCanonicalZeroTable =
        refl
    ; selectedEinsteinTensorFromRicciScalar =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.einsteinTensorFromRicciScalar
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; selectedContractedBianchiDivergenceZero =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.contractedBianchiDivergenceZero
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; factorVecSSPAllLaneZeroTableLaw =
        DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw
    ; factorVecSSPAllLaneZeroTableLawIsCanonical =
        refl
    ; doubledChristoffelInputStaged =
        true
    ; doubledChristoffelInputStagedIsTrue =
        refl
    ; localFourRFibreShapeStaged =
        true
    ; localFourRFibreShapeStagedIsTrue =
        refl
    ; localRicciFibreShapeStaged =
        true
    ; localRicciFibreShapeStagedIsTrue =
        refl
    ; localScalarFibreShapeStaged =
        true
    ; localScalarFibreShapeStagedIsTrue =
        refl
    ; localTwoTimesEinsteinFibreShapeStaged =
        true
    ; localTwoTimesEinsteinFibreShapeStagedIsTrue =
        refl
    ; selectedFiniteNonFlatLocalCompatibilityReceipt =
        SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; selectedFiniteNonFlatMetricCompatibilityPromoted =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromotedIsTrue
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; selectedFiniteNonFlatTorsionFreePromoted =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFreePromotedIsTrue
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; localZeroTableFibreShapeStaged =
        true
    ; localZeroTableFibreShapeStagedIsTrue =
        refl
    ; localZeroTableFibreProofConstructed =
        false
    ; localZeroTableFibreProofConstructedIsFalse =
        refl
    ; localFibreContractionOnly =
        true
    ; localFibreContractionOnlyIsTrue =
        refl
    ; r1ConcreteSiteSplitCanInhabitMetricCompatibility =
        false
    ; r1ConcreteSiteSplitCanInhabitMetricCompatibilityIsFalse =
        refl
    ; selectedMetricCompatibilityPromoted =
        false
    ; selectedMetricCompatibilityPromotedIsFalse =
        refl
    ; selectedLeviCivitaPromoted =
        false
    ; selectedLeviCivitaPromotedIsFalse =
        refl
    ; selectedRicciEinsteinTowerPromoted =
        false
    ; selectedRicciEinsteinTowerPromotedIsFalse =
        refl
    ; exactFirstSelectedNonFlatMetricBlocker =
        GRBianchi.missingMetricCompatibility
    ; exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility =
        refl
    ; selectedMetricCompatibilityAfterDoubledInputPromoted =
        true
    ; selectedMetricCompatibilityAfterDoubledInputPromotedIsTrue =
        refl
    ; exactPostCompatibilitySelectedConnectionBlocker =
        GRBianchi.missingCarrierConnectionIsLeviCivita
    ; exactPostCompatibilitySelectedConnectionBlockerIsCarrierConnection =
        refl
    ; selectedConnectionDependencyName =
        "SelectedMetric.missingSelectedCarrierConnectionIsLeviCivita for selectedCarrierConnection over selectedGRNonFlatMetricDependency"
    ; fibreBoundary =
        "The local fibre functions close over the canonical u4 doubled-Christoffel input and take SelectedMetric base/index arguments explicitly"
        ∷ "The selected finite non-flat local compatibility receipt supplies metric compatibility and torsion-free witnesses over the selected two-base table"
        ∷ "The 4R, Ricci, scalar, and 2G zero-table shape is staged, but pointwise zero proof construction is deferred"
        ∷ "The FactorVec/SSP all-15-lane Ricci/scalar/Einstein zero-table law is consumed as a canonical finite-contraction witness"
        ∷ "The r1 concrete site split audit is carried beside the fibre as the legacy compatibility-era blocker"
        ∷ "The newer doubled-input adapter promotes selected metric compatibility locally; the exact post-compatibility blocker is missingCarrierConnectionIsLeviCivita"
        ∷ "The fibre receipt keeps contraction site/base-local to avoid global eager normalization across the selected finite table"
        ∷ "No selected metric-compatibility proof, selected Levi-Civita proof, Ricci/Einstein tower promotion, sourced equation, or non-flat GR promotion is constructed"
        ∷ []
    }

grDiscreteRicciGate4AllLaneZeroTableLaw :
  DET.FactorVecSSPAllLaneContractionEinsteinTensorLaw
grDiscreteRicciGate4AllLaneZeroTableLaw =
  GRDiscreteRicciGate4LocalFibreContractionReceipt.factorVecSSPAllLaneZeroTableLaw
    canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt

grDiscreteRicciGate4AllLaneZeroTableLawIsCanonical :
  grDiscreteRicciGate4AllLaneZeroTableLaw
  ≡
  DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw
grDiscreteRicciGate4AllLaneZeroTableLawIsCanonical =
  GRDiscreteRicciGate4LocalFibreContractionReceipt.factorVecSSPAllLaneZeroTableLawIsCanonical
    canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt

------------------------------------------------------------------------
-- Finite zero-table Ricci/Einstein arithmetic carrier.
--
-- The local fibre receipt above records the Ricci/scalar/Einstein maps over
-- NFScalar's selected four-chart table.  GRDiscreteBianchiFiniteR also carries
-- the finite 4R/Ricci/scalar/2G case-split arithmetic over the selected
-- two-coordinate table.  This receipt ties those two checked carriers
-- together and records the exact first missing precision for the non-flat and
-- contracted-Bianchi routes.

data GRDiscreteRicciFiniteZeroTableArithmeticStatus : Set where
  grDiscreteRicciFiniteZeroTableArithmeticStagedNoPromotion :
    GRDiscreteRicciFiniteZeroTableArithmeticStatus

record GRDiscreteRicciFiniteZeroTableArithmeticReceipt : Setω where
  field
    status :
      GRDiscreteRicciFiniteZeroTableArithmeticStatus

    localFibreContractionReceipt :
      GRDiscreteRicciGate4LocalFibreContractionReceipt

    finiteArithmeticReceipt :
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt

    localRiemannIsCanonicalZeroTable :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRiemannComponent
        localFibreContractionReceipt
      ≡
      NFScalar.grSelectedFiniteRCurvatureAction

    localRicciIsCanonicalZeroTable :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
        localFibreContractionReceipt
      ≡
      NFScalar.grSelectedFiniteRRicciComponent

    localRicciFromCurvatureContraction :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
        localFibreContractionReceipt mu nu
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRiemannComponent
            localFibreContractionReceipt rho mu rho nu)

    localScalarFromRicciTrace :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedScalarCurvatureComponent
        localFibreContractionReceipt
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              rho
              rho)
            (GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
              localFibreContractionReceipt rho rho))

    localEinsteinFromRicciScalar :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
        localFibreContractionReceipt mu nu
      ≡
      NFScalar.grFiniteRScalarSub
        (GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
          localFibreContractionReceipt mu nu)
        (NFScalar.grFiniteRScalarMul
          NFScalar.r2
          (NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRMetricComponent
              NFScalar.selectedFourChartIdentityMetric
              mu
              nu)
            (GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedScalarCurvatureComponent
              localFibreContractionReceipt)))

    localContractedBianchiDivergenceZero :
      (nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRContract
        (λ mu →
          GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
            localFibreContractionReceipt mu nu)
      ≡
      NFScalar.r0

    finiteFourTimesRiemannZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (rho sigma mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.fourTimesRiemann
        finiteArithmeticReceipt base rho sigma mu nu
      ≡
      NFScalar.r0

    finiteRicciFromFourRZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
        finiteArithmeticReceipt base sigma nu
      ≡
      NFScalar.r0

    finiteScalarFromRicciTraceZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.scalarFromRicciTrace
        finiteArithmeticReceipt base
      ≡
      NFScalar.r0

    finiteTwoTimesEinsteinZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
        finiteArithmeticReceipt base mu nu
      ≡
      NFScalar.r0

    finiteArithmeticFirstBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    finiteArithmeticFirstBlockerIsMetricCompatibility :
      finiteArithmeticFirstBlocker
      ≡
      GRBianchi.missingMetricCompatibility

    contractedBianchiDependencyBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    contractedBianchiDependencyBlockerIsCarrierConnection :
      contractedBianchiDependencyBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    ricciEinsteinTowerPromoted :
      Bool

    ricciEinsteinTowerPromotedIsFalse :
      ricciEinsteinTowerPromoted
      ≡
      false

    contractedBianchiPromoted :
      Bool

    contractedBianchiPromotedIsFalse :
      contractedBianchiPromoted
      ≡
      false

    arithmeticBoundary :
      List String

canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt :
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt
canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt =
  record
    { status =
        grDiscreteRicciFiniteZeroTableArithmeticStagedNoPromotion
    ; localFibreContractionReceipt =
        canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; finiteArithmeticReceipt =
        GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; localRiemannIsCanonicalZeroTable =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRiemannComponentIsCanonicalZeroTable
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localRicciIsCanonicalZeroTable =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponentIsCanonicalZeroTable
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localRicciFromCurvatureContraction =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciFromCurvatureContraction
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localScalarFromRicciTrace =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedScalarCurvatureFromRicciTrace
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localEinsteinFromRicciScalar =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorFromRicciScalar
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localContractedBianchiDivergenceZero =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedContractedBianchiDivergenceZero
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; finiteFourTimesRiemannZero =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.fourTimesRiemannZero
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; finiteRicciFromFourRZero =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourRZero
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; finiteScalarFromRicciTraceZero =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.scalarFromRicciTraceZero
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; finiteTwoTimesEinsteinZero =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinsteinZero
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; finiteArithmeticFirstBlocker =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.exactFirstSelectedNonFlatBlocker
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; finiteArithmeticFirstBlockerIsMetricCompatibility =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.exactFirstSelectedNonFlatBlockerIsMetricCompatibility
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; contractedBianchiDependencyBlocker =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiDependencyBlockerIsCarrierConnection =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; ricciEinsteinTowerPromoted =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciEinsteinTowerPromoted
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; ricciEinsteinTowerPromotedIsFalse =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciEinsteinTowerPromotedIsFalse
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; contractedBianchiPromoted =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiPromotedIsFalse =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromotedIsFalse
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; arithmeticBoundary =
        "The Ricci-side carrier ties the selected four-chart local fibre zero table to the m3 finite 4R/Ricci/scalar/2G arithmetic receipt"
        ∷ "Riemann-to-Ricci, Ricci-to-scalar, scalar-to-Einstein, and contracted-Bianchi zero are consumed as definitional local zero-table equations"
        ∷ "The finite two-coordinate table also exports 4R, Ricci, scalar, and two-times-Einstein zero equations"
        ∷ "The exact first finite-arithmetic blocker remains missingMetricCompatibility"
        ∷ "The contracted-Bianchi route remains blocked at missingCarrierConnectionIsLeviCivita"
        ∷ "No non-flat Ricci theorem, sourced Einstein equation, or GR promotion is constructed"
        ∷ []
    }

grDiscreteRicciFiniteZeroTableTwoTimesEinsteinZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
    base
    mu
    nu
  ≡
  NFScalar.r0
grDiscreteRicciFiniteZeroTableTwoTimesEinsteinZero =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteTwoTimesEinsteinZero
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableFourTimesRiemannZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (rho sigma mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.fourTimesRiemann
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
    base
    rho
    sigma
    mu
    nu
  ≡
  NFScalar.r0
grDiscreteRicciFiniteZeroTableFourTimesRiemannZero =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteFourTimesRiemannZero
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableRicciZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
    base
    sigma
    nu
  ≡
  NFScalar.r0
grDiscreteRicciFiniteZeroTableRicciZero =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteRicciFromFourRZero
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableScalarZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.scalarFromRicciTrace
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
    base
  ≡
  NFScalar.r0
grDiscreteRicciFiniteZeroTableScalarZero =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteScalarFromRicciTraceZero
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableContractedBianchiZero :
  (nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grSelectedFiniteRContract
    (λ mu →
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
          canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
        mu
        nu)
  ≡
  NFScalar.r0
grDiscreteRicciFiniteZeroTableContractedBianchiZero =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localContractedBianchiDivergenceZero
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableFirstBlocker :
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticFirstBlocker
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
  ≡
  GRBianchi.missingMetricCompatibility
grDiscreteRicciFiniteZeroTableFirstBlocker =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticFirstBlockerIsMetricCompatibility
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

grDiscreteRicciFiniteZeroTableContractedBianchiBlocker :
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiDependencyBlocker
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grDiscreteRicciFiniteZeroTableContractedBianchiBlocker =
  GRDiscreteRicciFiniteZeroTableArithmeticReceipt.contractedBianchiDependencyBlockerIsCarrierConnection
    canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt

record GRDiscreteRicciGate4SelectedChainFailClosedReceipt : Setω where
  field
    status :
      GRDiscreteRicciGate4SelectedChainStatus

    ricciCandidate :
      GRDiscreteRicciCandidateFromCurvature

    ricciCandidateFirstMissing :
      GRDiscreteRicciCandidateFirstMissing

    ricciCandidateFirstMissingIsBianchiProof :
      ricciCandidateFirstMissing
      ≡
      missingBianchiIdentityProof

    gate4AttemptSurfaceStaged :
      Bool

    gate4AttemptSurfaceStagedIsTrue :
      gate4AttemptSurfaceStaged
      ≡
      true

    m3TwoTimesEinsteinZeroTableStaged :
      Bool

    m3TwoTimesEinsteinZeroTableStagedIsTrue :
      m3TwoTimesEinsteinZeroTableStaged
      ≡
      true

    localFibreContractionReceipt :
      GRDiscreteRicciGate4LocalFibreContractionReceipt

    sourcedEinsteinFailClosedHandoff :
      GRBianchi.GRGate4SourcedEinsteinFailClosedHandoffReceipt

    contractedBianchiAfterSelectedLeviCivitaDependency :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    localFibreContractionOnly :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.localFibreContractionOnly
        localFibreContractionReceipt
      ≡
      true

    localFibreMetricCompatibilityPromotedIsFalse :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedMetricCompatibilityPromoted
        localFibreContractionReceipt
      ≡
      false

    localFibreLeviCivitaPromotedIsFalse :
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedLeviCivitaPromoted
        localFibreContractionReceipt
      ≡
      false

    r1ConcreteSiteSplitCannotInhabitMetricCompatibility :
      Bool

    r1ConcreteSiteSplitCannotInhabitMetricCompatibilityIsFalse :
      r1ConcreteSiteSplitCannotInhabitMetricCompatibility
      ≡
      false

    l2GaugeInvarianceProofStillMissing :
      Bool

    l2GaugeInvarianceProofStillMissingIsFalse :
      l2GaugeInvarianceProofStillMissing
      ≡
      false

    sourcedEinsteinAttachmentBlocked :
      Bool

    sourcedEinsteinAttachmentBlockedIsFalse :
      sourcedEinsteinAttachmentBlocked
      ≡
      false

    m3ScalarBaseDerivationConnectionAdvanced :
      Bool

    m3ScalarBaseDerivationConnectionAdvancedIsTrue :
      m3ScalarBaseDerivationConnectionAdvanced
      ≡
      true

    u4ZeroTableGeometryAdvanced :
      Bool

    u4ZeroTableGeometryAdvancedIsTrue :
      u4ZeroTableGeometryAdvanced
      ≡
      true

    localRicciScalarEinsteinTensorStaged :
      Bool

    localRicciScalarEinsteinTensorStagedIsTrue :
      localRicciScalarEinsteinTensorStaged
      ≡
      true

    ricciCandidateLocalContractionBoundaryOnly :
      GRDiscreteRicciCandidateFromCurvature.localRicciContractionBoundaryOnly
        ricciCandidate
      ≡
      true

    ricciCandidateNoGlobalEagerSweep :
      GRDiscreteRicciCandidateFromCurvature.globalEagerRicciSweepRequired
        ricciCandidate
      ≡
      false

    exactFirstSelectedNonFlatMetricBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility :
      exactFirstSelectedNonFlatMetricBlocker
      ≡
      GRBianchi.missingMetricCompatibility

    exactPostCompatibilitySelectedConnectionBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactPostCompatibilitySelectedConnectionBlockerIsCarrierConnection :
      exactPostCompatibilitySelectedConnectionBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    contractedBianchiAfterSelectedLeviCivitaDependencyPromoted :
      Bool

    contractedBianchiAfterSelectedLeviCivitaDependencyPromotedIsFalse :
      contractedBianchiAfterSelectedLeviCivitaDependencyPromoted
      ≡
      false

    exactSelectedConnectionDependencyName :
      String

    flatCompatibilityProved :
      Bool

    flatCompatibilityProvedIsTrue :
      flatCompatibilityProved
      ≡
      true

    nonFlatCompatibilityPromoted :
      Bool

    nonFlatCompatibilityPromotedIsFalse :
      nonFlatCompatibilityPromoted
      ≡
      false

    exactPostLocalGeometryBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactPostLocalGeometryBlockerIsStressEnergyCompatibility :
      exactPostLocalGeometryBlocker
      ≡
      GRBianchi.missingStressEnergyCompatibilityForContractedBianchi

    exactW4AuthorityBlockerName :
      String

    selectedChainPromotedToNonFlatGR :
      Bool

    selectedChainPromotedToNonFlatGRIsFalse :
      selectedChainPromotedToNonFlatGR
      ≡
      false

    receiptBoundary :
      List String

canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt
canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt =
  record
    { status =
        gate4SelectedChainRicciLocallyStagedFailClosed
    ; ricciCandidate =
        canonicalGRDiscreteRicciCandidateFromCurvature
    ; ricciCandidateFirstMissing =
        GRDiscreteRicciCandidateFromCurvature.firstMissing
          canonicalGRDiscreteRicciCandidateFromCurvature
    ; ricciCandidateFirstMissingIsBianchiProof =
        refl
    ; gate4AttemptSurfaceStaged =
        true
    ; gate4AttemptSurfaceStagedIsTrue =
        refl
    ; m3TwoTimesEinsteinZeroTableStaged =
        true
    ; m3TwoTimesEinsteinZeroTableStagedIsTrue =
        refl
    ; localFibreContractionReceipt =
        canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; sourcedEinsteinFailClosedHandoff =
        GRBianchi.canonicalGRGate4SourcedEinsteinFailClosedHandoffReceipt
    ; contractedBianchiAfterSelectedLeviCivitaDependency =
        GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; localFibreContractionOnly =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.localFibreContractionOnlyIsTrue
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localFibreMetricCompatibilityPromotedIsFalse =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedMetricCompatibilityPromotedIsFalse
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; localFibreLeviCivitaPromotedIsFalse =
        GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedLeviCivitaPromotedIsFalse
          canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt
    ; r1ConcreteSiteSplitCannotInhabitMetricCompatibility =
        false
    ; r1ConcreteSiteSplitCannotInhabitMetricCompatibilityIsFalse =
        refl
    ; l2GaugeInvarianceProofStillMissing =
        false
    ; l2GaugeInvarianceProofStillMissingIsFalse =
        refl
    ; sourcedEinsteinAttachmentBlocked =
        false
    ; sourcedEinsteinAttachmentBlockedIsFalse =
        refl
    ; m3ScalarBaseDerivationConnectionAdvanced =
        true
    ; m3ScalarBaseDerivationConnectionAdvancedIsTrue =
        refl
    ; u4ZeroTableGeometryAdvanced =
        true
    ; u4ZeroTableGeometryAdvancedIsTrue =
        refl
    ; localRicciScalarEinsteinTensorStaged =
        true
    ; localRicciScalarEinsteinTensorStagedIsTrue =
        refl
    ; ricciCandidateLocalContractionBoundaryOnly =
        grDiscreteRicciCandidateContractionBoundaryOnly
    ; ricciCandidateNoGlobalEagerSweep =
        grDiscreteRicciCandidateNoGlobalEagerRicciSweep
    ; exactFirstSelectedNonFlatMetricBlocker =
        GRBianchi.missingMetricCompatibility
    ; exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility =
        refl
    ; exactPostCompatibilitySelectedConnectionBlocker =
        GRBianchi.missingCarrierConnectionIsLeviCivita
    ; exactPostCompatibilitySelectedConnectionBlockerIsCarrierConnection =
        refl
    ; contractedBianchiAfterSelectedLeviCivitaDependencyPromoted =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiAfterSelectedLeviCivitaDependencyPromotedIsFalse =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromotedIsFalse
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; exactSelectedConnectionDependencyName =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyName
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; flatCompatibilityProved =
        true
    ; flatCompatibilityProvedIsTrue =
        refl
    ; nonFlatCompatibilityPromoted =
        false
    ; nonFlatCompatibilityPromotedIsFalse =
        refl
    ; exactPostLocalGeometryBlocker =
        GRBianchi.missingStressEnergyCompatibilityForContractedBianchi
    ; exactPostLocalGeometryBlockerIsStressEnergyCompatibility =
        refl
    ; exactW4AuthorityBlockerName =
        "W4Stress.missingCandidate256CalibrationReceiptForMatterInterface"
    ; selectedChainPromotedToNonFlatGR =
        false
    ; selectedChainPromotedToNonFlatGRIsFalse =
        refl
    ; receiptBoundary =
        "This C2 Ricci handoff consumes the strongest Gate 4 local attempt receipt from GRDiscreteBianchiFiniteR"
        ∷ "The m3 scalar/base/derivation/connection chain and u4 zero-table Ricci/scalar/Einstein tower are locally staged"
        ∷ "The doubled-Christoffel 4R/Ricci/scalar/2G arithmetic receipt is threaded explicitly and remains non-promotional"
        ∷ "The site/base-local fibre contraction receipt exposes SelectedMetric-indexed 4R/Ricci/scalar/2G functions and delegates all zero proofs to GRDiscreteBianchiFiniteR"
        ∷ "The fibre receipt is the timeout mitigation: contraction is consumed through local functions, not by global eager normalization"
        ∷ "The r1 concrete site split audit is retained as legacy compatibility-era context; the doubled-input adapter now promotes selected metric compatibility locally"
        ∷ "The l2/u3 stress-energy gauge scope is consumed fail-closed: W4Stress.lorentzGaugeInvarianceProof is still uninhabited locally"
        ∷ "The selected non-flat metric chain is not promoted: after local selected metric compatibility, the exact selected-connection blocker is missingCarrierConnectionIsLeviCivita"
        ∷ "The contracted Bianchi after-selected-dependency receipt is consumed fail-closed and names the missing selectedCarrierConnection Levi-Civita dependency"
        ∷ "The typed u3 DASHI matter-Lagrangian local interface surface is carried only as a fail-closed matter-interface handoff"
        ∷ "The u3 stress-energy handoff is consumed fail-closed: sourced Einstein remains blocked by missingStressEnergyCompatibilityForContractedBianchi, missingValuationMatterReceiptInterface, and the W4 Candidate256 authority boundary"
        ∷ "No non-flat GR, Ricci-from-Bianchi theorem, vacuum Ricci-zero theorem, or sourced Einstein equation is claimed"
        ∷ []
    }

grDiscreteRicciGate4SelectedChainFirstMetricBlocker :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlocker
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  GRBianchi.missingMetricCompatibility
grDiscreteRicciGate4SelectedChainFirstMetricBlocker =
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactFirstSelectedNonFlatMetricBlockerIsMetricCompatibility
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt

grDiscreteRicciGate4SelectedChainPostCompatibilityConnectionBlocker :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostCompatibilitySelectedConnectionBlocker
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grDiscreteRicciGate4SelectedChainPostCompatibilityConnectionBlocker =
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostCompatibilitySelectedConnectionBlockerIsCarrierConnection
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt

grDiscreteRicciGate4ContractedBianchiAfterSelectedDependencyStillBlocked :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.contractedBianchiAfterSelectedLeviCivitaDependencyPromoted
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  false
grDiscreteRicciGate4ContractedBianchiAfterSelectedDependencyStillBlocked =
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.contractedBianchiAfterSelectedLeviCivitaDependencyPromotedIsFalse
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt

grDiscreteRicciGate4SelectedChainPostGeometryBlocker :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostLocalGeometryBlocker
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  GRBianchi.missingStressEnergyCompatibilityForContractedBianchi
grDiscreteRicciGate4SelectedChainPostGeometryBlocker =
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.exactPostLocalGeometryBlockerIsStressEnergyCompatibility
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt

grDiscreteRicciGate4SelectedChainNoNonFlatPromotion :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGR
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  false
grDiscreteRicciGate4SelectedChainNoNonFlatPromotion =
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.selectedChainPromotedToNonFlatGRIsFalse
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt

grDiscreteRicciGate4SourcedEinsteinAttachmentBlocked :
  GRDiscreteRicciGate4SelectedChainFailClosedReceipt.sourcedEinsteinAttachmentBlocked
    canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
  ≡
  false
grDiscreteRicciGate4SourcedEinsteinAttachmentBlocked =
  refl

------------------------------------------------------------------------
-- Downstream Gate 4 sourced Einstein equation surface.
--
-- This is an equation-target receipt, not a promotion.  It records the
-- requested twoTimesEinsteinTensor = kappa * T target with
-- kappa = 8 * (355/113) = 2840/113 on the local zero-table FactorVec
-- staging, then keeps the selected non-flat metric and W4 matter receipt
-- gates closed.

data GRGate4SourcedEinsteinEquationSurfaceStatus : Set where
  gate4SourcedEinsteinEquationTargetStagedFailClosed :
    GRGate4SourcedEinsteinEquationSurfaceStatus

record GRGate4SourcedEinsteinEquationSurface : Setω where
  field
    status :
      GRGate4SourcedEinsteinEquationSurfaceStatus

    selectedChainHandoff :
      GRDiscreteRicciGate4SelectedChainFailClosedReceipt

    sourcedEinsteinFailClosedHandoffAvailable :
      Bool

    sourcedEinsteinFailClosedHandoffAvailableIsTrue :
      sourcedEinsteinFailClosedHandoffAvailable
      ≡
      true

    localFactorVecSourceShapeStaged :
      Bool

    localFactorVecSourceShapeStagedIsTrue :
      localFactorVecSourceShapeStaged
      ≡
      true

    kappaEightPiApproxName :
      String

    zeroTableEquationTargetName :
      String

    contractedBianchiCompatibilityTarget :
      String

    stressConservationCompatibilityTarget :
      String

    selectedMetricBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    selectedMetricBlockerIsCarrierConnection :
      selectedMetricBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    selectedNonFlatLeviCivitaBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    selectedNonFlatLeviCivitaBlockerIsCarrierConnection :
      selectedNonFlatLeviCivitaBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    selectedNonFlatMetricSurfaceStaged :
      Bool

    selectedNonFlatMetricSurfaceStagedIsTrue :
      selectedNonFlatMetricSurfaceStaged
      ≡
      true

    selectedNonFlatMetricFirstMissing :
      SelectedMetric.GRSelectedNonFlatMetricFirstMissingLaw

    selectedNonFlatMetricFirstMissingIsChristoffel :
      selectedNonFlatMetricFirstMissing
      ≡
      SelectedMetric.missingSelectedChristoffelFromMetricLaw

    selectedNonFlatLeviCivitaAbsentMarker :
      SelectedMetric.GRSelectedNonFlatMetricFirstMissingLaw

    selectedNonFlatLeviCivitaAbsentMarkerIsCarrierConnection :
      selectedNonFlatLeviCivitaAbsentMarker
      ≡
      SelectedMetric.missingSelectedCarrierConnectionIsLeviCivita

    localMatterReceiptInterfaceBlockerName :
      String

    w4AuthorityBlockerName :
      String

    w4MatterStressEnergyReceiptConstructed :
      Bool

    w4MatterStressEnergyReceiptConstructedIsFalse :
      w4MatterStressEnergyReceiptConstructed
      ≡
      false

    authorityBackedStressEnergyConstructed :
      Bool

    authorityBackedStressEnergyConstructedIsFalse :
      authorityBackedStressEnergyConstructed
      ≡
      false

    selectedNonFlatEquationPromoted :
      Bool

    selectedNonFlatEquationPromotedIsFalse :
      selectedNonFlatEquationPromoted
      ≡
      false

    candidate256Promoted :
      Bool

    candidate256PromotedIsFalse :
      candidate256Promoted
      ≡
      false

    surfaceBoundary :
      List String

canonicalGRGate4SourcedEinsteinEquationSurface :
  GRGate4SourcedEinsteinEquationSurface
canonicalGRGate4SourcedEinsteinEquationSurface =
  record
    { status =
        gate4SourcedEinsteinEquationTargetStagedFailClosed
    ; selectedChainHandoff =
        canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt
    ; sourcedEinsteinFailClosedHandoffAvailable =
        true
    ; sourcedEinsteinFailClosedHandoffAvailableIsTrue =
        refl
    ; localFactorVecSourceShapeStaged =
        true
    ; localFactorVecSourceShapeStagedIsTrue =
        refl
    ; kappaEightPiApproxName =
        "factorVecGate4KappaEightPiApprox"
    ; zeroTableEquationTargetName =
        "factorVecGate4SourcedEinsteinZeroTableEquationTarget"
    ; contractedBianchiCompatibilityTarget =
        "contracted Bianchi divergence must match covariant conservation of the accepted W4 stress-energy tensor for the selected non-flat connection"
    ; stressConservationCompatibilityTarget =
        "stress conservation target: nabla_mu T_mu_nu = 0 for the same selected non-flat Levi-Civita connection used by twoTimesEinsteinTensor"
    ; selectedMetricBlocker =
        GRBianchi.missingCarrierConnectionIsLeviCivita
    ; selectedMetricBlockerIsCarrierConnection =
        refl
    ; selectedNonFlatLeviCivitaBlocker =
        GRBianchi.missingCarrierConnectionIsLeviCivita
    ; selectedNonFlatLeviCivitaBlockerIsCarrierConnection =
        refl
    ; selectedNonFlatMetricSurfaceStaged =
        true
    ; selectedNonFlatMetricSurfaceStagedIsTrue =
        refl
    ; selectedNonFlatMetricFirstMissing =
        SelectedMetric.GRSelectedNonFlatMetricInstanceSurface.firstMissingNonFlatLaw
          SelectedMetric.canonicalGRSelectedNonFlatMetricInstanceSurface
    ; selectedNonFlatMetricFirstMissingIsChristoffel =
        SelectedMetric.canonicalGRSelectedNonFlatMetricFirstMissing
    ; selectedNonFlatLeviCivitaAbsentMarker =
        SelectedMetric.missingSelectedCarrierConnectionIsLeviCivita
    ; selectedNonFlatLeviCivitaAbsentMarkerIsCarrierConnection =
        refl
    ; localMatterReceiptInterfaceBlockerName =
        "missingValuationMatterReceiptInterface"
    ; w4AuthorityBlockerName =
        "missingCandidate256CalibrationReceiptForMatterInterface"
    ; w4MatterStressEnergyReceiptConstructed =
        false
    ; w4MatterStressEnergyReceiptConstructedIsFalse =
        refl
    ; authorityBackedStressEnergyConstructed =
        false
    ; authorityBackedStressEnergyConstructedIsFalse =
        refl
    ; selectedNonFlatEquationPromoted =
        false
    ; selectedNonFlatEquationPromotedIsFalse =
        refl
    ; candidate256Promoted =
        false
    ; candidate256PromotedIsFalse =
        refl
    ; surfaceBoundary =
        "The equation target is named as twoTimesEinsteinTensor = kappa * T at the FactorVec zero-table boundary"
        ∷ "The Ricci candidate keeps only lightweight names for the FactorVec source laws to avoid global eager normalization in this module"
        ∷ "Contracted-Bianchi/stress-conservation compatibility is carried as a target for the same selected non-flat Levi-Civita connection, not as a promoted theorem"
        ∷ "The selected non-flat route has metric compatibility witnessed and remains fail-closed at missingCarrierConnectionIsLeviCivita"
        ∷ "The matter/source route remains fail-closed at missingValuationMatterReceiptInterface and missingCandidate256CalibrationReceiptForMatterInterface"
        ∷ "No W4MatterStressEnergyInterfaceReceipt, Candidate256 promotion, selected non-flat sourced Einstein equation, W4 promotion, or GR/QFT promotion is constructed"
        ∷ []
    }

grGate4SourcedEinsteinEquationKappa :
  GRGate4SourcedEinsteinEquationSurface.kappaEightPiApproxName
    canonicalGRGate4SourcedEinsteinEquationSurface
  ≡
  "factorVecGate4KappaEightPiApprox"
grGate4SourcedEinsteinEquationKappa =
  refl

grGate4SourcedEinsteinEquationMetricBlocker :
  GRGate4SourcedEinsteinEquationSurface.selectedMetricBlocker
    canonicalGRGate4SourcedEinsteinEquationSurface
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grGate4SourcedEinsteinEquationMetricBlocker =
  refl

grGate4SourcedEinsteinEquationLeviCivitaBlocker :
  GRGate4SourcedEinsteinEquationSurface.selectedNonFlatLeviCivitaBlocker
    canonicalGRGate4SourcedEinsteinEquationSurface
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grGate4SourcedEinsteinEquationLeviCivitaBlocker =
  refl

grGate4SourcedEinsteinEquationW4Blocker :
  GRGate4SourcedEinsteinEquationSurface.w4AuthorityBlockerName
    canonicalGRGate4SourcedEinsteinEquationSurface
  ≡
  "missingCandidate256CalibrationReceiptForMatterInterface"
grGate4SourcedEinsteinEquationW4Blocker =
  refl

grGate4SourcedEinsteinEquationNoPromotion :
  GRGate4SourcedEinsteinEquationSurface.selectedNonFlatEquationPromoted
    canonicalGRGate4SourcedEinsteinEquationSurface
  ≡
  false
grGate4SourcedEinsteinEquationNoPromotion =
  refl

------------------------------------------------------------------------
-- GR-chain handoff after the selected metric-compatibility receipt.
--
-- The older Ricci candidate records remain available for compatibility with
-- prior waves.  This receipt consumes the stronger finite witnesses now
-- exposed by GRDiscreteBianchiFiniteR: the selected metric-compatibility
-- adapter is inhabited, while the Levi-Civita carrier identification,
-- contracted Bianchi promotion, and sourced equation are still blocked.

data GRDiscreteRicciSelectedCompatibilityHandoffStatus : Set where
  grDiscreteRicciSelectedCompatibilityAdvancedNoSourcedPromotion :
    GRDiscreteRicciSelectedCompatibilityHandoffStatus

record GRDiscreteRicciSelectedCompatibilityHandoffReceipt : Setω where
  field
    status :
      GRDiscreteRicciSelectedCompatibilityHandoffStatus

    selectedMetricCompatibilityAdapter :
      GRBianchi.GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt

    selectedMetricCompatibilityPromoted :
      GRBianchi.GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt.selectedMetricCompatibilityPromoted
        selectedMetricCompatibilityAdapter
      ≡
      true

    contractedBianchiDependencyReceipt :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    selectedConnectionLeviCivitaDependencyAvailable :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailable
        contractedBianchiDependencyReceipt
      ≡
      false

    exactSelectedGeometryBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactSelectedGeometryBlockerIsCarrierConnectionLeviCivita :
      exactSelectedGeometryBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    localTwoTimesEinsteinZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
        (GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.localRicciEinsteinZeroTable
          contractedBianchiDependencyReceipt)
        base
        mu
        nu
      ≡
      NFScalar.r0

    contractedBianchiPromoted :
      Bool

    contractedBianchiPromotedIsFalse :
      contractedBianchiPromoted
      ≡
      false

    sourcedEinsteinEquationSurface :
      GRGate4SourcedEinsteinEquationSurface

    sourcedEinsteinPromoted :
      GRGate4SourcedEinsteinEquationSurface.selectedNonFlatEquationPromoted
        sourcedEinsteinEquationSurface
      ≡
      false

    w4MatterAuthorityPromoted :
      GRGate4SourcedEinsteinEquationSurface.authorityBackedStressEnergyConstructed
        sourcedEinsteinEquationSurface
      ≡
      false

    handoffBoundary :
      List String

canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt :
  GRDiscreteRicciSelectedCompatibilityHandoffReceipt
canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt =
  record
    { status =
        grDiscreteRicciSelectedCompatibilityAdvancedNoSourcedPromotion
    ; selectedMetricCompatibilityAdapter =
        GRBianchi.canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
    ; selectedMetricCompatibilityPromoted =
        GRBianchi.GRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt.selectedMetricCompatibilityPromotedIsTrue
          GRBianchi.canonicalGRM3SelectedMetricCompatibilityDoubledInputAdapterReceipt
    ; contractedBianchiDependencyReceipt =
        GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionLeviCivitaDependencyAvailable =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailableIsFalse
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; exactSelectedGeometryBlocker =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; exactSelectedGeometryBlockerIsCarrierConnectionLeviCivita =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; localTwoTimesEinsteinZero =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.localTwoTimesEinsteinZero
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiPromoted =
        false
    ; contractedBianchiPromotedIsFalse =
        refl
    ; sourcedEinsteinEquationSurface =
        canonicalGRGate4SourcedEinsteinEquationSurface
    ; sourcedEinsteinPromoted =
        GRGate4SourcedEinsteinEquationSurface.selectedNonFlatEquationPromotedIsFalse
          canonicalGRGate4SourcedEinsteinEquationSurface
    ; w4MatterAuthorityPromoted =
        GRGate4SourcedEinsteinEquationSurface.authorityBackedStressEnergyConstructedIsFalse
          canonicalGRGate4SourcedEinsteinEquationSurface
    ; handoffBoundary =
        "Selected metric compatibility is consumed from the finite doubled-Christoffel adapter"
        ∷ "The Ricci handoff now exposes missingCarrierConnectionIsLeviCivita as the exact selected geometry blocker"
        ∷ "The local two-times-Einstein table is available only as zero-table finite arithmetic"
        ∷ "Contracted Bianchi remains unpromoted until selectedCarrierConnection is packaged as the carrier Levi-Civita connection and cyclic-sum curvature semantics are inhabited"
        ∷ "Sourced Einstein and W4 stress-energy authority remain false"
        ∷ []
    }

grDiscreteRicciSelectedCompatibilityNextBlocker :
  GRDiscreteRicciSelectedCompatibilityHandoffReceipt.exactSelectedGeometryBlocker
    canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grDiscreteRicciSelectedCompatibilityNextBlocker =
  GRDiscreteRicciSelectedCompatibilityHandoffReceipt.exactSelectedGeometryBlockerIsCarrierConnectionLeviCivita
    canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt

grDiscreteRicciSelectedCompatibilityNoSourcedPromotion :
  GRDiscreteRicciSelectedCompatibilityHandoffReceipt.contractedBianchiPromoted
    canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt
  ≡
  false
grDiscreteRicciSelectedCompatibilityNoSourcedPromotion =
  refl

------------------------------------------------------------------------
-- Schwarzschild finite-carrier Levi-Civita witness lane.
--
-- The available Schwarzschild surface is the bounded rational-shell
-- weak-field adapter, not a full analytic Schwarzschild connection.  This
-- receipt therefore closes exactly the locally typed parts: rational shell
-- valuation/match data, selected metric compatibility, torsion-free zero
-- Christoffel, finite four-chart Christoffel formula, and the already typed
-- Ricci/Bianchi zero consumers.  It keeps the non-flat selected carrier
-- Levi-Civita identification fail-closed at the inspected Christoffel slot.

data GRSchwarzschildFiniteCarrierLeviCivitaStatus : Set where
  schwarzschildFiniteCarrierLocalWitnessFailClosed :
    GRSchwarzschildFiniteCarrierLeviCivitaStatus

data GRSchwarzschildFiniteRouteStage : Set where
  schwarzschildFiniteRouteStagedFromCheckedReceipts :
    GRSchwarzschildFiniteRouteStage

record GRSchwarzschildFiniteCarrierLeviCivitaReceipt : Setω where
  field
    status :
      GRSchwarzschildFiniteCarrierLeviCivitaStatus

    rationalWeakFieldAdapter :
      Schwarzschild.RationalShellWeakFieldMatchAdapter

    rationalShellCarrier :
      Set

    rationalShellCarrierIsCanonical :
      rationalShellCarrier
      ≡
      Schwarzschild.RationalRadialShell

    radialValuation :
      rationalShellCarrier →
      NFScalar.GRFiniteRScalar

    weakFieldPotential :
      rationalShellCarrier →
      NFScalar.GRFiniteRScalar

    weakFieldLapse :
      rationalShellCarrier →
      NFScalar.GRFiniteRScalar

    schwarzschildLinearLapse :
      rationalShellCarrier →
      NFScalar.GRFiniteRScalar

    weakFieldLapseMatchesSchwarzschildLinear :
      (shell : rationalShellCarrier) →
      weakFieldLapse shell
      ≡
      schwarzschildLinearLapse shell

    rationalSchwarzschildWitnessShape :
      GRSchwarzschildFiniteRouteStage

    rationalRs2R3AnalyticTableReceipt :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt

    rationalRs2R3CoordinateCarrierIsCanonical :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.coordinateCarrier
        rationalRs2R3AnalyticTableReceipt
      ≡
      Schwarzschild.SchwarzschildCoordinateIndex

    rationalRs2R3DoubledChristoffelIsCanonical :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
        rationalRs2R3AnalyticTableReceipt
      ≡
      Schwarzschild.schwarzschildTwoGammaAtRs2R3

    rationalRs2R3DoubledChristoffelLowerSymmetry :
      (upper lower₁ lower₂ : Schwarzschild.SchwarzschildCoordinateIndex) →
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
        rationalRs2R3AnalyticTableReceipt
        upper
        lower₁
        lower₂
      ≡
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffel
        rationalRs2R3AnalyticTableReceipt
        upper
        lower₂
        lower₁

    rationalRs2R3VacuumPromotionIsFalse :
      Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotion
        rationalRs2R3AnalyticTableReceipt
      ≡
      false

    firstSchwarzschildMissingAfterAdapter :
      Schwarzschild.SchwarzschildLimitFirstMissingPrimitive

    firstSchwarzschildMissingAfterAdapterIsMetricMatch :
      firstSchwarzschildMissingAfterAdapter
      ≡
      Schwarzschild.missingSchwarzschildMetricMatch

    selectedLocalCompatibilityReceipt :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt

    metricCompatibility :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedMetricCompatibilityObligation
        base
        lambda
        mu
        nu

    metricCompatibilityPromoted :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromoted
        selectedLocalCompatibilityReceipt
      ≡
      true

    metricCompatibilityRoute :
      GRSchwarzschildFiniteRouteStage

    metricCompatibilityRouteChecked :
      Bool

    metricCompatibilityRouteCheckedIsTrue :
      metricCompatibilityRouteChecked
      ≡
      true

    torsionFree :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (lambda mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedChristoffelSymbol
        (SelectedMetric.selectedCarrierConnection base)
        lambda
        mu
        nu
      ≡
      SelectedMetric.selectedChristoffelSymbol
        (SelectedMetric.selectedCarrierConnection base)
        lambda
        nu
        mu

    torsionFreePromoted :
      SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFreePromoted
        selectedLocalCompatibilityReceipt
      ≡
      true

    torsionFreeRoute :
      GRSchwarzschildFiniteRouteStage

    torsionFreeRouteChecked :
      Bool

    torsionFreeRouteCheckedIsTrue :
      torsionFreeRouteChecked
      ≡
      true

    finiteFourChartChristoffelFromMetric :
      (base : NFScalar.GRFiniteRChartPoint) →
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grFiniteRScalarMul
        NFScalar.r2
        (NFScalar.grSelectedFiniteRChristoffelSymbol
          (NFScalar.grSelectedFiniteRConnectionAt base)
          lambda
          mu
          nu)
      ≡
      NFScalar.grSelectedFiniteRContract
        (λ rho →
          NFScalar.grFiniteRScalarMul
            (NFScalar.grSelectedFiniteRInverseMetricComponent
              (NFScalar.grSelectedFiniteRMetricAt base)
              lambda
              rho)
            (NFScalar.grFiniteRScalarSub
              (NFScalar.grFiniteRScalarAdd
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  mu
                  nu
                  rho)
                (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                  (NFScalar.grSelectedFiniteRMetricAt base)
                  nu
                  mu
                  rho))
              (NFScalar.grSelectedFiniteRCoordinateDerivativeOfMetric
                (NFScalar.grSelectedFiniteRMetricAt base)
                rho
                mu
                nu)))

    inspectedSelectedChristoffelObligationShape :
      GRBianchi.selectedInspectedChristoffelFromMetricObligation
      ≡
      (NFScalar.r0 ≡ NFScalar.r1)

    finiteFourChartLeviCivitaRoute :
      GRSchwarzschildFiniteRouteStage

    finiteFourChartLeviCivitaRouteChecked :
      Bool

    finiteFourChartLeviCivitaRouteCheckedIsTrue :
      finiteFourChartLeviCivitaRouteChecked
      ≡
      true

    selectedCarrierConnectionIsLeviCivitaPromoted :
      Bool

    selectedCarrierConnectionIsLeviCivitaPromotedIsFalse :
      selectedCarrierConnectionIsLeviCivitaPromoted
      ≡
      false

    exactRemainingLeviCivitaBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    exactRemainingLeviCivitaBlockerIsCarrierConnection :
      exactRemainingLeviCivitaBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    selectedRicciFromCurvatureContraction :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedRicciComponent base mu nu
      ≡
      SelectedMetric.selectedFiniteContract
        (λ rho →
          SelectedMetric.selectedCurvatureComponent base rho mu rho nu)

    selectedContractedBianchiDivergenceZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (nu : SelectedMetric.GRSelectedCoordinateIndex) →
      SelectedMetric.selectedFiniteContract
        (λ mu →
          SelectedMetric.selectedEinsteinTensorComponent base mu nu)
      ≡
      NFScalar.r0

    finiteFourChartBianchiZero :
      (lambda mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRBianchiCyclicSum lambda mu nu
      ≡
      NFScalar.r0

    finiteTwoTimesEinsteinZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
        GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
        base
        mu
        nu
      ≡
      NFScalar.r0

    ricciBianchiZeroConsumersTypeable :
      Bool

    ricciBianchiZeroConsumersTypeableIsTrue :
      ricciBianchiZeroConsumersTypeable
      ≡
      true

    sourcedEinsteinPromoted :
      Bool

    sourcedEinsteinPromotedIsFalse :
      sourcedEinsteinPromoted
      ≡
      false

    receiptBoundary :
      List String

canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt :
  GRSchwarzschildFiniteCarrierLeviCivitaReceipt
canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt =
  record
    { status =
        schwarzschildFiniteCarrierLocalWitnessFailClosed
    ; rationalWeakFieldAdapter =
        Schwarzschild.canonicalRationalShellWeakFieldMatchAdapter
    ; rationalShellCarrier =
        Schwarzschild.RationalRadialShell
    ; rationalShellCarrierIsCanonical =
        refl
    ; radialValuation =
        Schwarzschild.rationalShellRadialValuation
    ; weakFieldPotential =
        Schwarzschild.rationalShellWeakFieldPotentialResidue
    ; weakFieldLapse =
        Schwarzschild.weakFieldLinearLapseResidue
    ; schwarzschildLinearLapse =
        Schwarzschild.schwarzschildLinearLapseResidue
    ; weakFieldLapseMatchesSchwarzschildLinear =
        Schwarzschild.rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse
    ; rationalSchwarzschildWitnessShape =
        schwarzschildFiniteRouteStagedFromCheckedReceipts
    ; rationalRs2R3AnalyticTableReceipt =
        Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; rationalRs2R3CoordinateCarrierIsCanonical =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.coordinateCarrierIsCanonical
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; rationalRs2R3DoubledChristoffelIsCanonical =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffelIsCanonical
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; rationalRs2R3DoubledChristoffelLowerSymmetry =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.doubledChristoffelLowerSymmetry
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; rationalRs2R3VacuumPromotionIsFalse =
        Schwarzschild.SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotionIsFalse
          Schwarzschild.canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; firstSchwarzschildMissingAfterAdapter =
        Schwarzschild.RationalShellWeakFieldMatchAdapter.firstMissingAfterAdapter
          Schwarzschild.canonicalRationalShellWeakFieldMatchAdapter
    ; firstSchwarzschildMissingAfterAdapterIsMetricMatch =
        Schwarzschild.rationalShellWeakFieldAdapterFirstMissingMetricMatch
    ; selectedLocalCompatibilityReceipt =
        SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; metricCompatibility =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibility
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; metricCompatibilityPromoted =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromotedIsTrue
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; metricCompatibilityRoute =
        schwarzschildFiniteRouteStagedFromCheckedReceipts
    ; metricCompatibilityRouteChecked =
        true
    ; metricCompatibilityRouteCheckedIsTrue =
        refl
    ; torsionFree =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFree
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; torsionFreePromoted =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFreePromotedIsTrue
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; torsionFreeRoute =
        schwarzschildFiniteRouteStagedFromCheckedReceipts
    ; torsionFreeRouteChecked =
        true
    ; torsionFreeRouteCheckedIsTrue =
        refl
    ; finiteFourChartChristoffelFromMetric =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.selectedLeviCivitaEquality
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; inspectedSelectedChristoffelObligationShape =
        GRBianchi.selectedInspectedChristoffelFromMetricShape
    ; finiteFourChartLeviCivitaRoute =
        schwarzschildFiniteRouteStagedFromCheckedReceipts
    ; finiteFourChartLeviCivitaRouteChecked =
        true
    ; finiteFourChartLeviCivitaRouteCheckedIsTrue =
        refl
    ; selectedCarrierConnectionIsLeviCivitaPromoted =
        false
    ; selectedCarrierConnectionIsLeviCivitaPromotedIsFalse =
        refl
    ; exactRemainingLeviCivitaBlocker =
        GRBianchi.missingCarrierConnectionIsLeviCivita
    ; exactRemainingLeviCivitaBlockerIsCarrierConnection =
        refl
    ; selectedRicciFromCurvatureContraction =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.ricciFromCurvatureContraction
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; selectedContractedBianchiDivergenceZero =
        SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.contractedBianchiDivergenceZero
          SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt
    ; finiteFourChartBianchiZero =
        NFScalar.GRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt.finiteRBianchiLaw
          NFScalar.canonicalGRSelectedFourChartLeviCivitaBianchiEinsteinStagingReceipt
    ; finiteTwoTimesEinsteinZero =
        GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinsteinZero
          GRBianchi.canonicalGRM3FourRTwoGEinsteinFiniteArithmeticReceipt
    ; ricciBianchiZeroConsumersTypeable =
        true
    ; ricciBianchiZeroConsumersTypeableIsTrue =
        refl
    ; sourcedEinsteinPromoted =
        false
    ; sourcedEinsteinPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The bounded rational Schwarzschild lane consumes RationalRadialShell weak-field data: radial valuation, finite mass residue, potential, and the linear lapse match"
        ∷ "The rational Schwarzschild witness shape also threads the checked r_s=2, r=3 signed-rational analytic table and its lower-index Christoffel symmetry"
        ∷ "Metric compatibility is wired to SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibility"
        ∷ "Torsion-free is wired to SelectedMetric.canonicalGRSelectedFiniteNonFlatLocalCompatibilityReceipt.torsionFree"
        ∷ "The only Christoffel formula that is fully inhabited here is the finite four-chart zero-table Levi-Civita equality"
        ∷ "The selected non-flat Christoffel obligation is narrowed to the inspected shape r0 = r1, so selectedCarrierConnectionIsLeviCivita remains false"
        ∷ "Ricci contraction, contracted-Bianchi zero, finite four-chart Bianchi zero, and two-times-Einstein zero are exported only from existing typed zero-table helpers"
        ∷ "No full analytic Schwarzschild metric match, Birkhoff proof, W4 source, sourced Einstein equation, or non-flat GR promotion is constructed"
        ∷ []
    }

grSchwarzschildFiniteCarrierMetricCompatibilityClosed :
  SelectedMetric.GRSelectedFiniteNonFlatLocalCompatibilityReceipt.metricCompatibilityPromoted
    (GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedLocalCompatibilityReceipt
      canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt)
  ≡
  true
grSchwarzschildFiniteCarrierMetricCompatibilityClosed =
  GRSchwarzschildFiniteCarrierLeviCivitaReceipt.metricCompatibilityPromoted
    canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt

grSchwarzschildFiniteCarrierLeviCivitaStillBlocked :
  GRSchwarzschildFiniteCarrierLeviCivitaReceipt.exactRemainingLeviCivitaBlocker
    canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grSchwarzschildFiniteCarrierLeviCivitaStillBlocked =
  refl

grSchwarzschildFiniteCarrierRicciBianchiConsumersType :
  GRSchwarzschildFiniteCarrierLeviCivitaReceipt.ricciBianchiZeroConsumersTypeable
    canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
  ≡
  true
grSchwarzschildFiniteCarrierRicciBianchiConsumersType =
  refl

------------------------------------------------------------------------
-- Downstream Ricci convergence readiness boundary.
--
-- This is the Ricci-side handoff row for the eventual
-- DiscreteToSmoothRicciConvergence.ricciConvergesC0 Tier 3 target.  It
-- exports the checked zero-table arithmetic as named inputs while keeping
-- convergence, contracted Bianchi, sourced Einstein, and GR promotion closed.

data GRDiscreteRicciDownstreamConvergenceReadinessStatus : Set where
  grDiscreteRicciDownstreamConvergenceInputsStagedNoPromotion :
    GRDiscreteRicciDownstreamConvergenceReadinessStatus

record GRDiscreteRicciDownstreamConvergenceReadinessReceipt : Setω where
  field
    status :
      GRDiscreteRicciDownstreamConvergenceReadinessStatus

    finiteZeroTableArithmeticReceipt :
      GRDiscreteRicciFiniteZeroTableArithmeticReceipt

    selectedCompatibilityHandoff :
      GRDiscreteRicciSelectedCompatibilityHandoffReceipt

    downstreamModuleName :
      String

    downstreamRicciConvergenceTargetName :
      String

    downstreamReadinessTheoremName :
      String

    downstreamModuleNameIsDiscreteToSmoothRicciConvergence :
      downstreamModuleName
      ≡
      "DiscreteToSmoothRicciConvergence"

    downstreamRicciConvergenceTargetNameIsRicciConvergesC0 :
      downstreamRicciConvergenceTargetName
      ≡
      "DiscreteToSmoothRicciConvergence.ricciConvergesC0"

    downstreamReadinessTheoremNameIsCanonicalReceipt :
      downstreamReadinessTheoremName
      ≡
      "canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt"

    finiteRicciZeroInput :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
          finiteZeroTableArithmeticReceipt)
        base
        sigma
        nu
      ≡
      NFScalar.r0

    finiteScalarZeroInput :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.scalarFromRicciTrace
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
          finiteZeroTableArithmeticReceipt)
        base
      ≡
      NFScalar.r0

    finiteEinsteinZeroInput :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
          finiteZeroTableArithmeticReceipt)
        base
        mu
        nu
      ≡
      NFScalar.r0

    localContractedBianchiZeroInput :
      (nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRContract
        (λ mu →
          GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
            (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
              finiteZeroTableArithmeticReceipt)
            mu
            nu)
      ≡
      NFScalar.r0

    zeroTableArithmeticReadyForTier3 :
      Bool

    zeroTableArithmeticReadyForTier3IsTrue :
      zeroTableArithmeticReadyForTier3
      ≡
      true

    ricciConvergesC0Promoted :
      Bool

    ricciConvergesC0PromotedIsFalse :
      ricciConvergesC0Promoted
      ≡
      false

    contractedBianchiPromoted :
      Bool

    contractedBianchiPromotedIsFalse :
      contractedBianchiPromoted
      ≡
      false

    sourcedEinsteinPromoted :
      Bool

    sourcedEinsteinPromotedIsFalse :
      sourcedEinsteinPromoted
      ≡
      false

    grPromotionClaimed :
      Bool

    grPromotionClaimedIsFalse :
      grPromotionClaimed
      ≡
      false

    firstDownstreamBlocker :
      GRBianchi.GRDiscreteBianchiFiniteRMissingIngredient

    firstDownstreamBlockerIsCarrierConnectionLeviCivita :
      firstDownstreamBlocker
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    readinessBoundary :
      List String

canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt
canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt =
  record
    { status =
        grDiscreteRicciDownstreamConvergenceInputsStagedNoPromotion
    ; finiteZeroTableArithmeticReceipt =
        canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
    ; selectedCompatibilityHandoff =
        canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt
    ; downstreamModuleName =
        "DiscreteToSmoothRicciConvergence"
    ; downstreamRicciConvergenceTargetName =
        "DiscreteToSmoothRicciConvergence.ricciConvergesC0"
    ; downstreamReadinessTheoremName =
        "canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt"
    ; downstreamModuleNameIsDiscreteToSmoothRicciConvergence =
        refl
    ; downstreamRicciConvergenceTargetNameIsRicciConvergesC0 =
        refl
    ; downstreamReadinessTheoremNameIsCanonicalReceipt =
        refl
    ; finiteRicciZeroInput =
        grDiscreteRicciFiniteZeroTableRicciZero
    ; finiteScalarZeroInput =
        grDiscreteRicciFiniteZeroTableScalarZero
    ; finiteEinsteinZeroInput =
        grDiscreteRicciFiniteZeroTableTwoTimesEinsteinZero
    ; localContractedBianchiZeroInput =
        grDiscreteRicciFiniteZeroTableContractedBianchiZero
    ; zeroTableArithmeticReadyForTier3 =
        true
    ; zeroTableArithmeticReadyForTier3IsTrue =
        refl
    ; ricciConvergesC0Promoted =
        false
    ; ricciConvergesC0PromotedIsFalse =
        refl
    ; contractedBianchiPromoted =
        false
    ; contractedBianchiPromotedIsFalse =
        refl
    ; sourcedEinsteinPromoted =
        false
    ; sourcedEinsteinPromotedIsFalse =
        refl
    ; grPromotionClaimed =
        false
    ; grPromotionClaimedIsFalse =
        refl
    ; firstDownstreamBlocker =
        GRDiscreteRicciSelectedCompatibilityHandoffReceipt.exactSelectedGeometryBlocker
          canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt
    ; firstDownstreamBlockerIsCarrierConnectionLeviCivita =
        GRDiscreteRicciSelectedCompatibilityHandoffReceipt.exactSelectedGeometryBlockerIsCarrierConnectionLeviCivita
          canonicalGRDiscreteRicciSelectedCompatibilityHandoffReceipt
    ; readinessBoundary =
        "Finite Ricci, scalar, and two-times-Einstein zero-table arithmetic is exposed as named downstream input"
        ∷ "The local contracted-Bianchi zero table is available only as selected finite zero-table arithmetic"
        ∷ "The intended Tier 3 consumer is named as DiscreteToSmoothRicciConvergence.ricciConvergesC0"
        ∷ "ricciConvergesC0 is not promoted here because the selected carrier connection is not proved to be Levi-Civita"
        ∷ "No full Bianchi theorem, sourced Einstein equation, smooth convergence theorem, or GR promotion is claimed"
        ∷ []
    }

grDiscreteRicciDownstreamModuleNameExact :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamModuleName
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  "DiscreteToSmoothRicciConvergence"
grDiscreteRicciDownstreamModuleNameExact =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamModuleNameIsDiscreteToSmoothRicciConvergence
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamRicciConvergenceTargetNameExact :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamRicciConvergenceTargetName
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  "DiscreteToSmoothRicciConvergence.ricciConvergesC0"
grDiscreteRicciDownstreamRicciConvergenceTargetNameExact =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamRicciConvergenceTargetNameIsRicciConvergesC0
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamReadinessTheoremNameExact :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamReadinessTheoremName
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  "canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt"
grDiscreteRicciDownstreamReadinessTheoremNameExact =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.downstreamReadinessTheoremNameIsCanonicalReceipt
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamFiniteRicciZeroInput :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      (GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteZeroTableArithmeticReceipt
        canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt))
    base
    sigma
    nu
  ≡
  NFScalar.r0
grDiscreteRicciDownstreamFiniteRicciZeroInput =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteRicciZeroInput
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamFiniteScalarZeroInput :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.scalarFromRicciTrace
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      (GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteZeroTableArithmeticReceipt
        canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt))
    base
  ≡
  NFScalar.r0
grDiscreteRicciDownstreamFiniteScalarZeroInput =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteScalarZeroInput
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamFiniteEinsteinZeroInput :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (mu nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.twoTimesEinstein
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      (GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteZeroTableArithmeticReceipt
        canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt))
    base
    mu
    nu
  ≡
  NFScalar.r0
grDiscreteRicciDownstreamFiniteEinsteinZeroInput =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteEinsteinZeroInput
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamLocalContractedBianchiZeroInput :
  (nu : NFScalar.GRFiniteRCoordinateIndex) →
  NFScalar.grSelectedFiniteRContract
    (λ mu →
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
          (GRDiscreteRicciDownstreamConvergenceReadinessReceipt.finiteZeroTableArithmeticReceipt
            canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt))
        mu
        nu)
  ≡
  NFScalar.r0
grDiscreteRicciDownstreamLocalContractedBianchiZeroInput =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.localContractedBianchiZeroInput
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamZeroTableReady :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.zeroTableArithmeticReadyForTier3
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  true
grDiscreteRicciDownstreamZeroTableReady =
  refl

grDiscreteRicciDownstreamRicciConvergesC0NotPromoted :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.ricciConvergesC0Promoted
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  false
grDiscreteRicciDownstreamRicciConvergesC0NotPromoted =
  refl

grDiscreteRicciDownstreamContractedBianchiNotPromoted :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.contractedBianchiPromoted
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  false
grDiscreteRicciDownstreamContractedBianchiNotPromoted =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.contractedBianchiPromotedIsFalse
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamSourcedEinsteinNotPromoted :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.sourcedEinsteinPromoted
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  false
grDiscreteRicciDownstreamSourcedEinsteinNotPromoted =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.sourcedEinsteinPromotedIsFalse
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamGRPromotionNotClaimed :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.grPromotionClaimed
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  false
grDiscreteRicciDownstreamGRPromotionNotClaimed =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.grPromotionClaimedIsFalse
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

grDiscreteRicciDownstreamFirstBlocker :
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.firstDownstreamBlocker
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt
  ≡
  GRBianchi.missingCarrierConnectionIsLeviCivita
grDiscreteRicciDownstreamFirstBlocker =
  GRDiscreteRicciDownstreamConvergenceReadinessReceipt.firstDownstreamBlockerIsCarrierConnectionLeviCivita
    canonicalGRDiscreteRicciDownstreamConvergenceReadinessReceipt

------------------------------------------------------------------------
-- Finite Schwarzschild Ricci/Bianchi perturbation receipt.
--
-- This is a local receipt surface for the supplied finite facts only.  It
-- records the full selected finite Ricci tensor zero tables, the exact
-- contracted-Bianchi dependency route, and the numeric Ricci perturbation
-- bound L_Ricci = 640.  It deliberately does not promote an external
-- continuum Schwarzschild theorem.

grDiscreteRicciPerturbationBoundLRicci : Nat
grDiscreteRicciPerturbationBoundLRicci =
  640

grSchwarzschildFiniteRicciTightNumerator112 : Nat
grSchwarzschildFiniteRicciTightNumerator112 =
  112

grSchwarzschildFiniteRicciTightDenominator3008 : Nat
grSchwarzschildFiniteRicciTightDenominator3008 =
  3008

grSchwarzschildFiniteRicciTightRadialPower27 : Nat
grSchwarzschildFiniteRicciTightRadialPower27 =
  27

record GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt : Set where
  field
    coarseLRicci :
      Nat

    coarseLRicciIs640 :
      coarseLRicci
      ≡
      640

    tightNumerator :
      Nat

    tightNumeratorIs112 :
      tightNumerator
      ≡
      112

    tightDenominator :
      Nat

    tightDenominatorIs3008 :
      tightDenominator
      ≡
      3008

    tightRadialPower :
      Nat

    tightRadialPowerIs27 :
      tightRadialPower
      ≡
      27

    tightBoundPromotedAsConvergence :
      Bool

    tightBoundPromotedAsConvergenceIsFalse :
      tightBoundPromotedAsConvergence
      ≡
      false

canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt :
  GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt
canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt =
  record
    { coarseLRicci =
        grDiscreteRicciPerturbationBoundLRicci
    ; coarseLRicciIs640 =
        refl
    ; tightNumerator =
        grSchwarzschildFiniteRicciTightNumerator112
    ; tightNumeratorIs112 =
        refl
    ; tightDenominator =
        grSchwarzschildFiniteRicciTightDenominator3008
    ; tightDenominatorIs3008 =
        refl
    ; tightRadialPower =
        grSchwarzschildFiniteRicciTightRadialPower27
    ; tightRadialPowerIs27 =
        refl
    ; tightBoundPromotedAsConvergence =
        false
    ; tightBoundPromotedAsConvergenceIsFalse =
        refl
    }

grDiscreteRicciFourChartFullRicciTensorZero :
  (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
  GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
      canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt)
    mu
    nu
  ≡
  NFScalar.r0
grDiscreteRicciFourChartFullRicciTensorZero _ _ =
  refl

data GRSchwarzschildFiniteRicciBianchiPerturbationStatus : Set where
  schwarzschildFiniteRicciBianchiPerturbationReceiptFailClosed :
    GRSchwarzschildFiniteRicciBianchiPerturbationStatus

record GRSchwarzschildFiniteRicciBianchiPerturbationReceipt : Setω where
  field
    status :
      GRSchwarzschildFiniteRicciBianchiPerturbationStatus

    schwarzschildCandidateReceipt :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt

    schwarzschildCandidateFullLimitPromoted :
      Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.fullSchwarzschildLimitPromoted
        schwarzschildCandidateReceipt
      ≡
      false

    leviCivitaFiniteCarrierReceipt :
      GRSchwarzschildFiniteCarrierLeviCivitaReceipt

    leviCivitaSelectedCarrierStillBlocked :
      GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedCarrierConnectionIsLeviCivitaPromoted
        leviCivitaFiniteCarrierReceipt
      ≡
      false

    rationalSchwarzschildWitnessRoute :
      GRSchwarzschildFiniteRouteStage

    torsionFreeRouteChecked :
      GRSchwarzschildFiniteCarrierLeviCivitaReceipt.torsionFreeRouteChecked
        leviCivitaFiniteCarrierReceipt
      ≡
      true

    metricCompatibilityRouteChecked :
      GRSchwarzschildFiniteCarrierLeviCivitaReceipt.metricCompatibilityRouteChecked
        leviCivitaFiniteCarrierReceipt
      ≡
      true

    finiteRicciArithmeticReceipt :
      GRDiscreteRicciFiniteZeroTableArithmeticReceipt

    ricciZeroRoute :
      GRSchwarzschildFiniteRouteStage

    ricciZeroRouteChecked :
      Bool

    ricciZeroRouteCheckedIsTrue :
      ricciZeroRouteChecked
      ≡
      true

    ricciZeroPromotedAsContinuumVacuum :
      Bool

    ricciZeroPromotedAsContinuumVacuumIsFalse :
      ricciZeroPromotedAsContinuumVacuum
      ≡
      false

    fourChartFullRicciTensorZero :
      (mu nu : NFScalar.GRFiniteRCoordinateIndex) →
      GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedRicciComponent
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
          finiteRicciArithmeticReceipt)
        mu
        nu
      ≡
      NFScalar.r0

    selectedFiniteFullRicciTensorZero :
      (base : SelectedMetric.GRSelectedFiniteRBase) →
      (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
      GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
        (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
          finiteRicciArithmeticReceipt)
        base
        sigma
        nu
      ≡
      NFScalar.r0

    contractedBianchiRoute :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    contractedBianchiRouteChecked :
      Bool

    contractedBianchiRouteCheckedIsTrue :
      contractedBianchiRouteChecked
      ≡
      true

    contractedBianchiRouteStatusIsCanonical :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.status
        contractedBianchiRoute
      ≡
      GRBianchi.grGate4ContractedBianchiBlockedAtSelectedConnectionLeviCivita

    contractedBianchiRoutePromoted :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
        contractedBianchiRoute
      ≡
      false

    contractedBianchiExactBlocker :
      GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
        contractedBianchiRoute
      ≡
      GRBianchi.missingCarrierConnectionIsLeviCivita

    localContractedBianchiDivergenceZero :
      (nu : NFScalar.GRFiniteRCoordinateIndex) →
      NFScalar.grSelectedFiniteRContract
        (λ mu →
          GRDiscreteRicciGate4LocalFibreContractionReceipt.selectedEinsteinTensorComponent
            (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.localFibreContractionReceipt
              finiteRicciArithmeticReceipt)
            mu
            nu)
      ≡
      NFScalar.r0

    lRicciPerturbationBound :
      Nat

    lRicciPerturbationBoundIs640 :
      lRicciPerturbationBound
      ≡
      640

    tightRicciPerturbationArithmeticReceipt :
      GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt

    tightRicciNumeratorIs112 :
      GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightNumerator
        tightRicciPerturbationArithmeticReceipt
      ≡
      112

    tightRicciDenominatorIs3008 :
      GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightDenominator
        tightRicciPerturbationArithmeticReceipt
      ≡
      3008

    tightRicciRadialPowerIs27 :
      GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightRadialPower
        tightRicciPerturbationArithmeticReceipt
      ≡
      27

    ricciPerturbationBoundPromotedAsConvergence :
      Bool

    ricciPerturbationBoundPromotedAsConvergenceIsFalse :
      ricciPerturbationBoundPromotedAsConvergence
      ≡
      false

    externalContinuumSchwarzschildAuthorityClaimed :
      Bool

    externalContinuumSchwarzschildAuthorityClaimedIsFalse :
      externalContinuumSchwarzschildAuthorityClaimed
      ≡
      false

    receiptBoundary :
      List String

canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt :
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt
canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt =
  record
    { status =
        schwarzschildFiniteRicciBianchiPerturbationReceiptFailClosed
    ; schwarzschildCandidateReceipt =
        Schwarzschild.canonicalSchwarzschildLimitCanonicalCandidateReceipt
    ; schwarzschildCandidateFullLimitPromoted =
        Schwarzschild.SchwarzschildLimitCanonicalCandidateReceipt.fullSchwarzschildLimitPromotedIsFalse
          Schwarzschild.canonicalSchwarzschildLimitCanonicalCandidateReceipt
    ; leviCivitaFiniteCarrierReceipt =
        canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; leviCivitaSelectedCarrierStillBlocked =
        GRSchwarzschildFiniteCarrierLeviCivitaReceipt.selectedCarrierConnectionIsLeviCivitaPromotedIsFalse
          canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; rationalSchwarzschildWitnessRoute =
        GRSchwarzschildFiniteCarrierLeviCivitaReceipt.rationalSchwarzschildWitnessShape
          canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; torsionFreeRouteChecked =
        GRSchwarzschildFiniteCarrierLeviCivitaReceipt.torsionFreeRouteCheckedIsTrue
          canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; metricCompatibilityRouteChecked =
        GRSchwarzschildFiniteCarrierLeviCivitaReceipt.metricCompatibilityRouteCheckedIsTrue
          canonicalGRSchwarzschildFiniteCarrierLeviCivitaReceipt
    ; finiteRicciArithmeticReceipt =
        canonicalGRDiscreteRicciFiniteZeroTableArithmeticReceipt
    ; ricciZeroRoute =
        schwarzschildFiniteRouteStagedFromCheckedReceipts
    ; ricciZeroRouteChecked =
        true
    ; ricciZeroRouteCheckedIsTrue =
        refl
    ; ricciZeroPromotedAsContinuumVacuum =
        false
    ; ricciZeroPromotedAsContinuumVacuumIsFalse =
        refl
    ; fourChartFullRicciTensorZero =
        grDiscreteRicciFourChartFullRicciTensorZero
    ; selectedFiniteFullRicciTensorZero =
        grDiscreteRicciFiniteZeroTableRicciZero
    ; contractedBianchiRoute =
        GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiRouteChecked =
        true
    ; contractedBianchiRouteCheckedIsTrue =
        refl
    ; contractedBianchiRouteStatusIsCanonical =
        refl
    ; contractedBianchiRoutePromoted =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromotedIsFalse
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; contractedBianchiExactBlocker =
        GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
          GRBianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; localContractedBianchiDivergenceZero =
        grDiscreteRicciFiniteZeroTableContractedBianchiZero
    ; lRicciPerturbationBound =
        grDiscreteRicciPerturbationBoundLRicci
    ; lRicciPerturbationBoundIs640 =
        refl
    ; tightRicciPerturbationArithmeticReceipt =
        canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt
    ; tightRicciNumeratorIs112 =
        GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightNumeratorIs112
          canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt
    ; tightRicciDenominatorIs3008 =
        GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightDenominatorIs3008
          canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt
    ; tightRicciRadialPowerIs27 =
        GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightRadialPowerIs27
          canonicalGRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt
    ; ricciPerturbationBoundPromotedAsConvergence =
        false
    ; ricciPerturbationBoundPromotedAsConvergenceIsFalse =
        refl
    ; externalContinuumSchwarzschildAuthorityClaimed =
        false
    ; externalContinuumSchwarzschildAuthorityClaimedIsFalse =
        refl
    ; receiptBoundary =
        "Full finite Ricci tensor zero is recorded only for the local four-chart zero table and the selected finite 4R-contraction table"
        ∷ "The Ricci-zero route is checked as finite zero-table arithmetic only and is not promoted to continuum Schwarzschild vacuum"
        ∷ "The contracted-Bianchi route is the canonical Gate4 fail-closed dependency receipt and remains blocked at missingCarrierConnectionIsLeviCivita"
        ∷ "L_Ricci is recorded as the exact local perturbation bound 640, not as a smooth Ricci convergence theorem"
        ∷ "A tighter arithmetic receipt records 112/3008 at radial-power denominator 27 without promoting convergence"
        ∷ "The Schwarzschild candidate remains the bounded rational-shell request/adapter surface; full external continuum Schwarzschild authority is false"
        ∷ []
    }

grSchwarzschildFiniteRicciFullTensorZero :
  (base : SelectedMetric.GRSelectedFiniteRBase) →
  (sigma nu : SelectedMetric.GRSelectedCoordinateIndex) →
  GRBianchi.GRM3FourRTwoGEinsteinFiniteArithmeticReceipt.ricciFromFourR
    (GRDiscreteRicciFiniteZeroTableArithmeticReceipt.finiteArithmeticReceipt
      (GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.finiteRicciArithmeticReceipt
        canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt))
    base
    sigma
    nu
  ≡
  NFScalar.r0
grSchwarzschildFiniteRicciFullTensorZero =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.selectedFiniteFullRicciTensorZero
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt

grSchwarzschildFiniteContractedBianchiRouteStillBlocked :
  GRBianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
    (GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoute
      canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
  ≡
  false
grSchwarzschildFiniteContractedBianchiRouteStillBlocked =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoutePromoted
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt

grSchwarzschildFiniteRicciPerturbationBoundIs640 :
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBound
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
  ≡
  640
grSchwarzschildFiniteRicciPerturbationBoundIs640 =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBoundIs640
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt

grSchwarzschildFiniteRicciTightNumeratorIs112 :
  GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightNumerator
    (GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
      canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
  ≡
  112
grSchwarzschildFiniteRicciTightNumeratorIs112 =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciNumeratorIs112
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt

grSchwarzschildFiniteRicciTightDenominatorIs3008 :
  GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightDenominator
    (GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
      canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
  ≡
  3008
grSchwarzschildFiniteRicciTightDenominatorIs3008 =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciDenominatorIs3008
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt

grSchwarzschildFiniteRicciTightRadialPowerIs27 :
  GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightRadialPower
    (GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
      canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
  ≡
  27
grSchwarzschildFiniteRicciTightRadialPowerIs27 =
  GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciRadialPowerIs27
    canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
