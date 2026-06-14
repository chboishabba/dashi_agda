module DASHI.Algebra.Quantum.QFTParitySurface where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

-- This module is a fail-closed parity surface: it records the shape of the
-- quantum-mechanics/QFT interface needed for PhysLean parity without claiming
-- the analytic theorems that are still external or unproved in this repository.

data EvidenceState : Set where
  implementedSurface :
    EvidenceState
  candidateInterface :
    EvidenceState
  externalAuthorityRequired :
    EvidenceState
  blockedByAnalyticGap :
    EvidenceState
  deliberatelyNotPromoted :
    EvidenceState

evidenceClosed : EvidenceState → Bool
evidenceClosed implementedSurface = true
evidenceClosed candidateInterface = false
evidenceClosed externalAuthorityRequired = false
evidenceClosed blockedByAnalyticGap = false
evidenceClosed deliberatelyNotPromoted = false

data ParityAuthority : Set where
  constructiveHilbertCompletionAuthority :
    ParityAuthority
  boundedOperatorCalculusAuthority :
    ParityAuthority
  selfAdjointSpectralTheoremAuthority :
    ParityAuthority
  unitaryStoneTheoremAuthority :
    ParityAuthority
  completedTensorProductAuthority :
    ParityAuthority
  ccrRepresentationTheoremAuthority :
    ParityAuthority
  carRepresentationTheoremAuthority :
    ParityAuthority
  fockSpaceConstructionAuthority :
    ParityAuthority
  operatorValuedDistributionDomainAuthority :
    ParityAuthority
  osterwalderSchraderReconstructionAuthority :
    ParityAuthority
  wightmanAxiomVerificationAuthority :
    ParityAuthority
  haagRuelleScatteringAuthority :
    ParityAuthority
  renormalizationGroupContinuumLimitAuthority :
    ParityAuthority

canonicalAuthorityCutset : List ParityAuthority
canonicalAuthorityCutset =
  constructiveHilbertCompletionAuthority
  ∷ boundedOperatorCalculusAuthority
  ∷ selfAdjointSpectralTheoremAuthority
  ∷ unitaryStoneTheoremAuthority
  ∷ completedTensorProductAuthority
  ∷ ccrRepresentationTheoremAuthority
  ∷ carRepresentationTheoremAuthority
  ∷ fockSpaceConstructionAuthority
  ∷ operatorValuedDistributionDomainAuthority
  ∷ osterwalderSchraderReconstructionAuthority
  ∷ wightmanAxiomVerificationAuthority
  ∷ haagRuelleScatteringAuthority
  ∷ renormalizationGroupContinuumLimitAuthority
  ∷ []

data PromotionToken : Set where

promotionImpossibleWithoutAuthority : PromotionToken → ⊥
promotionImpossibleWithoutAuthority ()

record HilbertSurface (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    Scalar :
      Set ℓ

    zero :
      Carrier

    _+_ :
      Carrier → Carrier → Carrier

    _∙_ :
      Scalar → Carrier → Carrier

    inner :
      Carrier → Carrier → Scalar

    norm :
      Carrier → Scalar

    complete :
      EvidenceState

    completeClosed :
      evidenceClosed complete ≡ false

record BoundedOperatorSurface {ℓ : Level} (H : HilbertSurface ℓ) :
  Set (lsuc ℓ) where
  open HilbertSurface H
  field
    Op :
      Set ℓ

    apply :
      Op → Carrier → Carrier

    idOp :
      Op

    compose :
      Op → Op → Op

    adjoint :
      Op → Op

    bounded :
      Op → EvidenceState

    boundedClosed :
      ∀ A → evidenceClosed (bounded A) ≡ false

    selfAdjoint :
      Op → EvidenceState

    unitary :
      Op → EvidenceState

record SpectrumSurface {ℓ : Level}
  (H : HilbertSurface ℓ)
  (B : BoundedOperatorSurface H) :
  Set (lsuc ℓ) where
  open HilbertSurface H
  open BoundedOperatorSurface B
  field
    Spectrum :
      Op → Set ℓ

    resolvent :
      Op → Set ℓ

    spectralMeasure :
      Op → Set ℓ

    spectralTheorem :
      EvidenceState

    spectralTheoremClosed :
      evidenceClosed spectralTheorem ≡ false

record TensorSurface {ℓ₁ ℓ₂ : Level}
  (H₁ : HilbertSurface ℓ₁)
  (H₂ : HilbertSurface ℓ₂) :
  Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    TensorCarrier :
      Set (ℓ₁ ⊔ ℓ₂)

    pureTensor :
      HilbertSurface.Carrier H₁ →
      HilbertSurface.Carrier H₂ →
      TensorCarrier

    tensorInner :
      TensorCarrier → TensorCarrier → Set (ℓ₁ ⊔ ℓ₂)

    completedTensorProduct :
      EvidenceState

    completedTensorProductClosed :
      evidenceClosed completedTensorProduct ≡ false

data CommutationFamily : Set where
  canonicalCommutationRelations :
    CommutationFamily
  canonicalAnticommutationRelations :
    CommutationFamily
  weylExponentiatedCCR :
    CommutationFamily
  cliffordCAR :
    CommutationFamily

record CCRCARSurface {ℓ : Level}
  (H : HilbertSurface ℓ)
  (B : BoundedOperatorSurface H) :
  Set (lsuc ℓ) where
  open HilbertSurface H
  open BoundedOperatorSurface B
  field
    one :
      Op

    bracket :
      Op → Op → Op

    antibracket :
      Op → Op → Op

    symplecticForm :
      Carrier → Carrier → Set ℓ

    ccrLaw :
      EvidenceState

    ccrLawClosed :
      evidenceClosed ccrLaw ≡ false

    carLaw :
      EvidenceState

    carLawClosed :
      evidenceClosed carLaw ≡ false

record FockSurface {ℓ : Level}
  (H : HilbertSurface ℓ)
  (B : BoundedOperatorSurface H) :
  Set (lsuc ℓ) where
  open HilbertSurface H
  open BoundedOperatorSurface B
  field
    FockCarrier :
      Set ℓ

    vacuum :
      FockCarrier

    creation :
      Carrier → FockCarrier → FockCarrier

    annihilation :
      Carrier → FockCarrier → FockCarrier

    numberOperator :
      Op

    fockConstructed :
      EvidenceState

    fockConstructedClosed :
      evidenceClosed fockConstructed ≡ false

record FieldOperatorSurface {ℓ : Level}
  (H : HilbertSurface ℓ)
  (B : BoundedOperatorSurface H) :
  Set (lsuc ℓ) where
  open BoundedOperatorSurface B
  field
    TestFunction :
      Set ℓ

    Field :
      TestFunction → Op

    smearedFieldSymmetric :
      TestFunction → EvidenceState

    commonInvariantDomain :
      EvidenceState

    operatorValuedDistribution :
      EvidenceState

    operatorValuedDistributionClosed :
      evidenceClosed operatorValuedDistribution ≡ false

data WightmanAxiom : Set where
  temperedDistributions :
    WightmanAxiom
  poincareCovariance :
    WightmanAxiom
  spectrumCondition :
    WightmanAxiom
  vacuumCyclicity :
    WightmanAxiom
  localCommutativity :
    WightmanAxiom

canonicalWightmanAxioms : List WightmanAxiom
canonicalWightmanAxioms =
  temperedDistributions
  ∷ poincareCovariance
  ∷ spectrumCondition
  ∷ vacuumCyclicity
  ∷ localCommutativity
  ∷ []

data OSAxiom : Set where
  osRegularity :
    OSAxiom
  osEuclideanCovariance :
    OSAxiom
  osReflectionPositivity :
    OSAxiom
  osSymmetry :
    OSAxiom
  osClusterProperty :
    OSAxiom

canonicalOSAxioms : List OSAxiom
canonicalOSAxioms =
  osRegularity
  ∷ osEuclideanCovariance
  ∷ osReflectionPositivity
  ∷ osSymmetry
  ∷ osClusterProperty
  ∷ []

record OSWightmanSurface : Set₁ where
  field
    schwingerFunctions :
      Set

    wightmanDistributions :
      Set

    osAxioms :
      List OSAxiom

    osAxiomsCanonical :
      osAxioms ≡ canonicalOSAxioms

    wightmanAxioms :
      List WightmanAxiom

    wightmanAxiomsCanonical :
      wightmanAxioms ≡ canonicalWightmanAxioms

    osVerified :
      EvidenceState

    osVerifiedClosed :
      evidenceClosed osVerified ≡ false

    wightmanVerified :
      EvidenceState

    wightmanVerifiedClosed :
      evidenceClosed wightmanVerified ≡ false

    reconstructionAuthority :
      EvidenceState

    reconstructionAuthorityClosed :
      evidenceClosed reconstructionAuthority ≡ false

record ScatteringSurface : Set₁ where
  field
    InState :
      Set

    OutState :
      Set

    SMatrix :
      Set

    asymptoticCompleteness :
      EvidenceState

    asymptoticCompletenessClosed :
      evidenceClosed asymptoticCompleteness ≡ false

    scatteringUnitary :
      EvidenceState

    scatteringUnitaryClosed :
      evidenceClosed scatteringUnitary ≡ false

record RenormalizationBoundarySurface : Set₁ where
  field
    CutoffScale :
      Set

    BareCoupling :
      Set

    RenormalizedCoupling :
      Set

    betaFunctionAvailable :
      EvidenceState

    continuumLimitConstructed :
      EvidenceState

    continuumLimitClosed :
      evidenceClosed continuumLimitConstructed ≡ false

    nonperturbativeControl :
      EvidenceState

    nonperturbativeControlClosed :
      evidenceClosed nonperturbativeControl ≡ false

data QFTParityItem : Set where
  hilbertSpaces :
    QFTParityItem
  boundedOperators :
    QFTParityItem
  selfAdjointOperators :
    QFTParityItem
  unitaryOperators :
    QFTParityItem
  spectra :
    QFTParityItem
  tensorProducts :
    QFTParityItem
  ccrCarAlgebras :
    QFTParityItem
  fockSpace :
    QFTParityItem
  fieldOperators :
    QFTParityItem
  wightmanAxioms :
    QFTParityItem
  osAxioms :
    QFTParityItem
  scatteringTheory :
    QFTParityItem
  renormalizationBoundaries :
    QFTParityItem

canonicalParityItems : List QFTParityItem
canonicalParityItems =
  hilbertSpaces
  ∷ boundedOperators
  ∷ selfAdjointOperators
  ∷ unitaryOperators
  ∷ spectra
  ∷ tensorProducts
  ∷ ccrCarAlgebras
  ∷ fockSpace
  ∷ fieldOperators
  ∷ wightmanAxioms
  ∷ osAxioms
  ∷ scatteringTheory
  ∷ renormalizationBoundaries
  ∷ []

qftParityStatement : String
qftParityStatement =
  "QFTParitySurface is a checked fail-closed interface for PhysLean-style quantum mechanics and QFT parity. It exposes Hilbert, bounded/self-adjoint/unitary operator, spectrum, tensor, CCR/CAR, Fock, field-operator, OS/Wightman, scattering, and renormalization-boundary surfaces, but records hard analytic promotion as false unless an external authority token is supplied."

record QFTParityReceipt : Set₁ where
  field
    statement :
      String

    statementIsCanonical :
      statement ≡ qftParityStatement

    parityItems :
      List QFTParityItem

    parityItemsCanonical :
      parityItems ≡ canonicalParityItems

    requiredAuthorities :
      List ParityAuthority

    requiredAuthoritiesCanonical :
      requiredAuthorities ≡ canonicalAuthorityCutset

    hilbertSurfaceDeclared :
      Bool
    hilbertSurfaceDeclaredIsTrue :
      hilbertSurfaceDeclared ≡ true

    boundedOperatorSurfaceDeclared :
      Bool
    boundedOperatorSurfaceDeclaredIsTrue :
      boundedOperatorSurfaceDeclared ≡ true

    selfAdjointSurfaceDeclared :
      Bool
    selfAdjointSurfaceDeclaredIsTrue :
      selfAdjointSurfaceDeclared ≡ true

    unitarySurfaceDeclared :
      Bool
    unitarySurfaceDeclaredIsTrue :
      unitarySurfaceDeclared ≡ true

    spectrumSurfaceDeclared :
      Bool
    spectrumSurfaceDeclaredIsTrue :
      spectrumSurfaceDeclared ≡ true

    tensorSurfaceDeclared :
      Bool
    tensorSurfaceDeclaredIsTrue :
      tensorSurfaceDeclared ≡ true

    ccrCarSurfaceDeclared :
      Bool
    ccrCarSurfaceDeclaredIsTrue :
      ccrCarSurfaceDeclared ≡ true

    fockSurfaceDeclared :
      Bool
    fockSurfaceDeclaredIsTrue :
      fockSurfaceDeclared ≡ true

    fieldOperatorSurfaceDeclared :
      Bool
    fieldOperatorSurfaceDeclaredIsTrue :
      fieldOperatorSurfaceDeclared ≡ true

    osWightmanSurfaceDeclared :
      Bool
    osWightmanSurfaceDeclaredIsTrue :
      osWightmanSurfaceDeclared ≡ true

    scatteringSurfaceDeclared :
      Bool
    scatteringSurfaceDeclaredIsTrue :
      scatteringSurfaceDeclared ≡ true

    renormalizationBoundaryDeclared :
      Bool
    renormalizationBoundaryDeclaredIsTrue :
      renormalizationBoundaryDeclared ≡ true

    constructiveHilbertCompletionPromoted :
      Bool
    constructiveHilbertCompletionPromotedIsFalse :
      constructiveHilbertCompletionPromoted ≡ false

    boundedOperatorCalculusPromoted :
      Bool
    boundedOperatorCalculusPromotedIsFalse :
      boundedOperatorCalculusPromoted ≡ false

    selfAdjointSpectralTheoremPromoted :
      Bool
    selfAdjointSpectralTheoremPromotedIsFalse :
      selfAdjointSpectralTheoremPromoted ≡ false

    unitaryStoneTheoremPromoted :
      Bool
    unitaryStoneTheoremPromotedIsFalse :
      unitaryStoneTheoremPromoted ≡ false

    completedTensorProductPromoted :
      Bool
    completedTensorProductPromotedIsFalse :
      completedTensorProductPromoted ≡ false

    ccrRepresentationPromoted :
      Bool
    ccrRepresentationPromotedIsFalse :
      ccrRepresentationPromoted ≡ false

    carRepresentationPromoted :
      Bool
    carRepresentationPromotedIsFalse :
      carRepresentationPromoted ≡ false

    fockConstructionPromoted :
      Bool
    fockConstructionPromotedIsFalse :
      fockConstructionPromoted ≡ false

    fieldOperatorDomainPromoted :
      Bool
    fieldOperatorDomainPromotedIsFalse :
      fieldOperatorDomainPromoted ≡ false

    osAxiomsPromoted :
      Bool
    osAxiomsPromotedIsFalse :
      osAxiomsPromoted ≡ false

    wightmanAxiomsPromoted :
      Bool
    wightmanAxiomsPromotedIsFalse :
      wightmanAxiomsPromoted ≡ false

    scatteringTheoryPromoted :
      Bool
    scatteringTheoryPromotedIsFalse :
      scatteringTheoryPromoted ≡ false

    renormalizationContinuumLimitPromoted :
      Bool
    renormalizationContinuumLimitPromotedIsFalse :
      renormalizationContinuumLimitPromoted ≡ false

    noPromotionWithoutAuthority :
      Bool
    noPromotionWithoutAuthorityIsTrue :
      noPromotionWithoutAuthority ≡ true

    promotedParityClaim :
      Bool
    promotedParityClaimIsFalse :
      promotedParityClaim ≡ false

canonicalQFTParityReceipt : QFTParityReceipt
canonicalQFTParityReceipt =
  record
    { statement =
        qftParityStatement
    ; statementIsCanonical =
        refl
    ; parityItems =
        canonicalParityItems
    ; parityItemsCanonical =
        refl
    ; requiredAuthorities =
        canonicalAuthorityCutset
    ; requiredAuthoritiesCanonical =
        refl
    ; hilbertSurfaceDeclared =
        true
    ; hilbertSurfaceDeclaredIsTrue =
        refl
    ; boundedOperatorSurfaceDeclared =
        true
    ; boundedOperatorSurfaceDeclaredIsTrue =
        refl
    ; selfAdjointSurfaceDeclared =
        true
    ; selfAdjointSurfaceDeclaredIsTrue =
        refl
    ; unitarySurfaceDeclared =
        true
    ; unitarySurfaceDeclaredIsTrue =
        refl
    ; spectrumSurfaceDeclared =
        true
    ; spectrumSurfaceDeclaredIsTrue =
        refl
    ; tensorSurfaceDeclared =
        true
    ; tensorSurfaceDeclaredIsTrue =
        refl
    ; ccrCarSurfaceDeclared =
        true
    ; ccrCarSurfaceDeclaredIsTrue =
        refl
    ; fockSurfaceDeclared =
        true
    ; fockSurfaceDeclaredIsTrue =
        refl
    ; fieldOperatorSurfaceDeclared =
        true
    ; fieldOperatorSurfaceDeclaredIsTrue =
        refl
    ; osWightmanSurfaceDeclared =
        true
    ; osWightmanSurfaceDeclaredIsTrue =
        refl
    ; scatteringSurfaceDeclared =
        true
    ; scatteringSurfaceDeclaredIsTrue =
        refl
    ; renormalizationBoundaryDeclared =
        true
    ; renormalizationBoundaryDeclaredIsTrue =
        refl
    ; constructiveHilbertCompletionPromoted =
        false
    ; constructiveHilbertCompletionPromotedIsFalse =
        refl
    ; boundedOperatorCalculusPromoted =
        false
    ; boundedOperatorCalculusPromotedIsFalse =
        refl
    ; selfAdjointSpectralTheoremPromoted =
        false
    ; selfAdjointSpectralTheoremPromotedIsFalse =
        refl
    ; unitaryStoneTheoremPromoted =
        false
    ; unitaryStoneTheoremPromotedIsFalse =
        refl
    ; completedTensorProductPromoted =
        false
    ; completedTensorProductPromotedIsFalse =
        refl
    ; ccrRepresentationPromoted =
        false
    ; ccrRepresentationPromotedIsFalse =
        refl
    ; carRepresentationPromoted =
        false
    ; carRepresentationPromotedIsFalse =
        refl
    ; fockConstructionPromoted =
        false
    ; fockConstructionPromotedIsFalse =
        refl
    ; fieldOperatorDomainPromoted =
        false
    ; fieldOperatorDomainPromotedIsFalse =
        refl
    ; osAxiomsPromoted =
        false
    ; osAxiomsPromotedIsFalse =
        refl
    ; wightmanAxiomsPromoted =
        false
    ; wightmanAxiomsPromotedIsFalse =
        refl
    ; scatteringTheoryPromoted =
        false
    ; scatteringTheoryPromotedIsFalse =
        refl
    ; renormalizationContinuumLimitPromoted =
        false
    ; renormalizationContinuumLimitPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        true
    ; noPromotionWithoutAuthorityIsTrue =
        refl
    ; promotedParityClaim =
        false
    ; promotedParityClaimIsFalse =
        refl
    }
