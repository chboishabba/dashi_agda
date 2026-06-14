module DASHI.Algebra.Quantum.QFTParitySurface where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

record Sigma {ℓ : Level} (A : Set ℓ) : Set ℓ where
  constructor sigma
  field
    witness :
      A

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

    _·_ :
      Scalar → Carrier → Carrier

    inner :
      Carrier → Carrier → Scalar

    norm :
      Carrier → Scalar

    CauchySeq :
      Set ℓ

    LimSeq :
      Set ℓ

    completeness :
      CauchySeq → Sigma LimSeq

    CauchySequence :
      Set ℓ

    isCauchy :
      CauchySequence → EvidenceState

    Lim :
      CauchySequence → Carrier

    cauchyAuthority :
      ParityAuthority

    cauchyAuthorityIsHilbertCompletion :
      cauchyAuthority ≡ constructiveHilbertCompletionAuthority

    limAuthority :
      ParityAuthority

    limAuthorityIsHilbertCompletion :
      limAuthority ≡ constructiveHilbertCompletionAuthority

    complete :
      EvidenceState

    completeClosed :
      evidenceClosed complete ≡ false

    cauchyComplete :
      EvidenceState

    cauchyCompleteClosed :
      evidenceClosed cauchyComplete ≡ false

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

    idLaw :
      EvidenceState

    idLawClosed :
      evidenceClosed idLaw ≡ false

    composeLaw :
      EvidenceState

    composeLawClosed :
      evidenceClosed composeLaw ≡ false

    adjointLaw :
      EvidenceState

    adjointLawClosed :
      evidenceClosed adjointLaw ≡ false

    operatorLawAuthority :
      ParityAuthority

    operatorLawAuthorityIsBoundedCalculus :
      operatorLawAuthority ≡ boundedOperatorCalculusAuthority

    bounded :
      Op → EvidenceState

    boundedClosed :
      ∀ A → evidenceClosed (bounded A) ≡ false

    boundedAuthority :
      ParityAuthority

    boundedAuthorityIsBoundedCalculus :
      boundedAuthority ≡ boundedOperatorCalculusAuthority

    selfAdjoint :
      Op → EvidenceState

    selfAdjointAuthority :
      ParityAuthority

    selfAdjointAuthorityIsSpectralTheorem :
      selfAdjointAuthority ≡ selfAdjointSpectralTheoremAuthority

    unitary :
      Op → EvidenceState

    unitaryAuthority :
      ParityAuthority

    unitaryAuthorityIsStoneTheorem :
      unitaryAuthority ≡ unitaryStoneTheoremAuthority

record OperatorSurface {ℓ : Level} (H : HilbertSurface ℓ) :
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

    isBounded :
      Op → EvidenceState

    isSelfAdj :
      Op → EvidenceState

    isUnitary :
      Op → EvidenceState

    adjointId :
      EvidenceState

    selfAdjEq :
      Op → EvidenceState

    unitPres :
      Op → EvidenceState

    isBoundedClosed :
      ∀ A → evidenceClosed (isBounded A) ≡ false

    isSelfAdjClosed :
      ∀ A → evidenceClosed (isSelfAdj A) ≡ false

    isUnitaryClosed :
      ∀ U → evidenceClosed (isUnitary U) ≡ false

    adjointIdClosed :
      evidenceClosed adjointId ≡ false

    selfAdjEqClosed :
      ∀ A → evidenceClosed (selfAdjEq A) ≡ false

    unitPresClosed :
      ∀ U → evidenceClosed (unitPres U) ≡ false

canonicalHilbertSurfaceFields : List String
canonicalHilbertSurfaceFields =
  "Carrier"
  ∷ "Scalar"
  ∷ "zero"
  ∷ "_+_"
  ∷ "_·_"
  ∷ "inner"
  ∷ "norm"
  ∷ "completeness : CauchySeq -> Sigma LimSeq"
  ∷ []

canonicalOperatorSurfaceFields : List String
canonicalOperatorSurfaceFields =
  "Op"
  ∷ "apply"
  ∷ "idOp"
  ∷ "compose"
  ∷ "adjoint"
  ∷ "isBounded"
  ∷ "isSelfAdj"
  ∷ "isUnitary"
  ∷ "adjointId"
  ∷ "selfAdjEq"
  ∷ "unitPres"
  ∷ []

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

    spectrumTheoremAuthority :
      ParityAuthority

    spectrumTheoremAuthorityIsSpectralTheorem :
      spectrumTheoremAuthority ≡ selfAdjointSpectralTheoremAuthority

    resolventTheoremAuthority :
      ParityAuthority

    resolventTheoremAuthorityIsSpectralTheorem :
      resolventTheoremAuthority ≡ selfAdjointSpectralTheoremAuthority

    spectralMeasureTheoremAuthority :
      ParityAuthority

    spectralMeasureTheoremAuthorityIsSpectralTheorem :
      spectralMeasureTheoremAuthority ≡ selfAdjointSpectralTheoremAuthority

    spectrumTheorem :
      EvidenceState

    spectrumTheoremClosed :
      evidenceClosed spectrumTheorem ≡ false

    resolventTheorem :
      EvidenceState

    resolventTheoremClosed :
      evidenceClosed resolventTheorem ≡ false

    spectralMeasureTheorem :
      EvidenceState

    spectralMeasureTheoremClosed :
      evidenceClosed spectralMeasureTheorem ≡ false

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

record CCRLawRow : Set where
  field
    lawName :
      String

    bracket :
      String

    scalarOpWitnessText :
      String

    stoneVonNeumannAuthoritySlot :
      String

    authoritySlotFilled :
      Bool

    authoritySlotFilledIsFalse :
      authoritySlotFilled ≡ false

record CARLawRow : Set where
  field
    lawName :
      String

    antibracket :
      String

    scalarOpWitnessText :
      String

    finiteCARCStarAlgebraAuthoritySlot :
      String

    authoritySlotFilled :
      Bool

    authoritySlotFilledIsFalse :
      authoritySlotFilled ≡ false

canonicalCCRLawRows : List CCRLawRow
canonicalCCRLawRows =
  record
    { lawName =
        "CCR canonical bracket law"
    ; bracket =
        "[q(f), p(g)] = i * omega(f,g) * 1"
    ; scalarOpWitnessText =
        "scalarOp witnesses scalar multiples of idOp; this is a surface row, not a promoted representation theorem"
    ; stoneVonNeumannAuthoritySlot =
        "Stone-von Neumann uniqueness theorem authority required"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ []

canonicalCARLawRows : List CARLawRow
canonicalCARLawRows =
  record
    { lawName =
        "CAR canonical antibracket law"
    ; antibracket =
        "{a(f), a*(g)} = inner(f,g) * 1"
    ; scalarOpWitnessText =
        "scalarOp witnesses scalar multiples of idOp; this is a surface row, not a promoted finite CAR theorem"
    ; finiteCARCStarAlgebraAuthoritySlot =
        "finite CAR C*-algebra authority required"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ []

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

record CCRSurface {ℓ : Level}
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

    scalarOp :
      Scalar → Op

    scalarOpWitnessText :
      String

    symplecticForm :
      Carrier → Carrier → Set ℓ

    ccrLawRows :
      List CCRLawRow

    ccrLawRowsCanonical :
      ccrLawRows ≡ canonicalCCRLawRows

    ccrRepresentationAuthority :
      ParityAuthority

    ccrRepresentationAuthorityIsCCR :
      ccrRepresentationAuthority ≡ ccrRepresentationTheoremAuthority

    ccrLaw :
      EvidenceState

    ccrLawClosed :
      evidenceClosed ccrLaw ≡ false

record CARSurface {ℓ : Level}
  (H : HilbertSurface ℓ)
  (B : BoundedOperatorSurface H) :
  Set (lsuc ℓ) where
  open HilbertSurface H
  open BoundedOperatorSurface B
  field
    one :
      Op

    antibracket :
      Op → Op → Op

    scalarOp :
      Scalar → Op

    scalarOpWitnessText :
      String

    carLawRows :
      List CARLawRow

    carLawRowsCanonical :
      carLawRows ≡ canonicalCARLawRows

    carRepresentationAuthority :
      ParityAuthority

    carRepresentationAuthorityIsCAR :
      carRepresentationAuthority ≡ carRepresentationTheoremAuthority

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

    finiteParticleSector :
      Nat → Set ℓ

    finiteFockCarrier :
      Set ℓ

    creation :
      Carrier → FockCarrier → FockCarrier

    annihilation :
      Carrier → FockCarrier → FockCarrier

    numberOperator :
      Op

    finiteFockConstructed :
      EvidenceState

    finiteFockConstructedClosed :
      evidenceClosed finiteFockConstructed ≡ false

    fockConstructionAuthority :
      ParityAuthority

    fockConstructionAuthorityIsFock :
      fockConstructionAuthority ≡ fockSpaceConstructionAuthority

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

    Domain :
      Set ℓ

    domainMembership :
      Domain → Op → EvidenceState

    Field :
      TestFunction → Op

    smearedFieldSymmetric :
      TestFunction → EvidenceState

    commonInvariantDomain :
      EvidenceState

    commonInvariantDomainClosed :
      evidenceClosed commonInvariantDomain ≡ false

    domainAuthority :
      ParityAuthority

    domainAuthorityIsOperatorValuedDistribution :
      domainAuthority ≡ operatorValuedDistributionDomainAuthority

    operatorValuedDistribution :
      EvidenceState

    operatorValuedDistributionClosed :
      evidenceClosed operatorValuedDistribution ≡ false

record WightmanAxiom : Set where
  field
    axiomName :
      String

    axiomText :
      String

    authoritySlotFilled :
      Bool

    authoritySlotFilledIsFalse :
      authoritySlotFilled ≡ false

canonicalWightmanAxioms : List WightmanAxiom
canonicalWightmanAxioms =
  record
    { axiomName =
        "W1"
    ; axiomText =
        "W1 tempered distributions"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "W2"
    ; axiomText =
        "W2 Poincare covariance"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "W3"
    ; axiomText =
        "W3 spectrum condition"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "W4"
    ; axiomText =
        "W4 vacuum cyclicity"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "W5"
    ; axiomText =
        "W5 local commutativity"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "W6"
    ; axiomText =
        "W6 operator-valued distributions"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ []

wightmanAxiomName : WightmanAxiom → String
wightmanAxiomName row =
  WightmanAxiom.axiomText row

record OSAxiom : Set where
  field
    axiomName :
      String

    axiomText :
      String

    authoritySlotFilled :
      Bool

    authoritySlotFilledIsFalse :
      authoritySlotFilled ≡ false

canonicalOSAxioms : List OSAxiom
canonicalOSAxioms =
  record
    { axiomName =
        "OS1"
    ; axiomText =
        "OS1 regularity"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "OS2"
    ; axiomText =
        "OS2 Euclidean covariance"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "OS3"
    ; axiomText =
        "OS3 reflection positivity"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "OS4"
    ; axiomText =
        "OS4 symmetry"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ record
    { axiomName =
        "OS5"
    ; axiomText =
        "OS5 cluster property"
    ; authoritySlotFilled =
        false
    ; authoritySlotFilledIsFalse =
        refl
    }
  ∷ []

osAxiomName : OSAxiom → String
osAxiomName row =
  OSAxiom.axiomText row

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
  ccrAlgebras :
    QFTParityItem
  carAlgebras :
    QFTParityItem
  fockSpace :
    QFTParityItem
  operatorValuedDistributionDomains :
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
  ∷ ccrAlgebras
  ∷ carAlgebras
  ∷ fockSpace
  ∷ operatorValuedDistributionDomains
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

    authorityCutsetReferences :
      List ParityAuthority

    authorityCutsetReferencesCanonical :
      authorityCutsetReferences ≡ canonicalAuthorityCutset

    hilbertSurfaceFieldRows :
      List String
    hilbertSurfaceFieldRowsCanonical :
      hilbertSurfaceFieldRows ≡ canonicalHilbertSurfaceFields

    operatorSurfaceFieldRows :
      List String
    operatorSurfaceFieldRowsCanonical :
      operatorSurfaceFieldRows ≡ canonicalOperatorSurfaceFields

    hilbertSurfaceDeclared :
      Bool
    hilbertSurfaceDeclaredIsTrue :
      hilbertSurfaceDeclared ≡ true

    boundedOperatorSurfaceDeclared :
      Bool
    boundedOperatorSurfaceDeclaredIsTrue :
      boundedOperatorSurfaceDeclared ≡ true

    operatorSurfaceDeclared :
      Bool
    operatorSurfaceDeclaredIsTrue :
      operatorSurfaceDeclared ≡ true

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

    ccrSurfaceDeclared :
      Bool
    ccrSurfaceDeclaredIsTrue :
      ccrSurfaceDeclared ≡ true

    canonicalCCRRows :
      List CCRLawRow
    canonicalCCRRowsAreCanonical :
      canonicalCCRRows ≡ canonicalCCRLawRows

    carSurfaceDeclared :
      Bool
    carSurfaceDeclaredIsTrue :
      carSurfaceDeclared ≡ true

    canonicalCARRows :
      List CARLawRow
    canonicalCARRowsAreCanonical :
      canonicalCARRows ≡ canonicalCARLawRows

    fockSurfaceDeclared :
      Bool
    fockSurfaceDeclaredIsTrue :
      fockSurfaceDeclared ≡ true

    fockFiniteConstructionSurfaceDeclared :
      Bool
    fockFiniteConstructionSurfaceDeclaredIsTrue :
      fockFiniteConstructionSurfaceDeclared ≡ true

    operatorValuedDistributionDomainSurfaceDeclared :
      Bool
    operatorValuedDistributionDomainSurfaceDeclaredIsTrue :
      operatorValuedDistributionDomainSurfaceDeclared ≡ true

    fieldOperatorSurfaceDeclared :
      Bool
    fieldOperatorSurfaceDeclaredIsTrue :
      fieldOperatorSurfaceDeclared ≡ true

    osWightmanSurfaceDeclared :
      Bool
    osWightmanSurfaceDeclaredIsTrue :
      osWightmanSurfaceDeclared ≡ true

    canonicalOSRows :
      List OSAxiom
    canonicalOSRowsAreOS1ToOS5 :
      canonicalOSRows ≡ canonicalOSAxioms

    canonicalWightmanRows :
      List WightmanAxiom
    canonicalWightmanRowsAreW1ToW6 :
      canonicalWightmanRows ≡ canonicalWightmanAxioms

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
    ; authorityCutsetReferences =
        canonicalAuthorityCutset
    ; authorityCutsetReferencesCanonical =
        refl
    ; hilbertSurfaceFieldRows =
        canonicalHilbertSurfaceFields
    ; hilbertSurfaceFieldRowsCanonical =
        refl
    ; operatorSurfaceFieldRows =
        canonicalOperatorSurfaceFields
    ; operatorSurfaceFieldRowsCanonical =
        refl
    ; hilbertSurfaceDeclared =
        true
    ; hilbertSurfaceDeclaredIsTrue =
        refl
    ; boundedOperatorSurfaceDeclared =
        true
    ; boundedOperatorSurfaceDeclaredIsTrue =
        refl
    ; operatorSurfaceDeclared =
        true
    ; operatorSurfaceDeclaredIsTrue =
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
    ; ccrSurfaceDeclared =
        true
    ; ccrSurfaceDeclaredIsTrue =
        refl
    ; canonicalCCRRows =
        canonicalCCRLawRows
    ; canonicalCCRRowsAreCanonical =
        refl
    ; carSurfaceDeclared =
        true
    ; carSurfaceDeclaredIsTrue =
        refl
    ; canonicalCARRows =
        canonicalCARLawRows
    ; canonicalCARRowsAreCanonical =
        refl
    ; fockSurfaceDeclared =
        true
    ; fockSurfaceDeclaredIsTrue =
        refl
    ; fockFiniteConstructionSurfaceDeclared =
        true
    ; fockFiniteConstructionSurfaceDeclaredIsTrue =
        refl
    ; operatorValuedDistributionDomainSurfaceDeclared =
        true
    ; operatorValuedDistributionDomainSurfaceDeclaredIsTrue =
        refl
    ; fieldOperatorSurfaceDeclared =
        true
    ; fieldOperatorSurfaceDeclaredIsTrue =
        refl
    ; osWightmanSurfaceDeclared =
        true
    ; osWightmanSurfaceDeclaredIsTrue =
        refl
    ; canonicalOSRows =
        canonicalOSAxioms
    ; canonicalOSRowsAreOS1ToOS5 =
        refl
    ; canonicalWightmanRows =
        canonicalWightmanAxioms
    ; canonicalWightmanRowsAreW1ToW6 =
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
