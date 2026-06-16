module DASHI.Culture.QiOperatorTheoryBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
import DASHI.Core.AuthorityNonPromotionCore as AuthorityCore
import DASHI.Core.CandidateFunctionalCore as FunctionalCore
import DASHI.Core.CandidateOnlyCore as CandidateCore
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.OperatorShapeNonAuthorityCore as OperatorShapeCore
open import DASHI.Interop.RoleGrammarCore as RoleCore

------------------------------------------------------------------------
-- Feng Shui / Qi operator-theory boundary.
--
-- This module records the fetched-thread mapping as a receipt surface:
-- operator theory supplies role grammar for Qi-field formalism only.
-- It does not promote mystical, clinical, environmental, legal, empirical,
-- spiritual, or scientific authority without separate validation.

data QiOperatorTheoryBoundaryStatus : Set where
  qiOperatorTheoryRoleGrammarOnlyNonPromoting :
    QiOperatorTheoryBoundaryStatus

data QiRoleCategory : Set where
  QiStateSpace :
    QiRoleCategory
  QiOperator :
    QiRoleCategory
  QiObservable :
    QiRoleCategory
  QiSpectrumTool :
    QiRoleCategory
  QiBoundaryGate :
    QiRoleCategory
  QiObstruction :
    QiRoleCategory
  QiAlgebra :
    QiRoleCategory
  QiProofObligation :
    QiRoleCategory
  QiDecomposition :
    QiRoleCategory
  HistoricalMetadata :
    QiRoleCategory

canonicalQiRoleCategories :
  List QiRoleCategory
canonicalQiRoleCategories =
  QiStateSpace
  ∷ QiOperator
  ∷ QiObservable
  ∷ QiSpectrumTool
  ∷ QiBoundaryGate
  ∷ QiObstruction
  ∷ QiAlgebra
  ∷ QiProofObligation
  ∷ QiDecomposition
  ∷ HistoricalMetadata
  ∷ []

qiRoleFormalRole :
  QiRoleCategory → RoleCore.FormalRole
qiRoleFormalRole QiStateSpace =
  RoleCore.carrierSpaceRole
qiRoleFormalRole QiOperator =
  RoleCore.operatorRole
qiRoleFormalRole QiObservable =
  RoleCore.observableRole
qiRoleFormalRole QiSpectrumTool =
  RoleCore.spectrumToolRole
qiRoleFormalRole QiBoundaryGate =
  RoleCore.boundaryGateRole
qiRoleFormalRole QiObstruction =
  RoleCore.obstructionRole
qiRoleFormalRole QiAlgebra =
  RoleCore.algebraRole
qiRoleFormalRole QiProofObligation =
  RoleCore.proofObligationRole
qiRoleFormalRole QiDecomposition =
  RoleCore.decompositionRole
qiRoleFormalRole HistoricalMetadata =
  RoleCore.evidenceRole

record QiRoleCoreAlignmentRow : Set where
  constructor qiRoleCoreAlignmentRow
  field
    qiRole :
      QiRoleCategory
    coreRole :
      RoleCore.FormalRole
    coreRoleComputes :
      qiRoleFormalRole qiRole ≡ coreRole
    roleDomain :
      RoleCore.DomainLabel
    roleDomainIsQi :
      roleDomain ≡ RoleCore.qiDomain
    coreAuthorityClass :
      RoleCore.AuthorityClass
    coreAuthorityClassIsCandidateOnly :
      coreAuthorityClass ≡ RoleCore.candidateOnlyClass
    coreExternalAuthority :
      Bool
    coreExternalAuthorityIsFalse :
      coreExternalAuthority ≡ false
    reading :
      String

open QiRoleCoreAlignmentRow public

qiRoleCoreAlignment :
  QiRoleCategory → String → QiRoleCoreAlignmentRow
qiRoleCoreAlignment role reading =
  qiRoleCoreAlignmentRow
    role
    (qiRoleFormalRole role)
    refl
    RoleCore.qiDomain
    refl
    RoleCore.candidateOnlyClass
    refl
    (RoleCore.authorityClassExternalAuthority RoleCore.candidateOnlyClass)
    refl
    reading

canonicalQiRoleCoreAlignmentRows :
  List QiRoleCoreAlignmentRow
canonicalQiRoleCoreAlignmentRows =
  qiRoleCoreAlignment QiStateSpace "Qi state-space role delegates to the shared CarrierSpace formal role."
  ∷ qiRoleCoreAlignment QiOperator "Qi operator role delegates to the shared Operator formal role."
  ∷ qiRoleCoreAlignment QiObservable "Qi observable role delegates to the shared Observable formal role."
  ∷ qiRoleCoreAlignment QiSpectrumTool "Qi spectrum-tool role delegates to the shared SpectrumTool formal role."
  ∷ qiRoleCoreAlignment QiBoundaryGate "Qi boundary-gate role delegates to the shared BoundaryGate formal role."
  ∷ qiRoleCoreAlignment QiObstruction "Qi obstruction role delegates to the shared Obstruction formal role."
  ∷ qiRoleCoreAlignment QiAlgebra "Qi algebra role delegates to the shared Algebra formal role."
  ∷ qiRoleCoreAlignment QiProofObligation "Qi proof-obligation role delegates to the shared ProofObligation formal role."
  ∷ qiRoleCoreAlignment QiDecomposition "Qi decomposition role delegates to the shared Decomposition formal role."
  ∷ qiRoleCoreAlignment HistoricalMetadata "Historical metadata delegates to the shared Evidence formal role as receipt evidence only."
  ∷ []

canonicalQiCoreRoleFamily :
  RoleCore.RoleFamily
canonicalQiCoreRoleFamily =
  RoleCore.roleFamilyFor RoleCore.qiDomain

canonicalQiCoreRoleFamilyDomainIsQi :
  RoleCore.familyDomain canonicalQiCoreRoleFamily ≡ RoleCore.qiDomain
canonicalQiCoreRoleFamilyDomainIsQi =
  refl

canonicalQiCoreRoleFamilyExternalAuthorityFalse :
  RoleCore.familyExternalAuthority canonicalQiCoreRoleFamily ≡ false
canonicalQiCoreRoleFamilyExternalAuthorityFalse =
  refl

data OperatorFamily : Set where
  boundedOperator :
    OperatorFamily
  unboundedOperator :
    OperatorFamily
  compactOperator :
    OperatorFamily
  positiveOperator :
    OperatorFamily
  selfAdjointOperator :
    OperatorFamily
  unitaryOperator :
    OperatorFamily
  contractionOperator :
    OperatorFamily
  dissipativeOperator :
    OperatorFamily
  VolterraOperator :
    OperatorFamily
  transferOperator :
    OperatorFamily
  multiplicationOperator :
    OperatorFamily
  LaplaceOperator :
    OperatorFamily
  FredholmOperator :
    OperatorFamily
  projectionOperator :
    OperatorFamily
  resolventOperator :
    OperatorFamily
  functionalCalculusOperator :
    OperatorFamily
  semigroupOperator :
    OperatorFamily
  generatorOperator :
    OperatorFamily
  integralOperator :
    OperatorFamily
  kernelOperator :
    OperatorFamily
  traceClassOperator :
    OperatorFamily
  spectralMeasureOperator :
    OperatorFamily
  ToeplitzOperator :
    OperatorFamily
  pseudodifferentialOperator :
    OperatorFamily
  boundaryTraceOperator :
    OperatorFamily

operatorFamilyQiRole : OperatorFamily → QiRoleCategory
operatorFamilyQiRole boundedOperator =
  QiOperator
operatorFamilyQiRole unboundedOperator =
  QiProofObligation
operatorFamilyQiRole compactOperator =
  QiDecomposition
operatorFamilyQiRole positiveOperator =
  QiObservable
operatorFamilyQiRole selfAdjointOperator =
  QiSpectrumTool
operatorFamilyQiRole unitaryOperator =
  QiBoundaryGate
operatorFamilyQiRole contractionOperator =
  QiBoundaryGate
operatorFamilyQiRole dissipativeOperator =
  QiObstruction
operatorFamilyQiRole VolterraOperator =
  QiOperator
operatorFamilyQiRole transferOperator =
  QiOperator
operatorFamilyQiRole multiplicationOperator =
  QiObservable
operatorFamilyQiRole LaplaceOperator =
  QiObstruction
operatorFamilyQiRole FredholmOperator =
  QiProofObligation
operatorFamilyQiRole projectionOperator =
  QiDecomposition
operatorFamilyQiRole resolventOperator =
  QiSpectrumTool
operatorFamilyQiRole functionalCalculusOperator =
  QiAlgebra
operatorFamilyQiRole semigroupOperator =
  QiOperator
operatorFamilyQiRole generatorOperator =
  QiProofObligation
operatorFamilyQiRole integralOperator =
  QiOperator
operatorFamilyQiRole kernelOperator =
  QiStateSpace
operatorFamilyQiRole traceClassOperator =
  QiObservable
operatorFamilyQiRole spectralMeasureOperator =
  QiSpectrumTool
operatorFamilyQiRole ToeplitzOperator =
  HistoricalMetadata
operatorFamilyQiRole pseudodifferentialOperator =
  QiAlgebra
operatorFamilyQiRole boundaryTraceOperator =
  QiBoundaryGate

record OperatorFamilyQiRoleRow : Set where
  constructor operatorFamilyQiRoleRow
  field
    family :
      OperatorFamily
    role :
      QiRoleCategory
    roleComputes :
      operatorFamilyQiRole family ≡ role
    reading :
      String

open OperatorFamilyQiRoleRow public

operatorFamilyQiRoleRowFor :
  (family : OperatorFamily) →
  String →
  OperatorFamilyQiRoleRow
operatorFamilyQiRoleRowFor family reading =
  operatorFamilyQiRoleRow
    family
    (operatorFamilyQiRole family)
    refl
    reading

boundedOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
boundedOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    boundedOperator
    "bounded operator: controlled Qi transformation role"

unboundedOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
unboundedOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    unboundedOperator
    "unbounded operator: domain and closure obligation role"

compactOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
compactOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    compactOperator
    "compact operator: finite-pattern approximation role"

positiveOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
positiveOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    positiveOperator
    "positive operator: monotone observable role"

selfAdjointOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
selfAdjointOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    selfAdjointOperator
    "self-adjoint operator: spectral reading role"

unitaryOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
unitaryOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    unitaryOperator
    "unitary operator: reversible boundary passage role"

contractionOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
contractionOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    contractionOperator
    "contraction operator: attenuating gate role"

dissipativeOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
dissipativeOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    dissipativeOperator
    "dissipative operator: leakage or obstruction role"

VolterraOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
VolterraOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    VolterraOperator
    "Volterra operator: memory-flow transformation role"

transferOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
transferOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    transferOperator
    "transfer operator: directed circulation role"

multiplicationOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
multiplicationOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    multiplicationOperator
    "multiplication operator: local weighting observable role"

LaplaceOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
LaplaceOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    LaplaceOperator
    "Laplace operator: diffusion or tension-obstruction role"

FredholmOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
FredholmOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    FredholmOperator
    "Fredholm operator: index and solvability obligation role"

projectionOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
projectionOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    projectionOperator
    "projection operator: sector decomposition role"

resolventOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
resolventOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    resolventOperator
    "resolvent operator: spectral probing role"

functionalCalculusOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
functionalCalculusOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    functionalCalculusOperator
    "functional calculus: algebraic transformation grammar role"

semigroupOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
semigroupOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    semigroupOperator
    "semigroup operator: time-indexed flow role"

generatorOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
generatorOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    generatorOperator
    "generator operator: infinitesimal domain obligation role"

integralOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
integralOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    integralOperator
    "integral operator: accumulated influence role"

kernelOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
kernelOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    kernelOperator
    "kernel operator: state-space relation carrier role"

traceClassOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
traceClassOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    traceClassOperator
    "trace-class operator: aggregate observable role"

spectralMeasureOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
spectralMeasureOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    spectralMeasureOperator
    "spectral measure: spectrum partitioning tool role"

ToeplitzOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
ToeplitzOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    ToeplitzOperator
    "Toeplitz operator: inherited analytic metadata role"

pseudodifferentialOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
pseudodifferentialOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    pseudodifferentialOperator
    "pseudodifferential operator: symbolic calculus role"

boundaryTraceOperatorQiRoleRow :
  OperatorFamilyQiRoleRow
boundaryTraceOperatorQiRoleRow =
  operatorFamilyQiRoleRowFor
    boundaryTraceOperator
    "boundary trace operator: threshold interface role"

canonicalOperatorFamilyQiRoleRows :
  List OperatorFamilyQiRoleRow
canonicalOperatorFamilyQiRoleRows =
  boundedOperatorQiRoleRow
  ∷ unboundedOperatorQiRoleRow
  ∷ compactOperatorQiRoleRow
  ∷ positiveOperatorQiRoleRow
  ∷ selfAdjointOperatorQiRoleRow
  ∷ unitaryOperatorQiRoleRow
  ∷ contractionOperatorQiRoleRow
  ∷ dissipativeOperatorQiRoleRow
  ∷ VolterraOperatorQiRoleRow
  ∷ transferOperatorQiRoleRow
  ∷ multiplicationOperatorQiRoleRow
  ∷ LaplaceOperatorQiRoleRow
  ∷ FredholmOperatorQiRoleRow
  ∷ projectionOperatorQiRoleRow
  ∷ resolventOperatorQiRoleRow
  ∷ functionalCalculusOperatorQiRoleRow
  ∷ semigroupOperatorQiRoleRow
  ∷ generatorOperatorQiRoleRow
  ∷ integralOperatorQiRoleRow
  ∷ kernelOperatorQiRoleRow
  ∷ traceClassOperatorQiRoleRow
  ∷ spectralMeasureOperatorQiRoleRow
  ∷ ToeplitzOperatorQiRoleRow
  ∷ pseudodifferentialOperatorQiRoleRow
  ∷ boundaryTraceOperatorQiRoleRow
  ∷ []

data QiSpectralTerm : Set where
  Sheng :
    QiSpectralTerm
  Sha :
    QiSpectralTerm
  Si :
    QiSpectralTerm

data QiSpectralInterpretation : Set where
  generativeBandRole :
    QiSpectralInterpretation
  obstructiveBandRole :
    QiSpectralInterpretation
  stagnantKernelRole :
    QiSpectralInterpretation

spectralTermInterpretation :
  QiSpectralTerm → QiSpectralInterpretation
spectralTermInterpretation Sheng =
  generativeBandRole
spectralTermInterpretation Sha =
  obstructiveBandRole
spectralTermInterpretation Si =
  stagnantKernelRole

record QiSpectralInterpretationRow : Set where
  constructor qiSpectralInterpretationRow
  field
    spectralTerm :
      QiSpectralTerm
    spectrumTool :
      OperatorFamily
    interpretation :
      QiSpectralInterpretation
    interpretationComputes :
      spectralTermInterpretation spectralTerm ≡ interpretation
    promotedToDiagnosis :
      Bool
    promotedToDiagnosisIsFalse :
      promotedToDiagnosis ≡ false
    reading :
      String

open QiSpectralInterpretationRow public

ShengSpectralInterpretationRow :
  QiSpectralInterpretationRow
ShengSpectralInterpretationRow =
  qiSpectralInterpretationRow
    Sheng
    selfAdjointOperator
    generativeBandRole
    refl
    false
    refl
    "Sheng: generative spectral band role, not a validated outcome claim"

ShaSpectralInterpretationRow :
  QiSpectralInterpretationRow
ShaSpectralInterpretationRow =
  qiSpectralInterpretationRow
    Sha
    resolventOperator
    obstructiveBandRole
    refl
    false
    refl
    "Sha: obstruction spectral band role, not a validated harm claim"

SiSpectralInterpretationRow :
  QiSpectralInterpretationRow
SiSpectralInterpretationRow =
  qiSpectralInterpretationRow
    Si
    projectionOperator
    stagnantKernelRole
    refl
    false
    refl
    "Si: stagnant kernel role, not a clinical or environmental claim"

canonicalQiSpectralInterpretationRows :
  List QiSpectralInterpretationRow
canonicalQiSpectralInterpretationRows =
  ShengSpectralInterpretationRow
  ∷ ShaSpectralInterpretationRow
  ∷ SiSpectralInterpretationRow
  ∷ []

data ReciprocityGateStatus : Set where
  sweetgrassReciprocityRequired :
    ReciprocityGateStatus

record SweetgrassReciprocityGate : Set where
  constructor sweetgrassReciprocityGate
  field
    status :
      ReciprocityGateStatus
    role :
      QiRoleCategory
    requiresConsent :
      Bool
    requiresAttribution :
      Bool
    requiresNonExtraction :
      Bool
    permitsAuthorityTransfer :
      Bool
    permitsAuthorityTransferIsFalse :
      permitsAuthorityTransfer ≡ false
    reading :
      String

open SweetgrassReciprocityGate public

canonicalSweetgrassReciprocityGate :
  SweetgrassReciprocityGate
canonicalSweetgrassReciprocityGate =
  sweetgrassReciprocityGate
    sweetgrassReciprocityRequired
    QiBoundaryGate
    true
    true
    true
    false
    refl
    "Sweetgrass reciprocity is a boundary gate for consent, attribution, and non-extraction; it transfers no authority."

record QiAuthorityBoundary : Set where
  constructor qiAuthorityBoundary
  field
    validationSupplied :
      Bool
    empiricalAuthority :
      Bool
    empiricalAuthorityIsFalseWithoutValidation :
      empiricalAuthority ≡ false
    spiritualAuthority :
      Bool
    spiritualAuthorityIsFalseWithoutValidation :
      spiritualAuthority ≡ false
    clinicalAuthority :
      Bool
    clinicalAuthorityIsFalseWithoutValidation :
      clinicalAuthority ≡ false
    environmentalAuthority :
      Bool
    environmentalAuthorityIsFalseWithoutValidation :
      environmentalAuthority ≡ false
    mysticalAuthority :
      Bool
    mysticalAuthorityIsFalseWithoutValidation :
      mysticalAuthority ≡ false
    legalAuthority :
      Bool
    legalAuthorityIsFalseWithoutValidation :
      legalAuthority ≡ false
    scientificAuthority :
      Bool
    scientificAuthorityIsFalseWithoutValidation :
      scientificAuthority ≡ false

open QiAuthorityBoundary public

data QiBlockedAuthorityKind : Set where
  empiricalAuthorityKind :
    QiBlockedAuthorityKind
  spiritualAuthorityKind :
    QiBlockedAuthorityKind
  clinicalAuthorityKind :
    QiBlockedAuthorityKind
  environmentalAuthorityKind :
    QiBlockedAuthorityKind
  mysticalAuthorityKind :
    QiBlockedAuthorityKind
  legalAuthorityKind :
    QiBlockedAuthorityKind
  scientificAuthorityKind :
    QiBlockedAuthorityKind

canonicalQiBlockedAuthorityKinds :
  List QiBlockedAuthorityKind
canonicalQiBlockedAuthorityKinds =
  empiricalAuthorityKind
  ∷ spiritualAuthorityKind
  ∷ clinicalAuthorityKind
  ∷ environmentalAuthorityKind
  ∷ mysticalAuthorityKind
  ∷ legalAuthorityKind
  ∷ scientificAuthorityKind
  ∷ []

authorityKindPromotedWithoutValidation :
  QiBlockedAuthorityKind → Bool
authorityKindPromotedWithoutValidation _ =
  false

record QiBlockedAuthorityKindRow : Set where
  constructor qiBlockedAuthorityKindRow
  field
    authorityKind :
      QiBlockedAuthorityKind
    validationSuppliedForKind :
      Bool
    validationSuppliedForKindIsFalse :
      validationSuppliedForKind ≡ false
    promoted :
      Bool
    promotedComputes :
      authorityKindPromotedWithoutValidation authorityKind ≡ promoted
    reading :
      String

open QiBlockedAuthorityKindRow public

blockedAuthorityKindRow :
  QiBlockedAuthorityKind →
  String →
  QiBlockedAuthorityKindRow
blockedAuthorityKindRow authorityKind reading =
  qiBlockedAuthorityKindRow
    authorityKind
    false
    refl
    (authorityKindPromotedWithoutValidation authorityKind)
    refl
    reading

canonicalQiBlockedAuthorityKindRows :
  List QiBlockedAuthorityKindRow
canonicalQiBlockedAuthorityKindRows =
  blockedAuthorityKindRow empiricalAuthorityKind "Empirical authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow spiritualAuthorityKind "Spiritual authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow clinicalAuthorityKind "Clinical authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow environmentalAuthorityKind "Environmental authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow mysticalAuthorityKind "Mystical authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow legalAuthorityKind "Legal authority is blocked without a validation receipt."
  ∷ blockedAuthorityKindRow scientificAuthorityKind "Scientific authority is blocked without a validation receipt."
  ∷ []

canonicalQiAuthorityBoundary :
  QiAuthorityBoundary
canonicalQiAuthorityBoundary =
  qiAuthorityBoundary
    false
    (authorityKindPromotedWithoutValidation empiricalAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation spiritualAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation clinicalAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation environmentalAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation mysticalAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation legalAuthorityKind)
    refl
    (authorityKindPromotedWithoutValidation scientificAuthorityKind)
    refl

validationNotSuppliedForCanonicalQiAuthorityBoundary :
  validationSupplied canonicalQiAuthorityBoundary ≡ false
validationNotSuppliedForCanonicalQiAuthorityBoundary =
  refl

empiricalAuthorityFalseWithoutValidation :
  empiricalAuthority canonicalQiAuthorityBoundary ≡ false
empiricalAuthorityFalseWithoutValidation =
  refl

spiritualAuthorityFalseWithoutValidation :
  spiritualAuthority canonicalQiAuthorityBoundary ≡ false
spiritualAuthorityFalseWithoutValidation =
  refl

clinicalAuthorityFalseWithoutValidation :
  clinicalAuthority canonicalQiAuthorityBoundary ≡ false
clinicalAuthorityFalseWithoutValidation =
  refl

environmentalAuthorityFalseWithoutValidation :
  environmentalAuthority canonicalQiAuthorityBoundary ≡ false
environmentalAuthorityFalseWithoutValidation =
  refl

data QiReceiptBoundaryRow : Set where
  rowOperatorTheoryRoleGrammarOnly :
    QiReceiptBoundaryRow
  rowQiRoleCategoriesEnumerated :
    QiReceiptBoundaryRow
  rowCoreRoleGrammarDelegated :
    QiReceiptBoundaryRow
  rowOperatorFamiliesMapped :
    QiReceiptBoundaryRow
  rowShengShaSiSpectralInterpretations :
    QiReceiptBoundaryRow
  rowSweetgrassReciprocityGate :
    QiReceiptBoundaryRow
  rowAuthorityBlockedWithoutValidation :
    QiReceiptBoundaryRow

canonicalQiReceiptBoundaryRows :
  List QiReceiptBoundaryRow
canonicalQiReceiptBoundaryRows =
  rowOperatorTheoryRoleGrammarOnly
  ∷ rowQiRoleCategoriesEnumerated
  ∷ rowCoreRoleGrammarDelegated
  ∷ rowOperatorFamiliesMapped
  ∷ rowShengShaSiSpectralInterpretations
  ∷ rowSweetgrassReciprocityGate
  ∷ rowAuthorityBlockedWithoutValidation
  ∷ []

record QiOperatorTheoryBoundaryReceipt : Set where
  field
    status :
      QiOperatorTheoryBoundaryStatus
    roleCategories :
      List QiRoleCategory
    roleCategoriesAreCanonical :
      roleCategories ≡ canonicalQiRoleCategories
    operatorRows :
      List OperatorFamilyQiRoleRow
    operatorRowsAreCanonical :
      operatorRows ≡ canonicalOperatorFamilyQiRoleRows
    coreRoleRows :
      List QiRoleCoreAlignmentRow
    coreRoleRowsAreCanonical :
      coreRoleRows ≡ canonicalQiRoleCoreAlignmentRows
    coreQiRoleFamily :
      RoleCore.RoleFamily
    coreQiRoleFamilyIsCanonical :
      coreQiRoleFamily ≡ canonicalQiCoreRoleFamily
    coreQiRoleFamilyExternalAuthorityIsFalse :
      RoleCore.familyExternalAuthority coreQiRoleFamily ≡ false
    spectralRows :
      List QiSpectralInterpretationRow
    spectralRowsAreCanonical :
      spectralRows ≡ canonicalQiSpectralInterpretationRows
    sweetgrassGate :
      SweetgrassReciprocityGate
    sweetgrassGateIsCanonical :
      sweetgrassGate ≡ canonicalSweetgrassReciprocityGate
    authorityBoundary :
      QiAuthorityBoundary
    authorityBoundaryIsCanonical :
      authorityBoundary ≡ canonicalQiAuthorityBoundary
    blockedAuthorityKinds :
      List QiBlockedAuthorityKind
    blockedAuthorityKindsAreCanonical :
      blockedAuthorityKinds ≡ canonicalQiBlockedAuthorityKinds
    blockedAuthorityKindRows :
      List QiBlockedAuthorityKindRow
    blockedAuthorityKindRowsAreCanonical :
      blockedAuthorityKindRows ≡ canonicalQiBlockedAuthorityKindRows
    receiptRows :
      List QiReceiptBoundaryRow
    receiptRowsAreCanonical :
      receiptRows ≡ canonicalQiReceiptBoundaryRows
    operatorTheoryProvidesRoleGrammarOnly :
      Bool
    operatorTheoryProvidesRoleGrammarOnlyIsTrue :
      operatorTheoryProvidesRoleGrammarOnly ≡ true
    promotesEmpiricalAuthority :
      Bool
    promotesEmpiricalAuthorityIsFalse :
      promotesEmpiricalAuthority ≡ false
    promotesSpiritualAuthority :
      Bool
    promotesSpiritualAuthorityIsFalse :
      promotesSpiritualAuthority ≡ false
    promotesMysticalAuthority :
      Bool
    promotesMysticalAuthorityIsFalse :
      promotesMysticalAuthority ≡ false
    promotesClinicalAuthority :
      Bool
    promotesClinicalAuthorityIsFalse :
      promotesClinicalAuthority ≡ false
    promotesEnvironmentalAuthority :
      Bool
    promotesEnvironmentalAuthorityIsFalse :
      promotesEnvironmentalAuthority ≡ false
    promotesLegalAuthority :
      Bool
    promotesLegalAuthorityIsFalse :
      promotesLegalAuthority ≡ false
    promotesScientificAuthority :
      Bool
    promotesScientificAuthorityIsFalse :
      promotesScientificAuthority ≡ false
    receiptReading :
      String

open QiOperatorTheoryBoundaryReceipt public

canonicalQiOperatorTheoryBoundaryReceipt :
  QiOperatorTheoryBoundaryReceipt
canonicalQiOperatorTheoryBoundaryReceipt =
  record
    { status =
        qiOperatorTheoryRoleGrammarOnlyNonPromoting
    ; roleCategories =
        canonicalQiRoleCategories
    ; roleCategoriesAreCanonical =
        refl
    ; operatorRows =
        canonicalOperatorFamilyQiRoleRows
    ; operatorRowsAreCanonical =
        refl
    ; coreRoleRows =
        canonicalQiRoleCoreAlignmentRows
    ; coreRoleRowsAreCanonical =
        refl
    ; coreQiRoleFamily =
        canonicalQiCoreRoleFamily
    ; coreQiRoleFamilyIsCanonical =
        refl
    ; coreQiRoleFamilyExternalAuthorityIsFalse =
        refl
    ; spectralRows =
        canonicalQiSpectralInterpretationRows
    ; spectralRowsAreCanonical =
        refl
    ; sweetgrassGate =
        canonicalSweetgrassReciprocityGate
    ; sweetgrassGateIsCanonical =
        refl
    ; authorityBoundary =
        canonicalQiAuthorityBoundary
    ; authorityBoundaryIsCanonical =
        refl
    ; blockedAuthorityKinds =
        canonicalQiBlockedAuthorityKinds
    ; blockedAuthorityKindsAreCanonical =
        refl
    ; blockedAuthorityKindRows =
        canonicalQiBlockedAuthorityKindRows
    ; blockedAuthorityKindRowsAreCanonical =
        refl
    ; receiptRows =
        canonicalQiReceiptBoundaryRows
    ; receiptRowsAreCanonical =
        refl
    ; operatorTheoryProvidesRoleGrammarOnly =
        true
    ; operatorTheoryProvidesRoleGrammarOnlyIsTrue =
        refl
    ; promotesEmpiricalAuthority =
        false
    ; promotesEmpiricalAuthorityIsFalse =
        refl
    ; promotesSpiritualAuthority =
        false
    ; promotesSpiritualAuthorityIsFalse =
        refl
    ; promotesMysticalAuthority =
        false
    ; promotesMysticalAuthorityIsFalse =
        refl
    ; promotesClinicalAuthority =
        false
    ; promotesClinicalAuthorityIsFalse =
        refl
    ; promotesEnvironmentalAuthority =
        false
    ; promotesEnvironmentalAuthorityIsFalse =
        refl
    ; promotesLegalAuthority =
        false
    ; promotesLegalAuthorityIsFalse =
        refl
    ; promotesScientificAuthority =
        false
    ; promotesScientificAuthorityIsFalse =
        refl
    ; receiptReading =
        "Feng Shui/Qi operator theory is recorded as non-promoting role grammar for Qi-field formalism only."
    }

qiOperatorTheoryReceiptNonPromotingMystical :
  promotesMysticalAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingMystical =
  refl

qiOperatorTheoryReceiptNonPromotingEmpirical :
  promotesEmpiricalAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingEmpirical =
  refl

qiOperatorTheoryReceiptNonPromotingSpiritual :
  promotesSpiritualAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingSpiritual =
  refl

qiOperatorTheoryReceiptNonPromotingClinical :
  promotesClinicalAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingClinical =
  refl

qiOperatorTheoryReceiptNonPromotingEnvironmental :
  promotesEnvironmentalAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingEnvironmental =
  refl

qiOperatorTheoryReceiptNonPromotingLegal :
  promotesLegalAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingLegal =
  refl

qiOperatorTheoryReceiptNonPromotingScientific :
  promotesScientificAuthority canonicalQiOperatorTheoryBoundaryReceipt
    ≡ false
qiOperatorTheoryReceiptNonPromotingScientific =
  refl

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapter receipts consume the shared cores without replacing the
-- local Qi/operator-theory rows above.

authorityNonPromotionCoreAdapter :
  AuthorityCore.AuthorityNonPromotionBundle
authorityNonPromotionCoreAdapter =
  AuthorityCore.mkClosedAuthorityNonPromotionBundle
    "Qi/operator-theory boundary authority non-promotion adapter"

authorityNonPromotionCoreAdapterCanonicalKindsFalse :
  AuthorityCore.AllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds
authorityNonPromotionCoreAdapterCanonicalKindsFalse =
  AuthorityCore.proveAllAuthorityKindsFalse
    authorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds

authorityNonPromotionCoreAdapterGenericReceipt :
  GenericReceipt.GenericReceipt
authorityNonPromotionCoreAdapterGenericReceipt =
  AuthorityCore.authorityNonPromotionGenericReceipt
    authorityNonPromotionCoreAdapter

qiOperatorTheoryAdapterTheoremAuthorityFalse :
  AuthorityCore.theoremAuthorityFlag authorityNonPromotionCoreAdapter
    ≡ false
qiOperatorTheoryAdapterTheoremAuthorityFalse =
  AuthorityCore.bundleTheoremAuthorityIsFalse
    authorityNonPromotionCoreAdapter

qiOperatorTheoryAdapterScientificAuthorityFalse :
  AuthorityCore.scientificAuthorityFlag authorityNonPromotionCoreAdapter
    ≡ false
qiOperatorTheoryAdapterScientificAuthorityFalse =
  AuthorityCore.bundleScientificAuthorityIsFalse
    authorityNonPromotionCoreAdapter

qiOperatorTheoryAdapterMetaphysicalAuthorityFalse :
  AuthorityCore.metaphysicalAuthorityFlag authorityNonPromotionCoreAdapter
    ≡ false
qiOperatorTheoryAdapterMetaphysicalAuthorityFalse =
  AuthorityCore.bundleMetaphysicalAuthorityIsFalse
    authorityNonPromotionCoreAdapter

qiOperatorTheoryAdapterSpiritualAuthorityFalse :
  AuthorityCore.spiritualAuthorityFlag authorityNonPromotionCoreAdapter
    ≡ false
qiOperatorTheoryAdapterSpiritualAuthorityFalse =
  AuthorityCore.bundleSpiritualAuthorityIsFalse
    authorityNonPromotionCoreAdapter

candidateOnlyCoreAdapter :
  CandidateCore.CandidateOnlyRow
candidateOnlyCoreAdapter =
  CandidateCore.mkCandidateOnlyRow
    "Qi/operator-theory candidate-only adapter"
    "DASHI.Culture.QiOperatorTheoryBoundary"
    "candidateOnlyCoreAdapter"
    CandidateCore.operatorCandidateKind
    CandidateCore.operatorCandidateOnlyStatus
    "Qi operator-theory rows are candidate-only role-grammar surfaces."
    "Validation remains outside this Qi/operator-theory boundary."

candidateOnlyCoreAdapterReceipt :
  CandidateCore.CandidateOnlyReceipt candidateOnlyCoreAdapter
candidateOnlyCoreAdapterReceipt =
  CandidateCore.canonicalCandidateOnlyReceipt
    candidateOnlyCoreAdapter
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

candidateOnlyCoreAdapterPromotedFalse :
  CandidateCore.promoted candidateOnlyCoreAdapter ≡ false
candidateOnlyCoreAdapterPromotedFalse =
  CandidateCore.candidatePromotedIsFalse
    candidateOnlyCoreAdapterReceipt

candidateFunctionalCoreAdapter :
  FunctionalCore.CandidateFunctionalSurface
candidateFunctionalCoreAdapter =
  FunctionalCore.candidateFunctionalSurface
    "Qi symbolic carrier"
    "Qi operator-theory formal state"
    (FunctionalCore.NamedFunctionalKind "Qi role-grammar functional")
    (FunctionalCore.neutralFunctionalTerm
      "Qi role-grammar neutral term"
      FunctionalCore.neutralSymbolicWeight
      ∷ [])
    FunctionalCore.candidateTermCatalogue
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

candidateFunctionalCoreAdapterCandidateOnly :
  FunctionalCore.candidateOnly candidateFunctionalCoreAdapter
    ≡ true
candidateFunctionalCoreAdapterCandidateOnly =
  refl

candidateFunctionalCoreAdapterMetaphysicalAuthorityFalse :
  FunctionalCore.metaphysicalAuthority candidateFunctionalCoreAdapter
    ≡ false
candidateFunctionalCoreAdapterMetaphysicalAuthorityFalse =
  refl

candidateFunctionalCoreAdapterGenericReceipt :
  GenericReceipt.GenericReceipt
candidateFunctionalCoreAdapterGenericReceipt =
  FunctionalCore.candidateFunctionalSurfaceGenericReceipt
    candidateFunctionalCoreAdapter

operatorShapeNonAuthorityCoreAdapter :
  OperatorShapeCore.OperatorShapeCandidateReceipt
operatorShapeNonAuthorityCoreAdapter =
  OperatorShapeCore.mkOperatorShapeCandidateReceipt
    OperatorShapeCore.receiptDomainCarrier
    OperatorShapeCore.receiptCodomainCarrier
    OperatorShapeCore.symbolicOperatorTag
    OperatorShapeCore.diagnosticCompositionHint
    OperatorShapeCore.boundednessCandidateRequiresProof
    OperatorShapeCore.contractionCandidateUnwitnessed
    OperatorShapeCore.dissipativeCandidateUnwitnessed
    OperatorShapeCore.spectralShapeCandidate
    "Qi/operator theory consumes operator-shaped vocabulary as candidate grammar only; no operator theorem authority is supplied."

operatorShapeNonAuthorityCoreAdapterComponentsCanonical :
  OperatorShapeCore.components operatorShapeNonAuthorityCoreAdapter
    ≡ OperatorShapeCore.canonicalOperatorShapeReceiptComponents
operatorShapeNonAuthorityCoreAdapterComponentsCanonical =
  refl

operatorShapeNonAuthorityCoreAdapterTheoremAuthorityFalse :
  OperatorShapeCore.actualTheoremAuthority operatorShapeNonAuthorityCoreAdapter
    ≡ false
operatorShapeNonAuthorityCoreAdapterTheoremAuthorityFalse =
  OperatorShapeCore.operatorShapeBlocksTheoremAuthority
    operatorShapeNonAuthorityCoreAdapter

operatorShapeNonAuthorityCoreAdapterGenericReceipt :
  GenericReceipt.GenericReceipt
operatorShapeNonAuthorityCoreAdapterGenericReceipt =
  OperatorShapeCore.operatorShapeCandidateGenericReceipt
    operatorShapeNonAuthorityCoreAdapter
