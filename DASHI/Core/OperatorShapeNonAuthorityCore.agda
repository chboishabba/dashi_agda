module DASHI.Core.OperatorShapeNonAuthorityCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as GenericReceipt

data OperatorShapeNonAuthorityStatus : Set where
  operatorShapeCandidateOnly :
    OperatorShapeNonAuthorityStatus

data DomainCarrierLabel : Set where
  genericDomainCarrier :
    DomainCarrierLabel

  finiteSymbolicDomainCarrier :
    DomainCarrierLabel

  receiptDomainCarrier :
    DomainCarrierLabel

data CodomainCarrierLabel : Set where
  genericCodomainCarrier :
    CodomainCarrierLabel

  finiteSymbolicCodomainCarrier :
    CodomainCarrierLabel

  receiptCodomainCarrier :
    CodomainCarrierLabel

data OperatorShapeTag : Set where
  symbolicOperatorTag :
    OperatorShapeTag

  residualOperatorTag :
    OperatorShapeTag

  transportOperatorTag :
    OperatorShapeTag

  observationOperatorTag :
    OperatorShapeTag

data CompositionHint : Set where
  noCompositionWitness :
    CompositionHint

  endomorphismCompositionHint :
    CompositionHint

  domainToCodomainCompositionHint :
    CompositionHint

  diagnosticCompositionHint :
    CompositionHint

data BoundednessCandidate : Set where
  boundednessCandidateUnwitnessed :
    BoundednessCandidate

  boundednessCandidateSymbolic :
    BoundednessCandidate

  boundednessCandidateRequiresProof :
    BoundednessCandidate

data ContractionCandidate : Set where
  contractionCandidateUnwitnessed :
    ContractionCandidate

  contractionCandidateSymbolic :
    ContractionCandidate

  contractionCandidateRequiresProof :
    ContractionCandidate

data DissipativeCandidate : Set where
  dissipativeCandidateUnwitnessed :
    DissipativeCandidate

  dissipativeCandidateSymbolic :
    DissipativeCandidate

  dissipativeCandidateRequiresProof :
    DissipativeCandidate

data SpectralShapeTag : Set where
  noSpectrumWitness :
    SpectralShapeTag

  spectralShapeCandidate :
    SpectralShapeTag

  spectralDiagnosticShape :
    SpectralShapeTag

data OperatorShapeReceiptComponent : Set where
  domainCarrierComponent :
    OperatorShapeReceiptComponent

  codomainCarrierComponent :
    OperatorShapeReceiptComponent

  operatorTagComponent :
    OperatorShapeReceiptComponent

  compositionHintComponent :
    OperatorShapeReceiptComponent

  boundednessCandidateComponent :
    OperatorShapeReceiptComponent

  contractionCandidateComponent :
    OperatorShapeReceiptComponent

  dissipativeCandidateComponent :
    OperatorShapeReceiptComponent

  spectralShapeTagComponent :
    OperatorShapeReceiptComponent

  authorityBlockComponent :
    OperatorShapeReceiptComponent

canonicalOperatorShapeReceiptComponents :
  List OperatorShapeReceiptComponent
canonicalOperatorShapeReceiptComponents =
  domainCarrierComponent
  ∷ codomainCarrierComponent
  ∷ operatorTagComponent
  ∷ compositionHintComponent
  ∷ boundednessCandidateComponent
  ∷ contractionCandidateComponent
  ∷ dissipativeCandidateComponent
  ∷ spectralShapeTagComponent
  ∷ authorityBlockComponent
  ∷ []

data OperatorShapeBlockedAuthorityKind : Set where
  boundedLinearOperatorAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  selfAdjointAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  spectrumAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  semigroupAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  generatorAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  PDEAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  functionalCalculusAuthorityKind :
    OperatorShapeBlockedAuthorityKind

  theoremAuthorityKind :
    OperatorShapeBlockedAuthorityKind

canonicalOperatorShapeBlockedAuthorityKinds :
  List OperatorShapeBlockedAuthorityKind
canonicalOperatorShapeBlockedAuthorityKinds =
  boundedLinearOperatorAuthorityKind
  ∷ selfAdjointAuthorityKind
  ∷ spectrumAuthorityKind
  ∷ semigroupAuthorityKind
  ∷ generatorAuthorityKind
  ∷ PDEAuthorityKind
  ∷ functionalCalculusAuthorityKind
  ∷ theoremAuthorityKind
  ∷ []

operatorShapeAuthorityPromoted :
  OperatorShapeBlockedAuthorityKind →
  Bool
operatorShapeAuthorityPromoted _ =
  false

record OperatorShapeBlockedAuthorityRow : Set where
  constructor operatorShapeBlockedAuthorityRow
  field
    blockedAuthorityKind :
      OperatorShapeBlockedAuthorityKind

    promoted :
      Bool

    promotedComputes :
      operatorShapeAuthorityPromoted blockedAuthorityKind ≡ promoted

    promotedIsFalse :
      promoted ≡ false

    reading :
      String

open OperatorShapeBlockedAuthorityRow public

blockedAuthorityRow :
  OperatorShapeBlockedAuthorityKind →
  String →
  OperatorShapeBlockedAuthorityRow
blockedAuthorityRow kind reading =
  operatorShapeBlockedAuthorityRow
    kind
    (operatorShapeAuthorityPromoted kind)
    refl
    refl
    reading

canonicalOperatorShapeBlockedAuthorityRows :
  List OperatorShapeBlockedAuthorityRow
canonicalOperatorShapeBlockedAuthorityRows =
  blockedAuthorityRow
    boundedLinearOperatorAuthorityKind
    "bounded-linear-operator authority is blocked; boundedness remains a candidate label only"
  ∷ blockedAuthorityRow
    selfAdjointAuthorityKind
    "self-adjoint authority is blocked; no symmetry, domain, or adjoint proof is supplied"
  ∷ blockedAuthorityRow
    spectrumAuthorityKind
    "spectrum authority is blocked; spectral wording is a shape tag only"
  ∷ blockedAuthorityRow
    semigroupAuthorityKind
    "semigroup authority is blocked; no time-indexed operator law is supplied"
  ∷ blockedAuthorityRow
    generatorAuthorityKind
    "generator authority is blocked; no infinitesimal generator theorem is supplied"
  ∷ blockedAuthorityRow
    PDEAuthorityKind
    "PDE authority is blocked; no continuum equation or solution theory is supplied"
  ∷ blockedAuthorityRow
    functionalCalculusAuthorityKind
    "functional-calculus authority is blocked; no calculus theorem is supplied"
  ∷ blockedAuthorityRow
    theoremAuthorityKind
    "theorem authority is blocked; this receipt records vocabulary only"
  ∷ []

canonicalOperatorShapeNonAuthorityStatement :
  String
canonicalOperatorShapeNonAuthorityStatement =
  "Generic operator-shaped vocabulary records carrier labels, operator tags, composition hints, candidate boundedness, contraction, dissipativity, and spectral shape only; it grants no bounded-linear-operator, self-adjoint, spectrum, semigroup, generator, PDE, functional-calculus, or theorem authority."

record OperatorShapeCandidateReceipt : Set where
  field
    status :
      OperatorShapeNonAuthorityStatus

    statusIsCandidateOnly :
      status ≡ operatorShapeCandidateOnly

    domainCarrierLabel :
      DomainCarrierLabel

    codomainCarrierLabel :
      CodomainCarrierLabel

    operatorTag :
      OperatorShapeTag

    compositionHint :
      CompositionHint

    boundednessCandidate :
      BoundednessCandidate

    contractionCandidate :
      ContractionCandidate

    dissipativeCandidate :
      DissipativeCandidate

    spectralShapeTag :
      SpectralShapeTag

    components :
      List OperatorShapeReceiptComponent

    componentsAreCanonical :
      components ≡ canonicalOperatorShapeReceiptComponents

    blockedAuthorityKinds :
      List OperatorShapeBlockedAuthorityKind

    blockedAuthorityKindsAreCanonical :
      blockedAuthorityKinds ≡ canonicalOperatorShapeBlockedAuthorityKinds

    blockedAuthorityRows :
      List OperatorShapeBlockedAuthorityRow

    blockedAuthorityRowsAreCanonical :
      blockedAuthorityRows ≡ canonicalOperatorShapeBlockedAuthorityRows

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    actualBoundedLinearOperatorAuthority :
      Bool

    actualBoundedLinearOperatorAuthorityIsFalse :
      actualBoundedLinearOperatorAuthority ≡ false

    actualSelfAdjointAuthority :
      Bool

    actualSelfAdjointAuthorityIsFalse :
      actualSelfAdjointAuthority ≡ false

    actualSpectrumAuthority :
      Bool

    actualSpectrumAuthorityIsFalse :
      actualSpectrumAuthority ≡ false

    actualSemigroupAuthority :
      Bool

    actualSemigroupAuthorityIsFalse :
      actualSemigroupAuthority ≡ false

    actualGeneratorAuthority :
      Bool

    actualGeneratorAuthorityIsFalse :
      actualGeneratorAuthority ≡ false

    actualPDEAuthority :
      Bool

    actualPDEAuthorityIsFalse :
      actualPDEAuthority ≡ false

    actualFunctionalCalculusAuthority :
      Bool

    actualFunctionalCalculusAuthorityIsFalse :
      actualFunctionalCalculusAuthority ≡ false

    actualTheoremAuthority :
      Bool

    actualTheoremAuthorityIsFalse :
      actualTheoremAuthority ≡ false

    statement :
      String

open OperatorShapeCandidateReceipt public

mkOperatorShapeCandidateReceipt :
  DomainCarrierLabel →
  CodomainCarrierLabel →
  OperatorShapeTag →
  CompositionHint →
  BoundednessCandidate →
  ContractionCandidate →
  DissipativeCandidate →
  SpectralShapeTag →
  String →
  OperatorShapeCandidateReceipt
mkOperatorShapeCandidateReceipt
  domain
  codomain
  tag
  composition
  boundedness
  contraction
  dissipative
  spectral
  reading =
  record
    { status =
        operatorShapeCandidateOnly
    ; statusIsCandidateOnly =
        refl
    ; domainCarrierLabel =
        domain
    ; codomainCarrierLabel =
        codomain
    ; operatorTag =
        tag
    ; compositionHint =
        composition
    ; boundednessCandidate =
        boundedness
    ; contractionCandidate =
        contraction
    ; dissipativeCandidate =
        dissipative
    ; spectralShapeTag =
        spectral
    ; components =
        canonicalOperatorShapeReceiptComponents
    ; componentsAreCanonical =
        refl
    ; blockedAuthorityKinds =
        canonicalOperatorShapeBlockedAuthorityKinds
    ; blockedAuthorityKindsAreCanonical =
        refl
    ; blockedAuthorityRows =
        canonicalOperatorShapeBlockedAuthorityRows
    ; blockedAuthorityRowsAreCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; actualBoundedLinearOperatorAuthority =
        false
    ; actualBoundedLinearOperatorAuthorityIsFalse =
        refl
    ; actualSelfAdjointAuthority =
        false
    ; actualSelfAdjointAuthorityIsFalse =
        refl
    ; actualSpectrumAuthority =
        false
    ; actualSpectrumAuthorityIsFalse =
        refl
    ; actualSemigroupAuthority =
        false
    ; actualSemigroupAuthorityIsFalse =
        refl
    ; actualGeneratorAuthority =
        false
    ; actualGeneratorAuthorityIsFalse =
        refl
    ; actualPDEAuthority =
        false
    ; actualPDEAuthorityIsFalse =
        refl
    ; actualFunctionalCalculusAuthority =
        false
    ; actualFunctionalCalculusAuthorityIsFalse =
        refl
    ; actualTheoremAuthority =
        false
    ; actualTheoremAuthorityIsFalse =
        refl
    ; statement =
        reading
    }

canonicalOperatorShapeCandidateReceipt :
  OperatorShapeCandidateReceipt
canonicalOperatorShapeCandidateReceipt =
  mkOperatorShapeCandidateReceipt
    genericDomainCarrier
    genericCodomainCarrier
    symbolicOperatorTag
    noCompositionWitness
    boundednessCandidateUnwitnessed
    contractionCandidateUnwitnessed
    dissipativeCandidateUnwitnessed
    noSpectrumWitness
    canonicalOperatorShapeNonAuthorityStatement

canonicalOperatorShapeStatusCandidateOnly :
  status canonicalOperatorShapeCandidateReceipt
  ≡
  operatorShapeCandidateOnly
canonicalOperatorShapeStatusCandidateOnly =
  refl

canonicalOperatorShapeDomainCarrier :
  domainCarrierLabel canonicalOperatorShapeCandidateReceipt
  ≡
  genericDomainCarrier
canonicalOperatorShapeDomainCarrier =
  refl

canonicalOperatorShapeCodomainCarrier :
  codomainCarrierLabel canonicalOperatorShapeCandidateReceipt
  ≡
  genericCodomainCarrier
canonicalOperatorShapeCodomainCarrier =
  refl

canonicalOperatorShapeOperatorTag :
  operatorTag canonicalOperatorShapeCandidateReceipt
  ≡
  symbolicOperatorTag
canonicalOperatorShapeOperatorTag =
  refl

canonicalOperatorShapeCompositionHint :
  compositionHint canonicalOperatorShapeCandidateReceipt
  ≡
  noCompositionWitness
canonicalOperatorShapeCompositionHint =
  refl

canonicalOperatorShapeBoundednessCandidate :
  boundednessCandidate canonicalOperatorShapeCandidateReceipt
  ≡
  boundednessCandidateUnwitnessed
canonicalOperatorShapeBoundednessCandidate =
  refl

canonicalOperatorShapeContractionCandidate :
  contractionCandidate canonicalOperatorShapeCandidateReceipt
  ≡
  contractionCandidateUnwitnessed
canonicalOperatorShapeContractionCandidate =
  refl

canonicalOperatorShapeDissipativeCandidate :
  dissipativeCandidate canonicalOperatorShapeCandidateReceipt
  ≡
  dissipativeCandidateUnwitnessed
canonicalOperatorShapeDissipativeCandidate =
  refl

canonicalOperatorShapeSpectralShapeTag :
  spectralShapeTag canonicalOperatorShapeCandidateReceipt
  ≡
  noSpectrumWitness
canonicalOperatorShapeSpectralShapeTag =
  refl

canonicalOperatorShapeStatement :
  statement canonicalOperatorShapeCandidateReceipt
  ≡
  canonicalOperatorShapeNonAuthorityStatement
canonicalOperatorShapeStatement =
  refl

operatorShapeBlocksBoundedLinearOperatorAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualBoundedLinearOperatorAuthority receipt ≡ false
operatorShapeBlocksBoundedLinearOperatorAuthority receipt =
  actualBoundedLinearOperatorAuthorityIsFalse receipt

operatorShapeBlocksSelfAdjointAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualSelfAdjointAuthority receipt ≡ false
operatorShapeBlocksSelfAdjointAuthority receipt =
  actualSelfAdjointAuthorityIsFalse receipt

operatorShapeBlocksSpectrumAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualSpectrumAuthority receipt ≡ false
operatorShapeBlocksSpectrumAuthority receipt =
  actualSpectrumAuthorityIsFalse receipt

operatorShapeBlocksSemigroupAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualSemigroupAuthority receipt ≡ false
operatorShapeBlocksSemigroupAuthority receipt =
  actualSemigroupAuthorityIsFalse receipt

operatorShapeBlocksGeneratorAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualGeneratorAuthority receipt ≡ false
operatorShapeBlocksGeneratorAuthority receipt =
  actualGeneratorAuthorityIsFalse receipt

operatorShapeBlocksPDEAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualPDEAuthority receipt ≡ false
operatorShapeBlocksPDEAuthority receipt =
  actualPDEAuthorityIsFalse receipt

operatorShapeBlocksFunctionalCalculusAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualFunctionalCalculusAuthority receipt ≡ false
operatorShapeBlocksFunctionalCalculusAuthority receipt =
  actualFunctionalCalculusAuthorityIsFalse receipt

operatorShapeBlocksTheoremAuthority :
  (receipt : OperatorShapeCandidateReceipt) →
  actualTheoremAuthority receipt ≡ false
operatorShapeBlocksTheoremAuthority receipt =
  actualTheoremAuthorityIsFalse receipt

data BoundedLinearOperatorAuthorityFromShape : Set where

boundedLinearOperatorAuthorityFromShapeImpossible :
  BoundedLinearOperatorAuthorityFromShape →
  ⊥
boundedLinearOperatorAuthorityFromShapeImpossible ()

data SelfAdjointAuthorityFromShape : Set where

selfAdjointAuthorityFromShapeImpossible :
  SelfAdjointAuthorityFromShape →
  ⊥
selfAdjointAuthorityFromShapeImpossible ()

data SpectrumAuthorityFromShape : Set where

spectrumAuthorityFromShapeImpossible :
  SpectrumAuthorityFromShape →
  ⊥
spectrumAuthorityFromShapeImpossible ()

data SemigroupAuthorityFromShape : Set where

semigroupAuthorityFromShapeImpossible :
  SemigroupAuthorityFromShape →
  ⊥
semigroupAuthorityFromShapeImpossible ()

data GeneratorAuthorityFromShape : Set where

generatorAuthorityFromShapeImpossible :
  GeneratorAuthorityFromShape →
  ⊥
generatorAuthorityFromShapeImpossible ()

data PDEAuthorityFromShape : Set where

pdeAuthorityFromShapeImpossible :
  PDEAuthorityFromShape →
  ⊥
pdeAuthorityFromShapeImpossible ()

data FunctionalCalculusAuthorityFromShape : Set where

functionalCalculusAuthorityFromShapeImpossible :
  FunctionalCalculusAuthorityFromShape →
  ⊥
functionalCalculusAuthorityFromShapeImpossible ()

data TheoremAuthorityFromShape : Set where

theoremAuthorityFromShapeImpossible :
  TheoremAuthorityFromShape →
  ⊥
theoremAuthorityFromShapeImpossible ()

operatorShapeCandidateGenericReceipt :
  OperatorShapeCandidateReceipt →
  GenericReceipt.GenericReceipt
operatorShapeCandidateGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    "operator shape non-authority core"
    "DASHI.Core.OperatorShapeNonAuthorityCore"
    "canonicalOperatorShapeCandidateReceipt"
    (statement receipt)
    "operator-shaped vocabulary remains candidate-only and supplies no bounded-linear-operator, self-adjoint, spectrum, semigroup, generator, PDE, functional-calculus, or theorem authority"
    "agda -i . DASHI/Core/OperatorShapeNonAuthorityCore.agda"

canonicalOperatorShapeCandidateGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalOperatorShapeCandidateGenericReceipt =
  operatorShapeCandidateGenericReceipt canonicalOperatorShapeCandidateReceipt

canonicalOperatorShapeCandidateGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalOperatorShapeCandidateGenericReceipts =
  canonicalOperatorShapeCandidateGenericReceipt
  ∷ []

canonicalOperatorShapeCandidateGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalOperatorShapeCandidateGenericReceipts
canonicalOperatorShapeCandidateGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalOperatorShapeCandidateGenericReceipts
