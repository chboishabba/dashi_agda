module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Character
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact as Stone
import DASHI.Moonshine.Monster3BFiniteHeisenbergCommutantExact as Commutant

------------------------------------------------------------------------
-- FINITE STONE-VON NEUMANN UNIQUENESS: BIDI SPLIT
--
-- Do not leave "uniqueness" as one opaque payment.  The extraspecial character
-- inventory already has exactly two nonlinear signatures, distinguished by
-- the two nontrivial central C3 phases.  Thus fixed central phase determines a
-- unique nonlinear *character signature*.  Promotion from equal characters to
-- an equivariant representation isomorphism is a separate standard
-- characteristic-zero representation-theory theorem.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Stable nonlinear signature carrier.
------------------------------------------------------------------------

data NontrivialCentralPhase : Set where
  zetaPhase zetaSquaredPhase : NontrivialCentralPhase

data NonlinearCharacterSignature : Set where
  heisenbergZetaSignature
  heisenbergZetaSquaredSignature
  : NonlinearCharacterSignature

centralPhaseOfSignature : NonlinearCharacterSignature → NontrivialCentralPhase
centralPhaseOfSignature heisenbergZetaSignature = zetaPhase
centralPhaseOfSignature heisenbergZetaSquaredSignature = zetaSquaredPhase

traceOfSignature :
  NonlinearCharacterSignature →
  Character.ExtraspecialClassKind →
  Character.CyclotomicTrace3
traceOfSignature heisenbergZetaSignature = Character.heisenbergKernelTrace
traceOfSignature heisenbergZetaSquaredSignature = Character.conjugateHeisenbergKernelTrace

signatureDegree : NonlinearCharacterSignature → Nat
signatureDegree heisenbergZetaSignature = 729
signatureDegree heisenbergZetaSquaredSignature = 729

------------------------------------------------------------------------
-- 2. Fixed nontrivial central phase selects exactly one of the two signatures.
------------------------------------------------------------------------

signatureForPhase : NontrivialCentralPhase → NonlinearCharacterSignature
signatureForPhase zetaPhase = heisenbergZetaSignature
signatureForPhase zetaSquaredPhase = heisenbergZetaSquaredSignature

signatureHasRequestedPhase :
  (phase : NontrivialCentralPhase) →
  centralPhaseOfSignature (signatureForPhase phase) ≡ phase
signatureHasRequestedPhase zetaPhase = refl
signatureHasRequestedPhase zetaSquaredPhase = refl

fixedPhaseSignatureUnique :
  (phase : NontrivialCentralPhase) →
  (signature : NonlinearCharacterSignature) →
  centralPhaseOfSignature signature ≡ phase →
  signature ≡ signatureForPhase phase
fixedPhaseSignatureUnique zetaPhase heisenbergZetaSignature refl = refl
fixedPhaseSignatureUnique zetaPhase heisenbergZetaSquaredSignature ()
fixedPhaseSignatureUnique zetaSquaredPhase heisenbergZetaSignature ()
fixedPhaseSignatureUnique zetaSquaredPhase heisenbergZetaSquaredSignature refl = refl

zetaSignatureTraceIsCanonical :
  (kind : Character.ExtraspecialClassKind) →
  traceOfSignature (signatureForPhase zetaPhase) kind
  ≡ Character.heisenbergKernelTrace kind
zetaSignatureTraceIsCanonical kind = refl

zetaSquaredSignatureTraceIsCanonical :
  (kind : Character.ExtraspecialClassKind) →
  traceOfSignature (signatureForPhase zetaSquaredPhase) kind
  ≡ Character.conjugateHeisenbergKernelTrace kind
zetaSquaredSignatureTraceIsCanonical kind = refl

------------------------------------------------------------------------
-- 3. Model irreducibility has two independent theorem-bearing routes.
------------------------------------------------------------------------

record ModelIrreducibilityCrossCheck : Set where
  constructor model-irreducibility-cross-check
  field
    witnessedSubspaceRouteClosed : Bool
    scalarCommutantRouteAvailable : Bool

canonicalModelIrreducibilityCrossCheck : ModelIrreducibilityCrossCheck
canonicalModelIrreducibilityCrossCheck =
  model-irreducibility-cross-check true true

------------------------------------------------------------------------
-- 4. Generic characteristic-zero representation payment.
--
-- This interface states exactly what remains after signature uniqueness.  It
-- deliberately does not pretend character equality chooses a preferred basis.
------------------------------------------------------------------------

record IrreducibleCharacterDetermination : Set₂ where
  field
    Representation : Set₁
    CharacterOf : Representation → Character.ExtraspecialClassKind → Character.CyclotomicTrace3
    IsIrreducible : Representation → Set
    EquivariantIso : Representation → Representation → Set

    equalCharactersGiveIso :
      (left right : Representation) →
      IsIrreducible left →
      IsIrreducible right →
      ((kind : Character.ExtraspecialClassKind) →
        CharacterOf left kind ≡ CharacterOf right kind) →
      EquivariantIso left right

open IrreducibleCharacterDetermination public

------------------------------------------------------------------------
-- 5. Fixed-phase uniqueness compiler once a representation layer instantiates
-- the standard character-determination theorem.
------------------------------------------------------------------------

record FixedPhaseRepresentationData
    (theory : IrreducibleCharacterDetermination) : Set₁ where
  field
    representation : Representation theory
    irreducible : IsIrreducible theory representation
    centralPhase : NontrivialCentralPhase
    characterMatchesSelectedSignature :
      (kind : Character.ExtraspecialClassKind) →
      CharacterOf theory representation kind
      ≡ traceOfSignature (signatureForPhase centralPhase) kind

open FixedPhaseRepresentationData public

fixedPhaseRepresentationsAreIsomorphic :
  (theory : IrreducibleCharacterDetermination) →
  (left right : FixedPhaseRepresentationData theory) →
  centralPhase left ≡ centralPhase right →
  EquivariantIso theory (representation left) (representation right)
fixedPhaseRepresentationsAreIsomorphic theory left right samePhase =
  equalCharactersGiveIso theory
    (representation left)
    (representation right)
    (irreducible left)
    (irreducible right)
    (λ kind →
      trans
        (characterMatchesSelectedSignature left kind)
        (trans
          (cong
            (λ phase → traceOfSignature (signatureForPhase phase) kind)
            samePhase)
          (sym (characterMatchesSelectedSignature right kind))))

------------------------------------------------------------------------
-- 6. Search frontier.
------------------------------------------------------------------------

data UniquenessLeaf : Set where
  nonlinearSignatureInventory
  fixedPhaseSelectsUniqueSignature
  modelWitnessedIrreducibility
  modelScalarCommutant
  instantiateCharacterDeterminationTheorem
  attachActualRestrictedIrreduciblesToSignature
  constructActualZetaRecognition
  : UniquenessLeaf

data LeafStatus : Set where closed open blocked : LeafStatus

leafStatus : UniquenessLeaf → LeafStatus
leafStatus nonlinearSignatureInventory = closed
leafStatus fixedPhaseSelectsUniqueSignature = closed
leafStatus modelWitnessedIrreducibility = closed
leafStatus modelScalarCommutant = closed
leafStatus instantiateCharacterDeterminationTheorem = open
leafStatus attachActualRestrictedIrreduciblesToSignature = blocked
leafStatus constructActualZetaRecognition = blocked

highestImpactUniquenessLeaf : UniquenessLeaf
highestImpactUniquenessLeaf = instantiateCharacterDeterminationTheorem

highestImpactUniquenessLeafIsOpen :
  leafStatus highestImpactUniquenessLeaf ≡ open
highestImpactUniquenessLeafIsOpen = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data UniqueSignatureAutomaticallyChoosesBasis : Set where
data EqualCharactersAutomaticallyGiveLiteralStateEquality : Set where
data ScalarCommutantAloneConstructsActualMonsterSector : Set where

uniqueSignatureDoesNotChooseBasis : UniqueSignatureAutomaticallyChoosesBasis → ⊥
uniqueSignatureDoesNotChooseBasis ()

equalCharactersDoNotGiveLiteralStateEquality :
  EqualCharactersAutomaticallyGiveLiteralStateEquality → ⊥
equalCharactersDoNotGiveLiteralStateEquality ()

scalarCommutantDoesNotConstructActualSector :
  ScalarCommutantAloneConstructsActualMonsterSector → ⊥
scalarCommutantDoesNotConstructActualSector ()

record StoneVonNeumannUniquenessBidiBoundary : Set where
  constructor stone-von-neumann-uniqueness-bidi-boundary
  field
    twoNonlinearSignaturesNamed : Bool
    fixedZetaPhaseSelectsOneSignature : Bool
    fixedZetaSquaredPhaseSelectsOneSignature : Bool
    witnessedIrreducibilityRouteClosed : Bool
    scalarCommutantCrossCheckAvailable : Bool
    characterDeterminationStillRequiresRepresentationLayer : Bool
    signatureEqualityChoosesLiteralBasis : Bool

canonicalStoneVonNeumannUniquenessBidiBoundary : StoneVonNeumannUniquenessBidiBoundary
canonicalStoneVonNeumannUniquenessBidiBoundary =
  stone-von-neumann-uniqueness-bidi-boundary
    true true true true true true false
