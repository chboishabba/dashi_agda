module DASHI.Moonshine.Monster3BCommonRepresentationTransportExact where

------------------------------------------------------------------------
-- MONSTER 3B H_zeta: COMMON REPRESENTATION-THEORY SAME-OBJECT TRANSPORT
--
-- The literal finite Schrodinger model, its full Heisenberg action law,
-- irreducibility, exact additive-character orthogonality, and exhaustive
-- executable character receipt are already owned elsewhere on this branch.
--
-- The remaining H_zeta promotion must not be phrased as "same degree" or
-- "same character label".  Both the literal Schrodinger model and one actual
-- selected W_zeta|E constituent must inhabit the SAME
-- IrreducibleCharacterDetermination theory, with proof-relevant bindings back
-- to their source/model carriers.  Once that is paid, the existing
-- Monster3BHZetaCharacterTransportCompilerExact produces the equivariant iso.
--
-- This file owns only that adapter/compiler shape.  It does not manufacture an
-- actual Monster constituent, and it does not import executable evidence as an
-- Agda-kernel trace theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁; Set₂)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact as Compiler
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Hardening
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as LiteralCharacter
import DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact as Orthogonality

record LiteralSchrodingerCommonTheoryAttachment
    (theory : Uniqueness.IrreducibleCharacterDetermination) : Set₂ where
  field
    fixedPhaseData : Uniqueness.FixedPhaseRepresentationData theory
    literalVectorCarrierSameObject : Set
    literalHeisenbergActionSameObject : Set
    literalIrreducibilitySameObject : Set
    literalCharacterSameObject : Set
    literalVectorCarrierSameObjectWitness : literalVectorCarrierSameObject
    literalHeisenbergActionSameObjectWitness : literalHeisenbergActionSameObject
    literalIrreducibilitySameObjectWitness : literalIrreducibilitySameObject
    literalCharacterSameObjectWitness : literalCharacterSameObject
    selectedZetaPhase :
      Uniqueness.centralPhase fixedPhaseData ≡ Uniqueness.zetaPhase
open LiteralSchrodingerCommonTheoryAttachment public

record ActualHZetaConstituentCommonTheoryAttachment
    (theory : Uniqueness.IrreducibleCharacterDetermination) : Set₂ where
  field
    fixedPhaseData : Uniqueness.FixedPhaseRepresentationData theory
    actualWZetaRestrictionSameObject : Set
    actualSelectedConstituentSameObject : Set
    actualConstituentIrreducibilitySameObject : Set
    actualConstituentCharacterSameObject : Set
    actualWZetaRestrictionSameObjectWitness : actualWZetaRestrictionSameObject
    actualSelectedConstituentSameObjectWitness : actualSelectedConstituentSameObject
    actualConstituentIrreducibilitySameObjectWitness :
      actualConstituentIrreducibilitySameObject
    actualConstituentCharacterSameObjectWitness : actualConstituentCharacterSameObject
    selectedZetaPhase :
      Uniqueness.centralPhase fixedPhaseData ≡ Uniqueness.zetaPhase
open ActualHZetaConstituentCommonTheoryAttachment public

compileCharacterTransport :
  (theory : Uniqueness.IrreducibleCharacterDetermination) →
  LiteralSchrodingerCommonTheoryAttachment theory →
  ActualHZetaConstituentCommonTheoryAttachment theory →
  Compiler.HZetaCharacterTransport theory
compileCharacterTransport theory model actual = record
  { schrodingerRepresentation =
      LiteralSchrodingerCommonTheoryAttachment.fixedPhaseData model
  ; actualConstituentRepresentation =
      ActualHZetaConstituentCommonTheoryAttachment.fixedPhaseData actual
  ; selectedPhaseAgrees =
      trans
        (LiteralSchrodingerCommonTheoryAttachment.selectedZetaPhase model)
        (sym (ActualHZetaConstituentCommonTheoryAttachment.selectedZetaPhase actual))
  ; SchrodingerRepresentationIsLiteralModel =
      LiteralSchrodingerCommonTheoryAttachment.literalVectorCarrierSameObject model
  ; schrodingerRepresentationIsLiteralModelWitness =
      LiteralSchrodingerCommonTheoryAttachment.literalVectorCarrierSameObjectWitness model
  ; ActualRepresentationIsSelectedConstituent =
      ActualHZetaConstituentCommonTheoryAttachment.actualSelectedConstituentSameObject actual
  ; actualRepresentationIsSelectedConstituentWitness =
      ActualHZetaConstituentCommonTheoryAttachment.actualSelectedConstituentSameObjectWitness actual
  ; DashiCharacterTransportIsSameCharacter =
      LiteralSchrodingerCommonTheoryAttachment.literalCharacterSameObject model
  ; dashiCharacterTransportIsSameCharacterWitness =
      LiteralSchrodingerCommonTheoryAttachment.literalCharacterSameObjectWitness model
  }

compilePaidHZetaRecognition :
  (theory : Uniqueness.IrreducibleCharacterDetermination) →
  (model : LiteralSchrodingerCommonTheoryAttachment theory) →
  (actual : ActualHZetaConstituentCommonTheoryAttachment theory) →
  Hardening.PaidSchrodingerIsActualHZeta
    (Compiler.compiledLegacyHZetaRecognition theory
      (compileCharacterTransport theory model actual))
compilePaidHZetaRecognition theory model actual =
  Compiler.compiledPaidHZetaRecognition theory
    (compileCharacterTransport theory model actual)

record Boundary : Set where
  constructor boundary
  field
    modelSideAttachmentTyped : Bool
    actualConstituentAttachmentTyped : Bool
    sameTheoryCompilerTyped : Bool
    paidHZetaCompilerReused : Bool
    literalCharacterExecutablePaid : Bool
    additiveCharacterOrthogonalitySourceWritten : Bool
    formalLiteralTraceBridgeInhabited : Bool
    commonRepresentationTheoryInhabited : Bool
    literalModelAttachmentInhabited : Bool
    actualConstituentAttachmentInhabited : Bool
    actualHZetaSameObjectInhabited : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true
  (LiteralCharacter.literalCharacterMatchesCanonicalHeisenbergSignatureExecutable
    LiteralCharacter.canonicalBoundary)
  (Orthogonality.factorizedAdditiveCharacterOrthogonalityPaid
    Orthogonality.canonicalBoundary)
  false false false false false

data ExecutableCharacterCreatesCommonRepresentationTheory : Set where
data Degree729CreatesActualConstituent : Set where
data CharacterLabelCreatesSameObjectAttachment : Set where

executableCharacterDoesNotCreateCommonRepresentationTheory :
  ExecutableCharacterCreatesCommonRepresentationTheory → ⊥
executableCharacterDoesNotCreateCommonRepresentationTheory ()

degreeDoesNotCreateActualConstituent :
  Degree729CreatesActualConstituent → ⊥
degreeDoesNotCreateActualConstituent ()

characterLabelDoesNotCreateSameObjectAttachment :
  CharacterLabelCreatesSameObjectAttachment → ⊥
characterLabelDoesNotCreateSameObjectAttachment ()
