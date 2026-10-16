module DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact where

------------------------------------------------------------------------
-- H_zeta SAME-OBJECT COMPILER FROM FIXED-PHASE CHARACTER DATA
--
-- The generic representation theorem is already encoded by
-- `fixedPhaseRepresentationsAreIsomorphic`: two irreducible representations in
-- one `IrreducibleCharacterDetermination` theory, with equal selected central
-- phase and characters matching the canonical nonlinear signature, are
-- equivariantly isomorphic.
--
-- This owner turns that theorem into the exact hardened H_zeta target. It does
-- NOT package the concrete Monster or Schrodinger representations itself. The
-- literal Schrodinger monomial action now has an independent executable
-- character derivation over all 3^13 coordinates; what remains on the model
-- side is the narrower SAME-object transport into the common representation
-- theory consumed here.
--
-- Remaining external/same-object payment:
--
--   * put the explicit Schrodinger action in the common Representation type;
--   * put one actual W_zeta|E irreducible constituent in that same type;
--   * transport the already-derived DASHI class character into that theory;
--   * bind those abstract representation objects to the literal source/model
--     carriers with proof-relevant same-object witnesses.
--
-- Once those inputs exist, the action intertwiner is a theorem, not another
-- independent assumption.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁; Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Uniqueness
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Hardening
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as LiteralCharacter
import DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact as HZeta

------------------------------------------------------------------------
-- 1. Concrete transport package into one common representation theory.
--
-- Same-object roles are proof-relevant: each role names the proposition type
-- and carries an inhabitant of that exact type.
------------------------------------------------------------------------

record HZetaCharacterTransport
    (theory : Uniqueness.IrreducibleCharacterDetermination) : Set₂ where
  field
    schrodingerRepresentation :
      Uniqueness.FixedPhaseRepresentationData theory

    actualConstituentRepresentation :
      Uniqueness.FixedPhaseRepresentationData theory

    selectedPhaseAgrees :
      Uniqueness.centralPhase schrodingerRepresentation
      ≡ Uniqueness.centralPhase actualConstituentRepresentation

    SchrodingerRepresentationIsLiteralModel : Set
    schrodingerRepresentationIsLiteralModelWitness :
      SchrodingerRepresentationIsLiteralModel

    ActualRepresentationIsSelectedConstituent : Set
    actualRepresentationIsSelectedConstituentWitness :
      ActualRepresentationIsSelectedConstituent

    DashiCharacterTransportIsSameCharacter : Set
    dashiCharacterTransportIsSameCharacterWitness :
      DashiCharacterTransportIsSameCharacter

open HZetaCharacterTransport public

------------------------------------------------------------------------
-- 2. The generic fixed-phase theorem produces the action-preserving iso.
------------------------------------------------------------------------

compiledEquivariantIso :
  (theory : Uniqueness.IrreducibleCharacterDetermination) →
  (transport : HZetaCharacterTransport theory) →
  Uniqueness.EquivariantIso theory
    (Uniqueness.representation (schrodingerRepresentation transport))
    (Uniqueness.representation (actualConstituentRepresentation transport))
compiledEquivariantIso theory transport =
  Uniqueness.fixedPhaseRepresentationsAreIsomorphic
    theory
    (schrodingerRepresentation transport)
    (actualConstituentRepresentation transport)
    (selectedPhaseAgrees transport)

------------------------------------------------------------------------
-- 3. Compile directly to the historical H_zeta socket and its new
--    proof-relevant wrapper. Both historical proposition types are chosen to
--    be the exact equivariant-isomorphism type because an equivariant iso is
--    simultaneously the recognition and action-intertwining payment here.
------------------------------------------------------------------------

compiledLegacyHZetaRecognition :
  (theory : Uniqueness.IrreducibleCharacterDetermination) →
  (transport : HZetaCharacterTransport theory) →
  HZeta.SchrodingerIsActualHZeta
compiledLegacyHZetaRecognition theory transport = record
  { actualHZetaRecognition =
      Uniqueness.EquivariantIso theory
        (Uniqueness.representation (schrodingerRepresentation transport))
        (Uniqueness.representation (actualConstituentRepresentation transport))
  ; actualHZetaActionIntertwiner =
      Uniqueness.EquivariantIso theory
        (Uniqueness.representation (schrodingerRepresentation transport))
        (Uniqueness.representation (actualConstituentRepresentation transport))
  }

compiledPaidHZetaRecognition :
  (theory : Uniqueness.IrreducibleCharacterDetermination) →
  (transport : HZetaCharacterTransport theory) →
  Hardening.PaidSchrodingerIsActualHZeta
    (compiledLegacyHZetaRecognition theory transport)
compiledPaidHZetaRecognition theory transport = record
  { actualHZetaRecognitionWitness = compiledEquivariantIso theory transport
  ; actualHZetaActionIntertwinerWitness = compiledEquivariantIso theory transport
  }

------------------------------------------------------------------------
-- 4. Machine-readable max-cut boundary.
--
-- Character DERIVATION and representation-theory TRANSPORT are deliberately
-- separate. The literal action now pays the former executably; no flag below
-- turns that receipt into a Mathlib FDRep or actual-Monster same-object proof.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    fixedPhaseIsoCompilerAvailable : Bool
    paidHZetaRecognitionCompilerAvailable : Bool

    literalSchrodingerCharacterDerivedExecutable : Bool
    literalSchrodingerCharacterMatchesCanonicalSignatureExecutable : Bool

    concreteSchrodingerRepresentationTransportPaidHere : Bool
    concreteActualConstituentTransportPaidHere : Bool
    concreteDashiToTheoryCharacterTransportPaidHere : Bool
    actualHZetaSameObjectInhabitedHere : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true
  (LiteralCharacter.all1594323HeisenbergCoordinatesClassified
    LiteralCharacter.canonicalBoundary)
  (LiteralCharacter.literalCharacterMatchesCanonicalHeisenbergSignatureExecutable
    LiteralCharacter.canonicalBoundary)
  false false false false
