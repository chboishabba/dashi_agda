module DASHI.Wikimedia.IbrahimMonster3BCyclotomicScalarExtensionInteropExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger

------------------------------------------------------------------------
-- EXACT Q(zeta_3) -> ALGEBRAICALLY CLOSED CHARACTERISTIC-ZERO SCALAR EXTENSION
--
-- The concrete DASHI Schrodinger model is not currently a representation over
-- an algebraically closed field: its amplitudes are exact rational-coordinate
-- elements of Q(zeta_3).  The pinned mathlib irreducible-character theorem
-- therefore cannot be consumed by a type alias.
--
-- This owner names the first transport payment exactly.  It requires an
-- injective scalar embedding preserving the cyclotomic field operations and
-- the distinguished zeta phase, followed by a pointwise extension of the
-- Schrodinger functions whose six translations and six modulations commute
-- with scalar extension.
--
-- Nothing here manufactures a Lean FDRep, character equality, irreducibility
-- transport or representation isomorphism.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Mathematical source attribution.
------------------------------------------------------------------------

washington : Attribution.AttributedSource
washington = Attribution.mkDOISource
  "Lawrence C. Washington"
  "Introduction to Cyclotomic Fields, Second Edition"
  "Springer Graduate Texts in Mathematics 83"
  "1997"
  "10.1007/978-1-4612-1934-7"
  "https://doi.org/10.1007/978-1-4612-1934-7"
  Attribution.academicArticleSource
  "primary algebraic calibration for Q(zeta_3), cyclotomic embeddings and exact field structure; not authority for DASHI-to-mathlib representation transport"
  Attribution.publicAttribution

washingtonAttribution = Snowball.canonicalSourceRoleSnowballReceipt washington

------------------------------------------------------------------------
-- 2. Exact scalar-extension contract.
------------------------------------------------------------------------

record Cyclotomic3ScalarExtension : Set₁ where
  field
    TargetScalar : Set
    targetZero : TargetScalar
    targetOne : TargetScalar
    targetZeta : TargetScalar
    addTarget : TargetScalar → TargetScalar → TargetScalar
    multiplyTarget : TargetScalar → TargetScalar → TargetScalar

    embed : C3.Cyclotomic3 → TargetScalar
    embedInjective :
      (left right : C3.Cyclotomic3) →
      embed left ≡ embed right → left ≡ right

    preservesZero : embed C3.zero ≡ targetZero
    preservesOne : embed C3.one ≡ targetOne
    preservesZeta : embed C3.zeta ≡ targetZeta

    preservesAddition :
      (left right : C3.Cyclotomic3) →
      embed (Schrodinger.addC3 left right)
      ≡ addTarget (embed left) (embed right)

    preservesMultiplication :
      (left right : C3.Cyclotomic3) →
      embed (C3.multiply left right)
      ≡ multiplyTarget (embed left) (embed right)

    targetZetaSquared :
      multiplyTarget targetZeta targetZeta
      ≡ embed C3.zetaSquared

    targetZetaCubedIsOne :
      multiplyTarget (embed C3.zetaSquared) targetZeta
      ≡ targetOne

    -- This is deliberately a semantic receipt at the Agda boundary.  The
    -- target's actual field/algebraic-closure instance must be supplied by the
    -- consuming proof assistant transport; it is not inferred from operations.
    targetAlgebraicallyClosedCharacteristicZero : Set

open Cyclotomic3ScalarExtension public

------------------------------------------------------------------------
-- 3. Extend the existing concrete Schrodinger carrier pointwise.
------------------------------------------------------------------------

record SchrodingerScalarExtensionTransport
    (extension : Cyclotomic3ScalarExtension) : Set₁ where
  field
    ExtendedSchrodingerCarrier : Set

    extendState :
      Schrodinger.SchrodingerFunction → ExtendedSchrodingerCarrier

    extendedTranslationAction :
      H.Axis6 → ExtendedSchrodingerCarrier → ExtendedSchrodingerCarrier

    extendedModulationAction :
      H.Axis6 → ExtendedSchrodingerCarrier → ExtendedSchrodingerCarrier

    translationActionPreserved :
      (axis : H.Axis6) →
      (state : Schrodinger.SchrodingerFunction) →
      extendState (Schrodinger.translationAction axis state)
      ≡ extendedTranslationAction axis (extendState state)

    modulationActionPreserved :
      (axis : H.Axis6) →
      (state : Schrodinger.SchrodingerFunction) →
      extendState (Schrodinger.modulationAction axis state)
      ≡ extendedModulationAction axis (extendState state)

    extensionInjectiveOnStates :
      (left right : Schrodinger.SchrodingerFunction) →
      extendState left ≡ extendState right →
      Schrodinger.PointwiseEqual left right

open SchrodingerScalarExtensionTransport public

------------------------------------------------------------------------
-- 4. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data ScalarExtensionCreatesFDRepCharacterTransport : Set where
data FieldEmbeddingCreatesMonsterConstituentIdentity : Set where
data PreservedGeneratorsCreateIrreducibleCharacterIso : Set where
data QidCreatesScalarExtension : Set where
data DeweyCreatesScalarExtension : Set where
data OeisCreatesScalarExtension : Set where

scalarExtensionDoesNotCreateFDRepCharacterTransport :
  ScalarExtensionCreatesFDRepCharacterTransport → ⊥
scalarExtensionDoesNotCreateFDRepCharacterTransport ()

fieldEmbeddingDoesNotCreateMonsterConstituentIdentity :
  FieldEmbeddingCreatesMonsterConstituentIdentity → ⊥
fieldEmbeddingDoesNotCreateMonsterConstituentIdentity ()

preservedGeneratorsDoNotCreateIrreducibleCharacterIso :
  PreservedGeneratorsCreateIrreducibleCharacterIso → ⊥
preservedGeneratorsDoNotCreateIrreducibleCharacterIso ()

qidDoesNotCreateScalarExtension : QidCreatesScalarExtension → ⊥
qidDoesNotCreateScalarExtension ()

deweyDoesNotCreateScalarExtension : DeweyCreatesScalarExtension → ⊥
deweyDoesNotCreateScalarExtension ()

oeisDoesNotCreateScalarExtension : OeisCreatesScalarExtension → ⊥
oeisDoesNotCreateScalarExtension ()

------------------------------------------------------------------------
-- 5. Navigation/provenance coordinates remain non-promoting.
------------------------------------------------------------------------

record CyclotomicScalarExtensionExternalCoordinates : Set where
  constructor cyclotomic-scalar-extension-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasScalarExtensionAuthority : Bool
open CyclotomicScalarExtensionExternalCoordinates public

canonicalCyclotomicScalarExtensionExternalCoordinates :
  CyclotomicScalarExtensionExternalCoordinates
canonicalCyclotomicScalarExtensionExternalCoordinates =
  cyclotomic-scalar-extension-external-coordinates
    "Q1055807"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no cyclotomic-field embedding, algebraic-closure, scalar-extension, generator-action, FDRep, character, or intertwiner authority"
    false

------------------------------------------------------------------------
-- 6. Pareto frontier.
------------------------------------------------------------------------

record CyclotomicScalarExtensionFrontier : Set where
  constructor cyclotomic-scalar-extension-frontier
  field
    exactCyclotomic3ArithmeticAlreadyOwned : Bool
    exactSchrodingerCarrierAlreadyOwned : Bool
    translationAndModulationActionsAlreadyOwned : Bool
    algebraicallyClosedTargetRequired : Bool
    exactScalarEmbeddingPaid : Bool
    schrodingerStateExtensionPaid : Bool
    translationActionExtensionPaid : Bool
    modulationActionExtensionPaid : Bool
    mathlibFDRepTransportPaid : Bool
    nextResidual : String
open CyclotomicScalarExtensionFrontier public

currentCyclotomicScalarExtensionFrontier : CyclotomicScalarExtensionFrontier
currentCyclotomicScalarExtensionFrontier =
  cyclotomic-scalar-extension-frontier
    true true true true
    false false false false false
    "construct Cyclotomic3ScalarExtension into an algebraically closed characteristic-zero target without approximating zeta_3, then construct SchrodingerScalarExtensionTransport by pointwise scalar extension and prove the six translation and six modulation actions commute with extension. After those payments, package the extended finite Heisenberg representation as the concrete mathlib FDRep consumed by DashiToMathlibCharacterDeterminationTransport and prove the cyclotomic class-character agrees with the mathlib trace. Washington DOI/QID/Dewey/OEIS coordinates and dimension 729 do not create the embedding or representation transport."
