module DASHI.Moonshine.Monster3BFiniteSchrodingerProjectorIrreducibilityBidiExact where

------------------------------------------------------------------------
-- PROJECTOR-BASED IRREDUCIBILITY BIDI COLLAPSE
--
-- The repository already proves the concrete finite-Heisenberg commutant is
-- scalar and every commuting idempotent projector is zero or identity.
-- Therefore the remaining ordinary finite-dimensional attachment is exactly:
-- turn an invariant subspace into its commuting projector, and connect the two
-- projector branches back to the subspace semantics.
--
-- This owner isolates that ordinary attachment and consumes it.  It does not
-- re-prove orthogonal projection construction inside the Monster lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Extract
import DASHI.Moonshine.Monster3BFiniteSchrodingerIrreducibilityAssemblyExact as Irred
import DASHI.Moonshine.Monster3BFiniteHeisenbergProjectionNoGoExact as Projection

------------------------------------------------------------------------
-- 1. Exact ordinary attachment from subspace semantics to projector semantics.
------------------------------------------------------------------------

record InvariantSubspaceProjectorAttachment
    {Member : V.SchrodingerFunction → Set}
    (inv : V.HeisenbergInvariantSubspace Member) : Set₁ where
  field
    commutingProjection : Projection.HeisenbergCommutingProjection

    zeroProjectionContradictsNonzeroWitness :
      Projection.ProjectionIsZero commutingProjection →
      Extract.NonzeroInvariantVector inv → ⊥

    identityProjectionMakesSubspaceWhole :
      Projection.ProjectionIsIdentity commutingProjection →
      Irred.WholeSchrodingerSubspace Member
open InvariantSubspaceProjectorAttachment public

------------------------------------------------------------------------
-- 2. Existing zero/identity no-go now compiles directly to irreducibility.
------------------------------------------------------------------------

wholeFromProjectorAttachment :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    InvariantSubspaceProjectorAttachment inv →
    Extract.NonzeroInvariantVector inv →
    Irred.WholeSchrodingerSubspace Member
wholeFromProjectorAttachment inv attachment witness
  with Projection.heisenbergCommutingProjectionDichotomy
    (commutingProjection attachment)
... | inj₁ projectionZero =
  Data.Empty.⊥-elim
    (zeroProjectionContradictsNonzeroWitness attachment projectionZero witness)
... | inj₂ projectionIdentity =
  identityProjectionMakesSubspaceWhole attachment projectionIdentity

------------------------------------------------------------------------
-- 3. Package the ordinary machinery once, rather than per invariant subspace.
------------------------------------------------------------------------

record ExistingFiniteProjectorMachinery : Set₁ where
  field
    attachProjector :
      ∀ {Member}
        (inv : V.HeisenbergInvariantSubspace Member) →
        InvariantSubspaceProjectorAttachment inv
open ExistingFiniteProjectorMachinery public

record ProjectorSchrodingerIrreducibilityReceipt : Set₁ where
  constructor projector-schrodinger-irreducibility-receipt
  field
    projectorMachinery : ExistingFiniteProjectorMachinery
    everyNonzeroInvariantSubspaceIsWhole :
      ∀ {Member}
        (inv : V.HeisenbergInvariantSubspace Member) →
        Extract.NonzeroInvariantVector inv →
        Irred.WholeSchrodingerSubspace Member
open ProjectorSchrodingerIrreducibilityReceipt public

assembleProjectorSchrodingerIrreducibility :
  ExistingFiniteProjectorMachinery → ProjectorSchrodingerIrreducibilityReceipt
assembleProjectorSchrodingerIrreducibility machinery =
  projector-schrodinger-irreducibility-receipt machinery
    (λ inv witness →
      wholeFromProjectorAttachment inv (attachProjector machinery inv) witness)

record ProjectorIrreducibilityBoundary : Set where
  constructor projector-irreducibility-boundary
  field
    scalarCommutantConsumed : Bool
    commutingProjectorDichotomyConsumed : Bool
    ordinarySubspaceProjectorAttachmentSeparated : Bool
    explicit729TermEnumerationRequired : Bool
    MonsterConstituentIdentificationProvedHere : Bool
open ProjectorIrreducibilityBoundary public

canonicalProjectorIrreducibilityBoundary : ProjectorIrreducibilityBoundary
canonicalProjectorIrreducibilityBoundary =
  projector-irreducibility-boundary true true true false false
