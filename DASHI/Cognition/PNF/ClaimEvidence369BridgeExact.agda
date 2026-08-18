module DASHI.Cognition.PNF.ClaimEvidence369BridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Cognition.PNF.EvidenceHorizon369 as Horizon
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.DialecticInvariantGeometry as Dialectic

------------------------------------------------------------------------
-- Dialectic / PNF / 369 cross-pollination.
--
-- A DialecticField already supplies two independent Boolean predicates.
-- Pointwise, that is exactly the support-square shape.  The 369/TriTruth lane
-- remains a coarser projection: its residual projection is proven incapable of
-- emitting the explicit contradiction residual.  Contradiction therefore has
-- to be retained in the fine claim/evidence fibre rather than manufactured by
-- the ternary presentation.
------------------------------------------------------------------------

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

dialecticPolarity :
  ∀ {X} →
  Dialectic.DialecticField X →
  X →
  Four.PolarAssessment
dialecticPolarity field x =
  Four.assess
    (Dialectic.thesis field x)
    (Dialectic.antithesis field x)

dialecticSupportIsThesis :
  ∀ {X} (field : Dialectic.DialecticField X) x →
  Four.supportsP (dialecticPolarity field x)
  ≡ Dialectic.thesis field x
dialecticSupportIsThesis field x = refl

dialecticRefutationIsAntithesis :
  ∀ {X} (field : Dialectic.DialecticField X) x →
  Four.supportsNotP (dialecticPolarity field x)
  ≡ Dialectic.antithesis field x
dialecticRefutationIsAntithesis field x = refl

dialectic369Residual :
  ∀ {X} →
  Dialectic.DialecticField X →
  X →
  Residual.ResidualLevel
dialectic369Residual field x =
  Tetralemma.triResidual
    (Tetralemma.tetralemmaTone
      (Four.polarPosition (dialecticPolarity field x)))

dialectic369ProjectionCannotEmitContradiction :
  ∀ {X} (field : Dialectic.DialecticField X) x →
  dialectic369Residual field x ≢ Residual.contradiction
dialectic369ProjectionCannotEmitContradiction field x =
  Tetralemma.triResidual-excludes-contradiction
    (Tetralemma.tetralemmaTone
      (Four.polarPosition (dialecticPolarity field x)))

------------------------------------------------------------------------
-- The H3/H6/H9 evidence horizon already carries fine signed evidence and
-- explicitly proves that omission is not refutation.  This bridge records the
-- corresponding support-square discipline without replacing signed evidence.
------------------------------------------------------------------------

record ClaimEvidence369Boundary : Set where
  field
    dialecticRetainsTwoIndependentPolarities : Bool
    supportSquareReplacesSignedEvidenceClaimed : Bool
    omittedHorizonCoordinateMeansRefutationClaimed : Bool
    ternaryProjectionManufacturesContradictionClaimed : Bool
    claimIndexedPoolingRequired : Bool

canonicalClaimEvidence369Boundary : ClaimEvidence369Boundary
canonicalClaimEvidence369Boundary = record
  { dialecticRetainsTwoIndependentPolarities = true
  ; supportSquareReplacesSignedEvidenceClaimed = false
  ; omittedHorizonCoordinateMeansRefutationClaimed = false
  ; ternaryProjectionManufacturesContradictionClaimed = false
  ; claimIndexedPoolingRequired = true
  }

horizonOmissionStillCannotRefute :
  Horizon.HorizonOmissionRefutationPermission Horizon.horizonProjectionOnly → ⊥
horizonOmissionStillCannotRefute = Horizon.horizonProjectionCannotRefute

claimIndexedBoundaryReused :
  Indexed.ClaimIndexedEvidencePolarityBoundary
claimIndexedBoundaryReused = Indexed.canonicalClaimIndexedEvidencePolarityBoundary
