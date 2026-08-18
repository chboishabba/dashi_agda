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
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens

------------------------------------------------------------------------
-- Dialectic / PNF / 369 cross-pollination.
--
-- A DialecticField supplies two independent Boolean predicates: thesis and
-- antithesis. Pointwise that has the same TWO-BIT SHAPE as PolarAssessment,
-- but the second bit is only "antithesis present". It is not definitionally
-- logical negation, algebraic inverse, orientation reversal, or any particular
-- contextual counterposition. RelationalLensSynthesisCore already separates
-- those operator roles.
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

dialecticCounterSupportIsAntithesis :
  ∀ {X} (field : Dialectic.DialecticField X) x →
  Four.supportsNotP (dialecticPolarity field x)
  ≡ Dialectic.antithesis field x
dialecticCounterSupportIsAntithesis field x = refl

-- The field name `supportsNotP` comes from the reused two-bit carrier; this
-- theorem records that the dialectic antithesis coordinate is not thereby
-- qualified as classical logical negation.
contextualCounterpositionStillNotLogicalNegation :
  Lens.contextualCounterpositionRole ≡ Lens.logicalNegationRole → ⊥
contextualCounterpositionStillNotLogicalNegation =
  Lens.contextualCounterpositionIsNotLogicalNegationByRole

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
-- corresponding two-coordinate discipline without replacing signed evidence.
------------------------------------------------------------------------

record ClaimEvidence369Boundary : Set where
  field
    dialecticRetainsTwoIndependentPolarities : Bool
    antithesisAutomaticallyMeansLogicalNegationClaimed : Bool
    supportSquareReplacesSignedEvidenceClaimed : Bool
    omittedHorizonCoordinateMeansRefutationClaimed : Bool
    ternaryProjectionManufacturesContradictionClaimed : Bool
    claimOperatorContextIndexedPoolingRequired : Bool

canonicalClaimEvidence369Boundary : ClaimEvidence369Boundary
canonicalClaimEvidence369Boundary = record
  { dialecticRetainsTwoIndependentPolarities = true
  ; antithesisAutomaticallyMeansLogicalNegationClaimed = false
  ; supportSquareReplacesSignedEvidenceClaimed = false
  ; omittedHorizonCoordinateMeansRefutationClaimed = false
  ; ternaryProjectionManufacturesContradictionClaimed = false
  ; claimOperatorContextIndexedPoolingRequired = true
  }

horizonOmissionStillCannotRefute :
  Horizon.HorizonOmissionRefutationPermission Horizon.horizonProjectionOnly → ⊥
horizonOmissionStillCannotRefute = Horizon.horizonProjectionCannotRefute

claimIndexedBoundaryReused :
  Indexed.ClaimIndexedEvidencePolarityBoundary
claimIndexedBoundaryReused = Indexed.canonicalClaimIndexedEvidencePolarityBoundary
