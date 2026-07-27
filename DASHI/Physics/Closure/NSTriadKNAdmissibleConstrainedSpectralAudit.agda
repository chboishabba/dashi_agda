module DASHI.Physics.Closure.NSTriadKNAdmissibleConstrainedSpectralAudit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNVariationalRigidityOperatorRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNShellScaleHeadroom as ScaleHeadroom

------------------------------------------------------------------------
-- Admissibility-constrained generalized spectral audit.
--
-- The previous variational/rigidity/operator modules expose all proof shapes,
-- but the current canonical carrier remembers only one natural number: total
-- residue energy.  It therefore cannot express divergence-free, gauge, phase,
-- parity, or triad-incidence constraints.  This module separates the two facts:
--
--   * on a richer carrier, excluding every rigid equality direction gives a
--     genuine quantitative gap;
--   * on the current energy-only carrier, the exported Stage-3 surrogate is the
--     identity and the unit-energy state has generalized eigenvalue exactly one.
------------------------------------------------------------------------

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

------------------------------------------------------------------------
-- Finite constrained Rayleigh certificate.
--
-- `Code` is the finite normal-form index used for an executable/offline audit.
-- No division is used: the generalized eigenvalue bound is represented by the
-- cross-multiplied inequalities needed by the q-gap implementation.
------------------------------------------------------------------------

record ConstrainedGeneralizedEigenvalueCertificate {ℓ : Level}
    (Carrier : Set ℓ)
    (admissible normalized : Carrier → Set)
    (qBase qError strongNormSquared : Carrier → Nat) : Set (lsuc ℓ) where
  constructor mkConstrainedGeneralizedEigenvalueCertificate
  field
    Code : Set
    encode : Carrier → Code
    decode : Code → Carrier

    admissibleNormalizedRetract :
      (x : Carrier) → admissible x → normalized x → decode (encode x) ≡ x

    baseConstant : Nat
    errorConstant : Nat
    baseConstantPositive : zero < baseConstant
    errorConstantStrictlyBelowBase : errorConstant < baseConstant

    constrainedBaseRayleigh :
      (x : Carrier) → admissible x → normalized x →
      baseConstant * strongNormSquared x ≤ four * qBase x

    constrainedOperatorEstimate :
      (x : Carrier) → admissible x → normalized x →
      four * qError x ≤ errorConstant * strongNormSquared x

open ConstrainedGeneralizedEigenvalueCertificate public

------------------------------------------------------------------------
-- Rigid equality-direction exclusion.
------------------------------------------------------------------------

record AdmissibleRigidExclusion {ℓ : Level}
    (Carrier : Set ℓ)
    (admissible normalized rigid : Carrier → Set) : Set (lsuc ℓ) where
  constructor mkAdmissibleRigidExclusion
  field
    rigidDirectionsExcluded :
      (x : Carrier) → admissible x → normalized x → ¬ rigid x

open AdmissibleRigidExclusion public

admissibleRigidityGapWitness :
  {Carrier : Set} →
  {admissible normalized rigid : Carrier → Set} →
  {qBase qError strongNormSquared : Carrier → Nat} →
  (gap : Refinement.QuantitativeRigidityGap
    Carrier normalized rigid qBase qError strongNormSquared) →
  (exclusion : AdmissibleRigidExclusion
    Carrier admissible normalized rigid) →
  (x : Carrier) → admissible x → normalized x →
  qError x
    + Refinement.QuantitativeRigidityGap.defectConstant gap
      * strongNormSquared x
    ≤ qBase x
admissibleRigidityGapWitness gap exclusion x admissibleX normalizedX =
  Refinement.rigidityGapWitness gap x normalizedX
    (rigidDirectionsExcluded exclusion x admissibleX normalizedX)

------------------------------------------------------------------------
-- Rich-carrier handoff.
--
-- This is the exact input still missing from the active NS chain.  It requires a
-- carrier that retains the data on which physical admissibility acts and a map to
-- the legacy energy summary.  The map is deliberately not assumed injective:
-- collapsing to energy is exactly what erased the possible spectral slack.
------------------------------------------------------------------------

record AdmissibleStage3Carrier : Set₁ where
  constructor mkAdmissibleStage3Carrier
  field
    Carrier : Set
    admissible : Carrier → Set
    normalized : Carrier → Set
    rigid : Carrier → Set

    residueEnergy : Carrier → Nat
    qBase : Carrier → Nat
    qError : Carrier → Nat
    strongNormSquared : Carrier → Nat

    forgetToEnergy : Carrier → ResidueNorm.ResidueEnergyCarrier one
    forgetPreservesEnergy :
      (x : Carrier) →
      ResidueNorm.residueEnergy (forgetToEnergy x) ≡ residueEnergy x

open AdmissibleStage3Carrier public

record AdmissibleStage3SpectralGap
    (stage3 : AdmissibleStage3Carrier) : Set₁ where
  constructor mkAdmissibleStage3SpectralGap
  field
    rigidityGap :
      Refinement.QuantitativeRigidityGap
        (AdmissibleStage3Carrier.Carrier stage3)
        (AdmissibleStage3Carrier.normalized stage3)
        (AdmissibleStage3Carrier.rigid stage3)
        (AdmissibleStage3Carrier.qBase stage3)
        (AdmissibleStage3Carrier.qError stage3)
        (AdmissibleStage3Carrier.strongNormSquared stage3)

    rigidExclusion :
      AdmissibleRigidExclusion
        (AdmissibleStage3Carrier.Carrier stage3)
        (AdmissibleStage3Carrier.admissible stage3)
        (AdmissibleStage3Carrier.normalized stage3)
        (AdmissibleStage3Carrier.rigid stage3)

open AdmissibleStage3SpectralGap public

------------------------------------------------------------------------
-- Concrete audit of the currently exported canonical data.
------------------------------------------------------------------------

CanonicalCarrier : Set
CanonicalCarrier = ResidueNorm.ResidueEnergyCarrier one

canonicalNormModel : ResidueNorm.ResidueNormModel
canonicalNormModel = ResidueNorm.nWeightedResidueNormModel

canonicalKernelData :
  CrossMatrix.ProfileCrossMatrixKernelData canonicalNormModel one
canonicalKernelData =
  CrossMatrix.canonicalProfileCrossMatrixKernelData canonicalNormModel

-- The currently exported weighted-Schur operator is definitionally the identity.
-- Thus its only available quadratic form is the weak norm itself, not the actual
-- Stage-3 matrix/eigenstructure requested by the constrained spectral check.
canonicalExportedOperatorIsIdentity :
  (x : CanonicalCarrier) →
  CrossMatrix.ProfileCrossMatrixKernelData.weightedSchurOperator
    canonicalKernelData x ≡ x
canonicalExportedOperatorIsIdentity x = refl

canonicalQBase : CanonicalCarrier → Nat
canonicalQBase = ResidueNorm.residueEnergy

canonicalQError : CanonicalCarrier → Nat
canonicalQError = ResidueNorm.residueEnergy

canonicalStrongNormSquared : CanonicalCarrier → Nat
canonicalStrongNormSquared x = one * ResidueNorm.residueEnergy x

canonicalUnit : CanonicalCarrier
canonicalUnit = ResidueNorm.mkResidueEnergyCarrier one

canonicalGeneralizedEigenvalueIsOne :
  canonicalQError canonicalUnit ≡ canonicalQBase canonicalUnit
canonicalGeneralizedEigenvalueIsOne = refl

------------------------------------------------------------------------
-- Any purported physical admissibility predicate on the energy-only carrier
-- that still admits the unit-energy state retains the saturated direction.
------------------------------------------------------------------------

energyOnlyAdmissibilityRetainsSaturation :
  (Admissible : CanonicalCarrier → Set) →
  Admissible canonicalUnit →
  canonicalQError canonicalUnit ≡ canonicalQBase canonicalUnit
energyOnlyAdmissibilityRetainsSaturation Admissible admissibleUnit = refl

positiveDefectImpossibleWhenUnitAdmissible :
  (Admissible : CanonicalCarrier → Set) →
  Admissible canonicalUnit →
  (δ : Nat) → zero < δ →
  ¬ (canonicalQError canonicalUnit
      + δ * canonicalStrongNormSquared canonicalUnit
      ≤ canonicalQBase canonicalUnit)
positiveDefectImpossibleWhenUnitAdmissible
  Admissible admissibleUnit zero ()
positiveDefectImpossibleWhenUnitAdmissible
  Admissible admissibleUnit (suc δ) positive ()

------------------------------------------------------------------------
-- Audit conclusion.
------------------------------------------------------------------------

data ConstrainedSpectralAuditOutcome : Set where
  strictGapFound : ConstrainedSpectralAuditOutcome
  saturatedDirectionFound : ConstrainedSpectralAuditOutcome
  actualOperatorNotExposed : ConstrainedSpectralAuditOutcome

canonicalConstrainedSpectralAuditOutcome : ConstrainedSpectralAuditOutcome
canonicalConstrainedSpectralAuditOutcome = saturatedDirectionFound

canonicalActualStage3MatrixExposed : Bool
canonicalActualStage3MatrixExposed = false

canonicalActualStage3MatrixExposedIsFalse :
  canonicalActualStage3MatrixExposed ≡ false
canonicalActualStage3MatrixExposedIsFalse = refl

canonicalEnergyCarrierCanEncodePhysicalConstraints : Bool
canonicalEnergyCarrierCanEncodePhysicalConstraints = false

canonicalEnergyCarrierCanEncodePhysicalConstraintsIsFalse :
  canonicalEnergyCarrierCanEncodePhysicalConstraints ≡ false
canonicalEnergyCarrierCanEncodePhysicalConstraintsIsFalse = refl

constrainedSpectralAuditImplemented : Bool
constrainedSpectralAuditImplemented = true

constrainedSpectralAuditImplementedIsTrue :
  constrainedSpectralAuditImplemented ≡ true
constrainedSpectralAuditImplementedIsTrue = refl
