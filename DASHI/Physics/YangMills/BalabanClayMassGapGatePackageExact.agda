module DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Bridge sources:
-- Tosio Kato, Perturbation Theory for Linear Operators,
-- DOI 10.1007/978-3-642-66282-9.
-- Konrad Osterwalder and Robert Schrader, Axioms for Euclidean Green's
-- Functions I/II, DOI 10.1007/BF01645738 and 10.1007/BF01608978.
-- Umberto Mosco, Convergence of Convex Sets and of Solutions of Variational
-- Inequalities, DOI 10.1016/0001-8708(69)90009-7.
-- Kazuhiro Kuwae and Takashi Shioya, Convergence of Spectral Structures,
-- DOI 10.4310/cag.2003.v11.n4.a1.
--
-- M7 is kept source-honest:
--   M7a action variation = physical H_YM is a same-object identification;
--   M7b/M7c now prefer the Kato closed-form route, where a densely-defined
--     closed semibounded physical YM form produces its associated domain and
--     self-adjoint operator together;
--   the selected common invariant operator core remains a separate payment.
--
-- The finite P33 lane now separately owns a literal projected operator
-- H_P = PMP whose projector-image domain is invariant, whose matrix
-- representative is symmetric whenever M is symmetric, and whose physical
-- projector image inherits the exact 1/32 P33 quadratic floor whenever the
-- supplied literal physical Hessian carries the existing matrix-coercivity
-- certificate. This is a genuine finite precursor, not continuum M7b/M7c.
--
-- The gauge-invariant L2 subspace is the selected carrier route.  A separate
-- quotient of configuration space by gauge orbits is not a mandatory M7
-- payment on this route.

import DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact
import DASHI.Physics.YangMills.BalabanClayObservableGapEdgeExact
import DASHI.Physics.YangMills.BalabanClaySpectralUVCompatibilityExact
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato
import DASHI.Physics.YangMills.BalabanP33ProjectedHamiltonianDomainExact as P33Projected

infixr 4 _or_
data _or_ (A B : Set) : Set where
  leftRoute : A → A or B
  rightRoute : B → A or B

record ClayMassGapGatePropositions : Set₁ where
  field
    M1PhysicalScaleClustering : Set
    M2DenseCoreSpectralExclusion : Set
    M3LocalNoncollapse : Set
    M4ExactOSPullback : Set
    M4TransferIntertwining : Set
    M5ObservableDetectsGapEdge : Set
    M6SpectralUVCompatibility : Set

    M7aPhysicalActionVariationHamiltonianSameObject : Set
    M7bHamiltonianDomainCommonInvariantDenseCore : Set
    M7cSelfAdjointSelectedYMForm : Set

    M8YMOSGeneratorEvolutionIdentification : Set
    M9PhysicalVacuumRecoverySystem : Set

open ClayMassGapGatePropositions public

record MandatoryClayMassGapGates
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    m1 : M1PhysicalScaleClustering gates
    m2 : M2DenseCoreSpectralExclusion gates
    m3 : M3LocalNoncollapse gates
    m4 : M4ExactOSPullback gates or M4TransferIntertwining gates
    m6 : M6SpectralUVCompatibility gates
    m7a : M7aPhysicalActionVariationHamiltonianSameObject gates
    m7b : M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7c : M7cSelfAdjointSelectedYMForm gates
    m8 : M8YMOSGeneratorEvolutionIdentification gates
    m9 : M9PhysicalVacuumRecoverySystem gates

open MandatoryClayMassGapGates public

record SharpMassIdentification
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    mandatory : MandatoryClayMassGapGates gates
    m5 : M5ObservableDetectsGapEdge gates

open SharpMassIdentification public

assembleMandatoryClayMassGapGates :
  ∀ gates →
  M1PhysicalScaleClustering gates →
  M2DenseCoreSpectralExclusion gates →
  M3LocalNoncollapse gates →
  (M4ExactOSPullback gates or M4TransferIntertwining gates) →
  M6SpectralUVCompatibility gates →
  M7aPhysicalActionVariationHamiltonianSameObject gates →
  M7bHamiltonianDomainCommonInvariantDenseCore gates →
  M7cSelfAdjointSelectedYMForm gates →
  M8YMOSGeneratorEvolutionIdentification gates →
  M9PhysicalVacuumRecoverySystem gates →
  MandatoryClayMassGapGates gates
assembleMandatoryClayMassGapGates
    gates gate1 gate2 gate3 gate4 gate6 gate7a gate7b gate7c gate8 gate9 = record
  { m1 = gate1
  ; m2 = gate2
  ; m3 = gate3
  ; m4 = gate4
  ; m6 = gate6
  ; m7a = gate7a
  ; m7b = gate7b
  ; m7c = gate7c
  ; m8 = gate8
  ; m9 = gate9
  }

addOptionalSpectralEdgeIdentification :
  ∀ {gates} →
  MandatoryClayMassGapGates gates →
  M5ObservableDetectsGapEdge gates →
  SharpMassIdentification gates
addOptionalSpectralEdgeIdentification mandatoryGates gate5 = record
  { mandatory = mandatoryGates
  ; m5 = gate5
  }

------------------------------------------------------------------------
-- Cross-prover prerequisites already paid.
------------------------------------------------------------------------

generatorUniquenessCompilerClosed :
  Frontier.generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
generatorUniquenessCompilerClosed = refl

vacuumRecoveryGapCompilerClosed :
  Frontier.vacuumOrthogonalRecoveryGapCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
vacuumRecoveryGapCompilerClosed = refl

denseCoreSpectralExclusionCompilerClosed :
  Frontier.denseCoreSpectralExclusionCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
denseCoreSpectralExclusionCompilerClosed = refl

gaugeInvariantSubspaceCarrierSelected :
  Frontier.gaugeInvariantSubspaceCarrierRouteSelected
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
gaugeInvariantSubspaceCarrierSelected = refl

gaugeOrbitConfigurationQuotientNotRequiredForSelectedCarrier :
  Frontier.gaugeOrbitConfigurationQuotientRequiredForSelectedCarrier
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
gaugeOrbitConfigurationQuotientNotRequiredForSelectedCarrier = refl

finiteSelectedHodgeVariationPairingClosed :
  Frontier.finiteSelectedHodgeVariationPairingClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
finiteSelectedHodgeVariationPairingClosed = refl

------------------------------------------------------------------------
-- New finite P33 operator/domain precursor.
------------------------------------------------------------------------

p33FiniteProjectedHamiltonianInvariantDomainLevel : ProofLevel
p33FiniteProjectedHamiltonianInvariantDomainLevel =
  P33Projected.p33ProjectedHamiltonianInvariantDomainLevel

p33FiniteProjectedHamiltonianMatrixRepresentationLevel : ProofLevel
p33FiniteProjectedHamiltonianMatrixRepresentationLevel =
  P33Projected.p33ProjectedHamiltonianMatrixRepresentationLevel

p33FiniteProjectedHamiltonianSymmetryLevel : ProofLevel
p33FiniteProjectedHamiltonianSymmetryLevel =
  P33Projected.p33ProjectedHamiltonianFiniteSymmetryLevel

p33FiniteProjectedHamiltonianPhysicalFloorLevel : ProofLevel
p33FiniteProjectedHamiltonianPhysicalFloorLevel =
  P33Projected.p33ProjectedHamiltonianPhysicalFloorLevel

p33FiniteProjectedHamiltonianCoerciveClosureLevel : ProofLevel
p33FiniteProjectedHamiltonianCoerciveClosureLevel =
  P33Projected.p33ProjectedHamiltonianCoerciveClosureLevel

-- Scheduling consequence:
-- the finite P33 carrier no longer needs separate proofs that the projected
-- operator preserves the projector-image physical domain, that its literal
-- PMP representative is symmetric, or that an already-coercive literal
-- physical Hessian keeps its 1/32 floor after restricting to im(P). Those are
-- now one compiler package. The remaining M7 work is continuum/analytic and
-- the actual concrete PhysicalSU2MatrixHessian producer.

------------------------------------------------------------------------
-- Preferred Kato M7b/M7c compiler.
------------------------------------------------------------------------

M7PhysicalClosedSemiboundedFormInput : Set → Set → Set₁
M7PhysicalClosedSemiboundedFormInput = Kato.PhysicalYMClosedFormInput

M7KatoRepresentationAuthority : Set → Set → Set₁
M7KatoRepresentationAuthority = Kato.KatoFirstRepresentationAuthority

M7AssociatedSelfAdjointOperator :
  ∀ {Hilbert Scalar} →
  Kato.ClosedSemiboundedFormData Hilbert Scalar → Set₁
M7AssociatedSelfAdjointOperator = Kato.AssociatedSelfAdjointOperator

M7CommonInvariantOperatorCore :
  ∀ {Hilbert Scalar}
    {formData : Kato.ClosedSemiboundedFormData Hilbert Scalar} →
  Kato.AssociatedSelfAdjointOperator formData → Set₁
M7CommonInvariantOperatorCore = Kato.CommonInvariantOperatorCore

katoDomainAndSelfAdjointCompilerLevel : ProofLevel
katoDomainAndSelfAdjointCompilerLevel =
  Kato.katoClosedFormHamiltonianCompilerLevel

katoRepresentationAuthorityLevel : ProofLevel
katoRepresentationAuthorityLevel =
  Kato.katoFirstRepresentationTheoremAuthorityLevel

-- Consequence for scheduling:
-- M7b's operator-domain coordinate and M7c self-adjointness are not two
-- independent analytic producers on the preferred route.  They are joint
-- outputs of the Kato representation theorem once the physical closed form is
-- supplied.  The common invariant operator core is deliberately NOT output by
-- this compiler.

------------------------------------------------------------------------
-- Exact M7 physical frontier.
------------------------------------------------------------------------

m7aPhysicalActionVariationHamiltonianSameObjectStillOpen :
  Frontier.physicalActionVariationHamiltonianSameObjectClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7aPhysicalActionVariationHamiltonianSameObjectStillOpen = refl

m7bPartialDomainHamiltonianStillOpen :
  Frontier.genuinePartialDomainHamiltonianFormalized
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7bPartialDomainHamiltonianStillOpen = refl

m7bCommonInvariantDenseCoreStillOpen :
  Frontier.commonInvariantDensePhysicalCoreConstructed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7bCommonInvariantDenseCoreStillOpen = refl

m7cSelfAdjointSelectedYMFormStillOpen :
  Frontier.physicalSelfAdjointSelectedYMFormClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7cSelfAdjointSelectedYMFormStillOpen = refl

literalM7PhysicalClosedSemiboundedFormLevel : ProofLevel
literalM7PhysicalClosedSemiboundedFormLevel =
  Kato.literalPhysicalYMClosedSemiboundedFormLevel

literalM7CommonInvariantCoreLevel : ProofLevel
literalM7CommonInvariantCoreLevel =
  Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

massGapGateSeparationLevel : ProofLevel
massGapGateSeparationLevel = machineChecked

physicalGateProducersLevel : ProofLevel
physicalGateProducersLevel = conditional
