{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact where

------------------------------------------------------------------------
-- ROUND202 BIDI CORRECTION: THE PHYSICAL HAMILTONIAN ACTS ON WAVEFUNCTIONS /
-- OBSERVABLES OVER CONFIGURATION SPACE, NOT ON GAUGE FIELDS THEMSELVES.
--
-- R196 remains the correct set-level rooted normal-form presentation of the
-- based gauge quotient.  R199-R201 used a field endomorphism U -> H(U) as the
-- Hamiltonian carrier; that is the wrong semantic type for the physical
-- Hamiltonian.  This owner supersedes that interpretation.
--
-- A physical scalar wavefunction is represented on the raw field carrier and
-- carries explicit invariance under ACTUAL based gauge-action arrows.  It can
-- then be evaluated on the R196 rooted quotient without allowing the value to
-- depend on the proof component `representativeIsRooted`.
--
-- A finite Hamiltonian is an operator on this gauge-invariant function space.
-- Since its codomain is again gauge-invariant, quotient descent is built into
-- the carrier: no field-level equation N(H(U)) = H(N(U)) is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196

RawField :
  ∀ {N : Nat} {{_ : NonZero N}} →
  Transport.GroupStructure → Set
RawField {N} group = Covariance.DirectedGaugeField4 N group

record BasedGaugeInvariantWavefunction
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N) : Set₁ where
  field
    amplitude : RawField group → ℚ

    invariantUnderBasedArrow :
      ∀ {left right}
        (arrow : Free.GaugeActionArrow group left right) →
      Free.BasedGaugeFunction group base (Free.gauge arrow) →
      amplitude left ≡ amplitude right

open BasedGaugeInvariantWavefunction public

-- Evaluate a wavefunction on the canonical rooted representative only.  The
-- wavefunction never receives the quotient record itself, so it cannot inspect
-- or depend on the rootedness proof witness.
evaluateOnRootedQuotient :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  BasedGaugeInvariantWavefunction group base →
  R196.FiniteRootedGaugeQuotientCarrier group base paths →
  ℚ
evaluateOnRootedQuotient wavefunction quotient =
  amplitude wavefunction (R196.representativeField quotient)

-- Every raw field and its R196 normalized representative have exactly the same
-- physical amplitude because R196 already supplies the actual based gauge
-- arrow between them.
normalizationEvaluationExact :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (wavefunction : BasedGaugeInvariantWavefunction group base)
    field →
  amplitude wavefunction field
  ≡ evaluateOnRootedQuotient wavefunction
      (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)
normalizationEvaluationExact
    {group = group} {base = base} {paths = paths}
    wavefunction field =
  invariantUnderBasedArrow wavefunction
    (R196.normalizationGaugeArrow group base paths field)
    (R196.normalizationGaugeArrowIsBased group base paths field)

-- Correct finite Hamiltonian carrier: an operator on gauge-invariant
-- wavefunctions.  Additional analytic structure (domain, inner product,
-- symmetry, closability/self-adjointness) belongs on top of this carrier.
record GaugeInvariantWavefunctionOperator
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N) : Set₁ where
  field
    act :
      BasedGaugeInvariantWavefunction group base →
      BasedGaugeInvariantWavefunction group base

open GaugeInvariantWavefunctionOperator public

-- Quotient descent is automatic at the evaluation level because `act` returns
-- another gauge-invariant wavefunction.  No endomorphism of gauge fields is
-- involved.
operatorNormalizationHandoff :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    (operator : GaugeInvariantWavefunctionOperator group base)
    (wavefunction : BasedGaugeInvariantWavefunction group base)
    field →
  amplitude (act operator wavefunction) field
  ≡ evaluateOnRootedQuotient (act operator wavefunction)
      (R196.normalizeToFiniteRootedGaugeQuotient group base paths field)
operatorNormalizationHandoff operator wavefunction =
  normalizationEvaluationExact (act operator wavefunction)

-- The quotient-facing operator is therefore simply evaluation of the physical
-- function-space operator on the canonical representative.
rootedQuotientOperatorEvaluation :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base} →
  GaugeInvariantWavefunctionOperator group base →
  BasedGaugeInvariantWavefunction group base →
  R196.FiniteRootedGaugeQuotientCarrier group base paths →
  ℚ
rootedQuotientOperatorEvaluation operator wavefunction quotient =
  evaluateOnRootedQuotient (act operator wavefunction) quotient

basedGaugeInvariantWavefunctionCarrierRound202Level : ProofLevel
basedGaugeInvariantWavefunctionCarrierRound202Level = machineChecked

rootedQuotientWavefunctionEvaluationRound202Level : ProofLevel
rootedQuotientWavefunctionEvaluationRound202Level = machineChecked

wavefunctionHamiltonianNormalizationHandoffRound202Level : ProofLevel
wavefunctionHamiltonianNormalizationHandoffRound202Level = machineChecked

-- Correct surviving physical leaves.
literalPhysicalGaugeInvariantL2MeasureRound202Level : ProofLevel
literalPhysicalGaugeInvariantL2MeasureRound202Level = conditional

literalFiniteYMHamiltonianOnGaugeInvariantWavefunctionsRound202Level : ProofLevel
literalFiniteYMHamiltonianOnGaugeInvariantWavefunctionsRound202Level = conditional

literalFiniteYMHamiltonianSymmetricSelfAdjointRound202Level : ProofLevel
literalFiniteYMHamiltonianSymmetricSelfAdjointRound202Level = conditional
