{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionSymmetricOperatorRound204Exact where

------------------------------------------------------------------------
-- ROUND204 BIDI: THE FINITE SYMMETRY PAYMENT ON THE CORRECT HAMILTONIAN TYPE.
--
-- R202: H acts on gauge-invariant wavefunctions.
-- R203: those wavefunctions already inherit R197's exact finite rooted pairing.
--
-- Consequently quotient descent is no longer a separate hypothesis in the
-- finite symmetry theorem.  The only operator-theoretic payment at this layer
-- is the literal pairing identity
--
--   <H f , g> = <f , H g>.
--
-- This record is theorem-bearing rather than a Bool ledger.  It does not invent
-- the physical Yang-Mills H or infer continuum self-adjointness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact as Rooted
import DASHI.Physics.YangMills.BalabanFiniteRootedGaugeQuotientL2Round197Exact as R197
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact as R203

record FiniteSymmetricGaugeInvariantOperator
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : Rooted.RootedPathSystem base)
    (ensemble : R197.FiniteRootedQuotientEnsemble group base paths) : Set₁ where
  field
    operator : R202.GaugeInvariantWavefunctionOperator group base

    symmetric :
      ∀ left right →
      R203.finiteWavefunctionPairing ensemble
        (R202.act operator left) right
      ≡ R203.finiteWavefunctionPairing ensemble
          left (R202.act operator right)

open FiniteSymmetricGaugeInvariantOperator public

-- Gauge quotient compatibility is automatic because the operator codomain is
-- already a gauge-invariant wavefunction.  This theorem makes the exact
-- dependency reduction explicit for downstream consumers.
symmetricOperatorNormalizationHandoff :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : Rooted.RootedPathSystem base}
    {ensemble : R197.FiniteRootedQuotientEnsemble group base paths}
    (symmetricOperator :
      FiniteSymmetricGaugeInvariantOperator group base paths ensemble)
    wavefunction field →
  R202.amplitude
    (R202.act (operator symmetricOperator) wavefunction) field
  ≡ R202.evaluateOnRootedQuotient
      (R202.act (operator symmetricOperator) wavefunction)
      (DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact.normalizeToFiniteRootedGaugeQuotient
        group base paths field)
symmetricOperatorNormalizationHandoff symmetricOperator wavefunction =
  R202.operatorNormalizationHandoff (operator symmetricOperator) wavefunction

finiteSymmetricGaugeInvariantOperatorRound204Level : ProofLevel
finiteSymmetricGaugeInvariantOperatorRound204Level = machineChecked

-- Exact surviving producer wall: construct the literal finite Yang-Mills
-- Hamiltonian on this carrier and prove the `symmetric` field from its physical
-- integration-by-parts/boundary law.
literalFiniteYMHamiltonianProducerRound204Level : ProofLevel
literalFiniteYMHamiltonianProducerRound204Level = conditional

literalFiniteYMHamiltonianSymmetryRound204Level : ProofLevel
literalFiniteYMHamiltonianSymmetryRound204Level = conditional

literalPhysicalGaugeInvariantL2CompletionRound204Level : ProofLevel
literalPhysicalGaugeInvariantL2CompletionRound204Level = conditional
