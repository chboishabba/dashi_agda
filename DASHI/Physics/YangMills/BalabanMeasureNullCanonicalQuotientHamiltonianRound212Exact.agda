{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanMeasureNullCanonicalQuotientHamiltonianRound212Exact where

------------------------------------------------------------------------
-- ROUND212 BIDI: CANONICAL MEASURE-NULL QUOTIENT -> DESCENDED HAMILTONIAN.
--
-- `DASHI.Geometry.UniversalCanonicalQuotient` already proves this pattern for
-- Set-level carriers.  R202 wavefunctions are proof-bearing and live in Set₁,
-- so this module lifts the same chosen-section argument one universe without
-- adding any new quotient mathematics.
--
-- Given a canonical quotient presentation whose equivalence is exactly the
-- R205 measure-null relation, and an R209 operator preserving that relation,
-- the map
--
--        psi |-> pi (H psi)
--
-- is invariant.  Hence H descends to a unique pointwise operator on the null
-- quotient.  Completion/domain/self-adjointness remain later analytic steps.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205
import DASHI.Physics.YangMills.BalabanNullQuotientHamiltonianDescentRound209Exact as R209

record CanonicalMeasureNullQuotient
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (Measure : Set)
    (semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure)
    (Q : Set₁) : Set₂ where
  field
    project : R202.BasedGaugeInvariantWavefunction group base → Q
    section : Q → R202.BasedGaugeInvariantWavefunction group base

    retract : ∀ q → project (section q) ≡ q

    nullSound : ∀ {left right} →
      R205.NullEquivalent semantics left right →
      project left ≡ project right

    nullComplete : ∀ {left right} →
      project left ≡ project right →
      R205.NullEquivalent semantics left right

    canonical : ∀ wavefunction →
      R205.NullEquivalent semantics
        wavefunction (section (project wavefunction))

open CanonicalMeasureNullQuotient public

descendedHamiltonian :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    {Q : Set₁} →
  CanonicalMeasureNullQuotient group base Measure semantics Q →
  R209.NullRespectingWavefunctionOperator group base Measure semantics →
  Q → Q
descendedHamiltonian quotient operatorData q =
  project quotient
    (R202.act (R209.operator operatorData) (section quotient q))

hamiltonianQuotientSquareCommutes :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    {Q : Set₁}
    (quotient : CanonicalMeasureNullQuotient group base Measure semantics Q)
    (operatorData :
      R209.NullRespectingWavefunctionOperator group base Measure semantics)
    wavefunction →
  descendedHamiltonian quotient operatorData (project quotient wavefunction)
  ≡ project quotient (R202.act (R209.operator operatorData) wavefunction)
hamiltonianQuotientSquareCommutes quotient operatorData wavefunction =
  nullSound quotient
    (R209.preservesNull operatorData
      (R205.nullSymmetric _ (canonical quotient wavefunction)))

-- Pointwise uniqueness of the descended action; no function extensionality is
-- required. Any quotient operator commuting with the raw H action must agree
-- with the canonical descended operator on every quotient point.
descendedHamiltonianUnique :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    {Q : Set₁}
    (quotient : CanonicalMeasureNullQuotient group base Measure semantics Q)
    (operatorData :
      R209.NullRespectingWavefunctionOperator group base Measure semantics)
    (candidate : Q → Q) →
  (∀ wavefunction →
    candidate (project quotient wavefunction)
    ≡ project quotient (R202.act (R209.operator operatorData) wavefunction)) →
  ∀ q → candidate q ≡ descendedHamiltonian quotient operatorData q
descendedHamiltonianUnique quotient operatorData candidate commutes q
  rewrite retract quotient q = commutes (section quotient q)

measureNullCanonicalQuotientHamiltonianRound212Level : ProofLevel
measureNullCanonicalQuotientHamiltonianRound212Level = machineChecked

measureNullQuotientHamiltonianUniqueRound212Level : ProofLevel
measureNullQuotientHamiltonianUniqueRound212Level = machineChecked

-- Physical same-object leaf: inhabit the canonical quotient presentation for
-- the literal finite Balaban measure semantics from R205. Once present, R209's
-- null-preserving physical H descends automatically by the theorem above.
literalBalabanMeasureNullCanonicalQuotientRound212Level : ProofLevel
literalBalabanMeasureNullCanonicalQuotientRound212Level = conditional

-- Completion and the unbounded/domain/self-adjoint operator theory remain
-- separate. A quotient presentation alone is not a Hilbert completion.
literalBalabanNullQuotientHilbertCompletionRound212Level : ProofLevel
literalBalabanNullQuotientHilbertCompletionRound212Level = conditional
