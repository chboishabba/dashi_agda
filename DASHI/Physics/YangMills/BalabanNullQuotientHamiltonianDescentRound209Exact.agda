{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanNullQuotientHamiltonianDescentRound209Exact where

------------------------------------------------------------------------
-- ROUND209 BIDI: HAMILTONIAN DESCENT THROUGH THE MEASURE NULL RELATION.
--
-- R205 now supplies an actual equivalence relation `NullEquivalent` and proves
-- that the finite-measure pairing is congruent under replacement of either
-- argument by a null-equivalent representative.  Therefore the quotient-stage
-- operator obligation is no longer an opaque Hilbert-space theorem:
--
--   H must preserve NullEquivalent.
--
-- Once that holds, both the operator action and R206 symmetry statement are
-- representative-independent.  Completion, domain closure and self-adjointness
-- remain genuinely analytic later steps.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205

record NullRespectingWavefunctionOperator
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (Measure : Set)
    (semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure) : Set₁ where
  field
    operator : R202.GaugeInvariantWavefunctionOperator group base

    preservesNull : ∀ {left right} →
      R205.NullEquivalent semantics left right →
      R205.NullEquivalent semantics
        (R202.act operator left)
        (R202.act operator right)

open NullRespectingWavefunctionOperator public

-- This is the constructive quotient-descent receipt: the action on an
-- equivalence class is independent of the chosen representative.
nullQuotientOperatorWellDefined :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    (dataSet : NullRespectingWavefunctionOperator group base Measure semantics)
    {left right} →
  R205.NullEquivalent semantics left right →
  R205.NullEquivalent semantics
    (R202.act (operator dataSet) left)
    (R202.act (operator dataSet) right)
nullQuotientOperatorWellDefined dataSet = preservesNull dataSet

-- Pairings with the descended output are likewise representative-independent
-- in the input wavefunction by R205's quotient congruence.
operatorPairingCongruentInInput :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    (dataSet : NullRespectingWavefunctionOperator group base Measure semantics)
    {left left'} →
  R205.NullEquivalent semantics left left' →
  ∀ right →
  R205.finiteMeasureWavefunctionPairing semantics
    (R202.act (operator dataSet) left) right
  ≡ R205.finiteMeasureWavefunctionPairing semantics
      (R202.act (operator dataSet) left') right
operatorPairingCongruentInInput dataSet nullProof right =
  R205.finiteMeasureWavefunctionPairingCongruentLeft _
    (preservesNull dataSet nullProof) right

nullQuotientHamiltonianDescentRound209Level : ProofLevel
nullQuotientHamiltonianDescentRound209Level = machineChecked

nullQuotientPairingWellDefinedRound209Level : ProofLevel
nullQuotientPairingWellDefinedRound209Level = machineChecked

-- Physical leaf: prove the actual finite Yang-Mills Hamiltonian preserves the
-- null space of the SAME finite-measure pairing.  This must not be inferred
-- merely from sample-level symmetry.
literalFiniteYMHamiltonianPreservesMeasureNullRound209Level : ProofLevel
literalFiniteYMHamiltonianPreservesMeasureNullRound209Level = conditional

-- Even after quotient descent, completion/domain/closure and self-adjointness
-- remain separate analytic obligations.
literalNullQuotientL2CompletionAndSelfAdjointnessRound209Level : ProofLevel
literalNullQuotientL2CompletionAndSelfAdjointnessRound209Level = conditional
