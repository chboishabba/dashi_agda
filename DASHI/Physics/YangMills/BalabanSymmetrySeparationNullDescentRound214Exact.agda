{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSymmetrySeparationNullDescentRound214Exact where

------------------------------------------------------------------------
-- TERMINAL ROUND214 BIDI: SYMMETRY + NULL-CLASS SEPARATION ALREADY FORCES
-- HAMILTONIAN DESCENT THROUGH THE SAME MEASURE-NULL RELATION.
--
-- R209 previously left preservation of the R205 null relation as an
-- independent physical Hamiltonian payment.  But once R206 supplies symmetry
-- on the SAME finite-measure pairing and R213 supplies separation of null
-- classes by that SAME pairing, null preservation is automatic:
--
--   left ~ right
--   => <left, H test> = <right, H test>       (R205 congruence)
--   => <H left, test> = <H right, test>       (R206 symmetry)
--   => H left ~ H right                       (R213 separation).
--
-- Thus null preservation is not a separate Yang-Mills theorem after the
-- physical IBP weld and pairing separation have been paid.  This module
-- constructs the R209 null-respecting operator directly from those two
-- receipts and therefore prunes one terminal leaf before R212 quotient descent.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeInvariantWavefunctionHamiltonianRound202Exact as R202
import DASHI.Physics.YangMills.BalabanFiniteMeasureWavefunctionL2BridgeRound205Exact as R205
import DASHI.Physics.YangMills.BalabanFiniteMeasureIBPWavefunctionSymmetryRound206Exact as R206
import DASHI.Physics.YangMills.BalabanNullQuotientHamiltonianDescentRound209Exact as R209
import DASHI.Physics.YangMills.BalabanWeakPairingSeparatesNullHamiltoniansRound213Exact as R213

symmetryAndSeparationPreserveNull :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure}
    (weld : R206.FiniteMeasureIBPWavefunctionSymmetryWeld
      group base Measure semantics)
    (separation : R213.PairingSeparatesMeasureNullClasses
      group base Measure semantics)
    {left right} →
  R205.NullEquivalent semantics left right →
  R205.NullEquivalent semantics
    (R202.act (R206.operator weld) left)
    (R202.act (R206.operator weld) right)
symmetryAndSeparationPreserveNull weld separation nullProof =
  R213.separates separation λ test →
    trans
      (R206.selectedIBPImpliesSameMeasureWavefunctionSymmetry
        weld _ test)
      (trans
        (R205.finiteMeasureWavefunctionPairingCongruentLeft
          _ nullProof (R202.act (R206.operator weld) test))
        (sym
          (R206.selectedIBPImpliesSameMeasureWavefunctionSymmetry
            weld _ test)))

symmetryAndSeparationGiveNullRespectingOperator :
  ∀ {N : Nat} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {Measure : Set}
    {semantics : R205.FiniteMeasureWavefunctionSemantics group base Measure} →
  R206.FiniteMeasureIBPWavefunctionSymmetryWeld group base Measure semantics →
  R213.PairingSeparatesMeasureNullClasses group base Measure semantics →
  R209.NullRespectingWavefunctionOperator group base Measure semantics
symmetryAndSeparationGiveNullRespectingOperator weld separation = record
  { R209.NullRespectingWavefunctionOperator.operator = R206.operator weld
  ; R209.NullRespectingWavefunctionOperator.preservesNull =
      symmetryAndSeparationPreserveNull weld separation
  }

symmetrySeparationNullDescentRound214Level : ProofLevel
symmetrySeparationNullDescentRound214Level = machineChecked

nullPreservationNoLongerIndependentRound214Level : ProofLevel
nullPreservationNoLongerIndependentRound214Level = machineChecked

-- The remaining physical payments are now upstream and same-object:
--   * inhabit the R205 semantics on the literal Balaban measure;
--   * inhabit R213 separation on that same pairing;
--   * instantiate the R206 IBP weld with the literal finite YM Hamiltonian.
-- Once these exist, R209 null preservation is compiler output above.
literalBalabanMeasureSemanticsRound214Level : ProofLevel
literalBalabanMeasureSemanticsRound214Level = conditional

literalBalabanPairingSeparationRound214Level : ProofLevel
literalBalabanPairingSeparationRound214Level = conditional

literalPhysicalYMIBPWeldRound214Level : ProofLevel
literalPhysicalYMIBPWeldRound214Level = conditional
