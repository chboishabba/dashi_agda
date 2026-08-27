module DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact where

------------------------------------------------------------------------
-- ROUND118 / EXACT SELECTED-SWAP ANTISYMMETRY ON ACTUAL K-SLOT CELLS
--
-- Round117 closes the cross-selected partner combinatorics.  Before attempting
-- a quantitative payment, inspect the literal cell algebra itself.
--
-- For fixed forcing incidence sigma,
--
--   T(tau,sigma)
--     = < N_sigma , u_p(tau) x u_q(tau) >.
--
-- Swapping the SELECTED incidence exchanges the two cross-product inputs while
-- leaving the forcing incidence untouched.  Since the C^3 cross product is
-- exactly antisymmetric,
--
--   T(swap tau,sigma) = - T(tau,sigma).
--
-- This is a genuine exact antisymmetric suborbit of the ACTUAL Waleffe quartic
-- cells.  It is different from the Round112 reality orbit, which is
-- transfer-invariant and therefore does not provide this sign.
--
-- Important boundary: this theorem alone does not prove the weighted external
-- defect vanishes.  A later aggregation theorem must prove that selected-swap
-- partners occur with the same critical weight (or expose the weight defect)
-- on the exact selected carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeCrossSelectedPartnerRound116Exact as R116

crossAnticommutative :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  Cross.complex3Cross v u
  ≡ C3.complex3Negate (Cross.complex3Cross u v)
crossAnticommutative {F = F}
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (R.solve 4
      (λ uy uz vy vz →
        ((vy R.⊗ uz) R.⊕ (R.⊝ (vz R.⊗ uy)))
        R.⊜
        R.⊝ ((uy R.⊗ vz) R.⊕ (R.⊝ (uz R.⊗ vy))))
      refl uy uz vy vz)
    (R.solve 4
      (λ uz ux vz vx →
        ((vz R.⊗ ux) R.⊕ (R.⊝ (vx R.⊗ uz)))
        R.⊜
        R.⊝ ((uz R.⊗ vx) R.⊕ (R.⊝ (ux R.⊗ vz))))
      refl uz ux vz vx)
    (R.solve 4
      (λ ux uy vx vy →
        ((vx R.⊗ uy) R.⊕ (R.⊝ (vy R.⊗ ux)))
        R.⊜
        R.⊝ ((ux R.⊗ vy) R.⊕ (R.⊝ (uy R.⊗ vx))))
      refl ux uy vx vy)
  where module R = Ring.Solver F

selectedSwapCrossIsNegative :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  Cross.complex3Cross
    (Audit.velocity system (Physical.p (Symmetry.swapTriad tau)))
    (Audit.velocity system (Physical.q (Symmetry.swapTriad tau)))
  ≡ C3.complex3Negate
      (Cross.complex3Cross
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau)))
selectedSwapCrossIsNegative system tau =
  crossAnticommutative
    (Audit.velocity system (Physical.p tau))
    (Audit.velocity system (Physical.q tau))

selectedSwapCellTransferIsNegative :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence) →
  R116.kWaleffeCrossCellTransfer system (Symmetry.swapTriad tau) sigma
  ≡ C3.complexNegate (R116.kWaleffeCrossCellTransfer system tau sigma)
selectedSwapCellTransferIsNegative system tau sigma =
  trans
    (cong
      (C3.hermitianPairing3 (Audit.projectedOrderedTerm system sigma))
      (selectedSwapCrossIsNegative system tau))
    (Additive.hermitianPairingNegateRight
      (Audit.projectedOrderedTerm system sigma)
      (Cross.complex3Cross
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))))

selectedSwapPairCancels :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau sigma : Physical.PhysicalTriadIncidence) →
  C3.complexAdd
    (R116.kWaleffeCrossCellTransfer system tau sigma)
    (R116.kWaleffeCrossCellTransfer system (Symmetry.swapTriad tau) sigma)
  ≡ C3.complexZero F
selectedSwapPairCancels system tau sigma
  rewrite selectedSwapCellTransferIsNegative system tau sigma =
  Additive.complexAddInverseRight
    (R116.kWaleffeCrossCellTransfer system tau sigma)

round118ActualSelectedSwapCellAntisymmetryClosed : Bool
round118ActualSelectedSwapCellAntisymmetryClosed = true

round118SelectedSwapPairCancelsBeforeAbsoluteValues : Bool
round118SelectedSwapPairCancelsBeforeAbsoluteValues = true

round118CriticalSelectedWeightSwapInvarianceClosed : Bool
round118CriticalSelectedWeightSwapInvarianceClosed = false

round118ActualSelectedSwapCellAntisymmetryClosedIsTrue :
  round118ActualSelectedSwapCellAntisymmetryClosed ≡ true
round118ActualSelectedSwapCellAntisymmetryClosedIsTrue = refl

round118SelectedSwapPairCancelsBeforeAbsoluteValuesIsTrue :
  round118SelectedSwapPairCancelsBeforeAbsoluteValues ≡ true
round118SelectedSwapPairCancelsBeforeAbsoluteValuesIsTrue = refl

round118CriticalSelectedWeightSwapInvarianceClosedIsFalse :
  round118CriticalSelectedWeightSwapInvarianceClosed ≡ false
round118CriticalSelectedWeightSwapInvarianceClosedIsFalse = refl
