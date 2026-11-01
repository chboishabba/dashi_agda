module DASHI.Physics.YangMills.BalabanCMP109Equation012SameObjectFrechetLittleOExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4FiniteDimensionalFrechetChainProductExact as Frechet
import DASHI.Physics.YangMills.BalabanCMP109Equation012DerivativeDAGExact as DAG
import DASHI.Physics.YangMills.BalabanCMP109L13Equation012DerivativeMassAssemblyExact as L13

record Equation012SameObjectFrechetLittleO
    {Sample Constraint State Bound Entry Base : Set}
    (algebra : DAG.DifferentialDAGAlgebra Entry Base)
    (stateCarrier : Frechet.AdditiveCarrier State)
    (constraintCarrier : Frechet.AdditiveCarrier Constraint)
    (leaves : DAG.Equation012DerivativeLeaves algebra)
    (dag : DAG.Equation012DerivativeDAG leaves)
    (samples : List Sample)
    (rows : List Constraint)
    (columns : List State)
    (l13Family : L13.Equation012FourStageKernelFamily Sample Constraint State samples rows columns)
    (mapExpansion : Frechet.ExactFirstOrderExpansion stateCarrier constraintCarrier)
    (meaning : Frechet.FrechetRemainderMeaning State Constraint Bound stateCarrier constraintCarrier mapExpansion)
    (mapPoint : State)
    (entryToMatrix : Entry → Sample → State → Constraint) : Set₁ where
  field
    -- 1. Exact identification with L13 derivative matrix
    sameObjectIdentification :
      ∀ sample vector →
      entryToMatrix (DAG.flattenedEquation012Derivative dag) sample vector
      ≡ L13.localDerivativeDifferenceKernel l13Family sample vector

    -- 2. Little-o residual needed for nonlinear tangent geometry
    littleOResidual :
      Frechet.LittleOAtZero meaning (Frechet.remainder mapExpansion mapPoint)

open Equation012SameObjectFrechetLittleO public

cmp109Equation012SameObjectFrechetLittleOLevel : ProofLevel
cmp109Equation012SameObjectFrechetLittleOLevel = machineChecked
