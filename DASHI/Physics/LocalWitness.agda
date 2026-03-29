module DASHI.Physics.LocalWitness where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.Refinement as Ref
open import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs

record OperatorWitness {ℓ : Level}
  (T : PT.PhysicalTheory ℓ) : Set (lsuc ℓ) where
  field
    Operator : Set ℓ
    apply    : Operator → PT.State T → PT.State T
    unitOp   : Operator
    compose  : Operator → Operator → Operator

    preservesInv :
      ∀ op {x} → PT.Inv T x → PT.Inv T (apply op x)

record ScalingWitness {ℓ : Level}
  (R : Ref.RefinementTower ℓ) : Set (lsuc ℓ) where
  open Ref.RefinementTower R
  field
    coarse-defect≤fine :
      ∀ n x →
      PT.defectSize (TheoryAt n)
        (Ref.ApproxRefinementStep.project (refine n) x)
      ≤
      PT.defectSize (TheoryAt (Agda.Builtin.Nat.suc n)) x

record LocalTheoryWitness {ℓ : Level}
  (base : PT.PhysicalTheory ℓ)
  (tower : Ref.RefinementTower ℓ)
  (quot : SQ.QuotientedTheory ℓ)
  (obs : Obs.ObservableTheory quot) : Set (lsuc ℓ) where
  field
    operators   : OperatorWitness base
    scaling     : ScalingWitness tower
    obsInvariant : Obs.SymmetryInvariantObservables quot obs
