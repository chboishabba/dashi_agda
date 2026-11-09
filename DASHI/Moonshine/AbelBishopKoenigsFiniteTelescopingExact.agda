module DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact where

------------------------------------------------------------------------
-- FINITE TELESCOPING ON THE ACTUAL VENDORED BISHOP SETOID
--
-- For any source complex trajectory h, its actual signed increment
-- h(n+1)-h(n) has Bishop componentwise prefix equal (in setoid
-- equality, not propositional equality) to h(N)-h(0).
-- Uses Murray/Bishop Sequence.SeriesOf and RealProperties.ℝ-Solver.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopKoenigsIncrementSeriesExact as Increments

scalarDifference : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
scalarDifference trajectory n =
  BishopReal._-_ (trajectory (suc n)) (trajectory n)

originalBishopFiniteScalarTelescope :
  (trajectory : Nat → BishopReal.ℝ) →
  (n : Nat) →
  BishopReal._≃_
    (BishopSequence.SeriesOf (scalarDifference trajectory) n)
    (BishopReal._-_ (trajectory n) (trajectory zero))
originalBishopFiniteScalarTelescope trajectory zero =
  let open BishopP.ℝ-Solver in
  solve 1
    (λ first → Κ 0ℚᵘ ⊜ (first ⊖ first))
    BishopP.≃-refl (trajectory zero)
originalBishopFiniteScalarTelescope trajectory (suc n) =
  BishopP.≃-trans
    (BishopP.+-cong
      (originalBishopFiniteScalarTelescope trajectory n)
      BishopP.≃-refl)
    (let open BishopP.ℝ-Solver in
     solve 3
       (λ first current next →
         ((current ⊖ first) ⊕ (next ⊖ current))
         ⊜ (next ⊖ first))
       BishopP.≃-refl
       (trajectory zero)
       (trajectory n)
       (trajectory (suc n)))

originalBishopComplexStepDifference :
  (trajectory : Nat → Complex.BishopComplex) →
  Nat → Complex.BishopComplex
originalBishopComplexStepDifference trajectory n =
  Algebra._-C_ (trajectory (suc n)) (trajectory n)

originalBishopKoenigsPrefixSameSource :
  (trajectory : Nat → Complex.BishopComplex) →
  (n : Nat) →
  Complex._≈C_
    (Increments.originalBishopKoenigsIncrementPrefix
      (originalBishopComplexStepDifference trajectory) n)
    (Algebra._-C_ (trajectory n) (trajectory zero))
originalBishopKoenigsPrefixSameSource trajectory n =
  originalBishopFiniteScalarTelescope
    (λ k → Complex.re (trajectory k)) n
  ,
  originalBishopFiniteScalarTelescope
    (λ k → Complex.im (trajectory k)) n
