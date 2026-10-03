module DASHI.ComputerScience.TekumPadicDualCylinderNaturalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Base using (reverse; init; tail)
open import Data.Vec.Properties using (init-reverse; reverse-involutive)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as PAdic
import DASHI.Codec.TriadicPAdicCylinderExact as Cylinder
import DASHI.ComputerScience.TekumTriadicPAdicKernelBridgeExact as Kernel
import DASHI.ComputerScience.TekumPadicDualChartExact as Dual

------------------------------------------------------------------------
-- The dual chart converts Tekum's head-drop orientation into tail-drop.
-- For one digit this is literally Vec.init; two digits are two inits.
------------------------------------------------------------------------

dualDropOne :
  ∀ {n} → Vec Trit.Trit (suc n) → Vec Trit.Trit n
dualDropOne xs = reverse (tail (reverse xs))

dualDropOneIsInit :
  ∀ {n} (xs : Vec Trit.Trit (suc n)) →
  dualDropOne xs ≡ init xs
dualDropOneIsInit xs =
  trans
    (cong reverse (sym (init-reverse xs)))
    (reverse-involutive (init xs))

------------------------------------------------------------------------
-- The existing carrier weld commutes with executable cylinder refinement.
------------------------------------------------------------------------

toKernelInitNaturality :
  ∀ {n} (xs : Vec Trit.Trit (suc n)) →
  Kernel.toKernel (init xs)
  ≡ Cylinder.refineKernel n (Kernel.toKernel xs)
toKernelInitNaturality {zero} (x ∷ []) = refl
toKernelInitNaturality {suc n} (x ∷ xs) =
  cong (x PAdic.∷ᵥ_) (toKernelInitNaturality xs)

------------------------------------------------------------------------
-- Two Tekum precision digits in the reversed chart are exactly two
-- executable cylinder refinements.
------------------------------------------------------------------------

dualPrecisionTwoAsInitTwice :
  ∀ {n} (xs : Vec Trit.Trit (suc (suc n))) →
  Dual.dualPrecisionTwo xs ≡ init (init xs)
dualPrecisionTwoAsInitTwice xs =
  trans
    (dualDropOneIsInit (tail (reverse xs)))
    (cong init (dualDropOneIsInit xs))

dualPrecisionTwoIsCylinderRefinementTwo :
  ∀ {n} (xs : Vec Trit.Trit (suc (suc n))) →
  Kernel.toKernel (Dual.dualPrecisionTwo xs)
  ≡ Cylinder.refineKernel n
      (Cylinder.refineKernel (suc n) (Kernel.toKernel xs))
dualPrecisionTwoIsCylinderRefinementTwo {n} xs =
  trans
    (cong Kernel.toKernel (dualPrecisionTwoAsInitTwice xs))
    (trans
      (toKernelInitNaturality (init xs))
      (cong (Cylinder.refineKernel n)
        (toKernelInitNaturality xs)))

------------------------------------------------------------------------
-- Authority boundary: finite representation naturality only.
------------------------------------------------------------------------

record TekumPadicDualCylinderBoundary : Set where
  constructor tekumPadicDualCylinderBoundary
  field
    reversalTurnsHeadDropIntoTailDrop : Bool
    carrierWeldCommutesWithCylinderRefinement : Bool
    twoDigitDualPrecisionEqualsTwoCylinderRefinements : Bool
    realValueIdentifiedWithPadicValue : Bool
    metricOrOrderIdentifiedAcrossCharts : Bool

finiteNaturalityOnly : TekumPadicDualCylinderBoundary
finiteNaturalityOnly =
  tekumPadicDualCylinderBoundary true true true false false
