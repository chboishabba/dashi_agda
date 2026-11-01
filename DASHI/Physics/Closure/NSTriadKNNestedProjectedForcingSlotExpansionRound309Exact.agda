module DASHI.Physics.Closure.NSTriadKNNestedProjectedForcingSlotExpansionRound309Exact where

------------------------------------------------------------------------
-- ROUND309 / EXPAND THE LITERAL PROJECTED N_p FIBRE INSIDE THE R307 SLOT
--
-- R307 reduces the heat-weighted nonlinear forcing problem to the existing
-- outer normalized-direction slot kernel
--
--   Kslot(P,Q,N_p,u_q).
--
-- The Galerkin audit defines N_p literally as a finite sum of projected
-- ordered interaction terms over the physical output-p fibre.  Because Kslot
-- is additive in its first amplitude, this file pushes that finite sum through
-- the SAME outer kernel before any norm estimate:
--
--   Kslot(P,Q,N_p,u_q)
--     = sum_{a+b=p} Kslot(P,Q,N_ab,u_q).
--
-- Thus the live R301 object is a nested resonant configuration
--
--   a+b=p,   p+q=k,
--
-- not a black-box cubic forcing norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145

complex3SubtractAdditive :
  ∀ {r} {F : C3.RealField r}
    (a b c d : C3.Complex3 F) →
  C3.complex3Subtract
    (C3.complex3Add a b)
    (C3.complex3Add c d)
  ≡
  C3.complex3Add
    (C3.complex3Subtract a c)
    (C3.complex3Subtract b d)
complex3SubtractAdditive {F = F}
    (C3.complex3 ax ay az) (C3.complex3 bx by bz)
    (C3.complex3 cx cy cz) (C3.complex3 dx dy dz) =
  Algebra.complex3Ext
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl ax bx cx dx)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl ay by cy dy)
    (R.solve 4 (λ a b c d → ((a R.⊕ b) R.⊕ (R.⊝ (c R.⊕ d))) R.⊜ ((a R.⊕ (R.⊝ c)) R.⊕ (b R.⊕ (R.⊝ d)))) refl az bz cz dz)
  where module R = Ring.Solver F

slotKernelAdditiveFirstAmplitude :
  ∀ {r} {F : C3.RealField r}
    (P Q a b v : C3.Complex3 F) →
  R145.slotKernel P Q (C3.complex3Add a b) v
  ≡
  C3.complex3Add
    (R145.slotKernel P Q a v)
    (R145.slotKernel P Q b v)
slotKernelAdditiveFirstAmplitude P Q a b v =
  trans
    (cong₂ C3.complex3Subtract
      (trans
        (cong₂ Cross.complex3Cross (R94.crossAddRight P a b) refl)
        (R94.crossAddLeft
          (Cross.complex3Cross P a)
          (Cross.complex3Cross P b)
          v))
      (R94.crossAddLeft a b (Cross.complex3Cross Q v)))
    (complex3SubtractAdditive
      (Cross.complex3Cross (Cross.complex3Cross P a) v)
      (Cross.complex3Cross (Cross.complex3Cross P b) v)
      (Cross.complex3Cross a (Cross.complex3Cross Q v))
      (Cross.complex3Cross b (Cross.complex3Cross Q v)))

slotKernelFoldFirstAmplitude :
  ∀ {r} {F : C3.RealField r}
    (P Q v : C3.Complex3 F)
    (items : List (C3.Complex3 F)) →
  R145.slotKernel P Q (Audit.sumVectors items) v
  ≡ Audit.sumVectors (map (λ item → R145.slotKernel P Q item v) items)
slotKernelFoldFirstAmplitude {F = F} P Q v [] = refl
slotKernelFoldFirstAmplitude P Q v (item ∷ rest) =
  trans
    (slotKernelAdditiveFirstAmplitude P Q item (Audit.sumVectors rest) v)
    (cong₂ C3.complex3Add refl
      (slotKernelFoldFirstAmplitude P Q v rest))

projectedNonlinearitySlotKernelExpands :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (P Q v : C3.Complex3 F)
    (p : Z3.FourierMode) →
  R145.slotKernel P Q (Audit.projectedNonlinearity system p) v
  ≡
  Audit.sumVectors
    (map
      (λ term → R145.slotKernel P Q term v)
      (Audit.mapTriadTerms system (Audit.concreteTriadsAt system p)))
projectedNonlinearitySlotKernelExpands system P Q v p =
  slotKernelFoldFirstAmplitude P Q v
    (Audit.mapTriadTerms system (Audit.concreteTriadsAt system p))

round309SlotKernelAdditivityClosed : Bool
round309SlotKernelAdditivityClosed = true

round309ProjectedNonlinearityExpandedBeforeNorms : Bool
round309ProjectedNonlinearityExpandedBeforeNorms = true

round309NestedResonanceCarrierExposed : Bool
round309NestedResonanceCarrierExposed = true

round309NestedShellEstimateClosed : Bool
round309NestedShellEstimateClosed = false

round309PackageAClosed : Bool
round309PackageAClosed = false

round309ClayPromotion : Bool
round309ClayPromotion = false
