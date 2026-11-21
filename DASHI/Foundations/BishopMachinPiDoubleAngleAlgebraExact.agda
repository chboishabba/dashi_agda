module DASHI.Foundations.BishopMachinPiDoubleAngleAlgebraExact where

------------------------------------------------------------------------
-- Concrete Bishop-real double-angle algebra for the existing Machin
-- quarter-angle source. NO new pi, no trigonometric-period assumption.
--
-- Given the analytic quarter-angle result sin(theta)=cos(theta) and the
-- Pythagorean identity, the double-angle formula forces
--   sin(2theta)=1, cos(2theta)=0,
--   sin(4theta)=0, cos(4theta)=-1.
-- The algebra below is proved via the EXISTING Bishop real ring solver.
--
-- What remains: the actual sin/cos power-series addition/double-angle
-- theorem, and the actual analytic Machin quarter-angle identification.
-- This source does not fabricate either result.
--
-- Attribution: Machin; Bishop/Bridges; Murray/Csimma; original DASHI
-- BishopMachinQuarterAngleBranchExact and BishopConcreteTrigSeries.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)

import Real as B
import RealProperties as BP

square : B.ℝ → B.ℝ
square x = B._*_ x x

doubleSin : B.ℝ → B.ℝ → B.ℝ
doubleSin s c = B._*_ (B._⋆ (+ 2 / 1)) (B._*_ s c)

doubleCos : B.ℝ → B.ℝ → B.ℝ
doubleCos s c = B._-_ (square c) (square s)

-- The source Pythagorean identity is stated at the original sine/cosine
-- outputs, not as a field in a fake real/complex carrier.
quarterSinCosEqualityGivesDoubleSinOne :
  ∀ s c →
  B._≃_ s c →
  B._≃_ (B._+_ (square s) (square c)) B.1ℝ →
  B._≃_ (doubleSin s c) B.1ℝ
quarterSinCosEqualityGivesDoubleSinOne s c same unit =
  BP.≃-trans
    (BP.*-congʳ (BP.*-congˡ same))
    (BP.≃-trans
      (let open BP.ℝ-Solver in
       solve 1
         (λ a → (Κ (+ 2 / 1) ⊗ (a ⊗ a))
           ⊜ ((a ⊗ a) ⊕ (a ⊗ a)))
         BP.≃-refl c)
      (BP.≃-trans
        (BP.+-cong
          (BP.≃-symm (BP.*-cong same same))
          BP.≃-refl)
        unit))

quarterSinCosEqualityGivesDoubleCosZero :
  ∀ s c →
  B._≃_ s c →
  B._≃_ (doubleCos s c) B.0ℝ
quarterSinCosEqualityGivesDoubleCosZero s c same =
  BP.≃-trans
    (BP.-cong
      BP.≃-refl
      (BP.*-cong same same))
    (let open BP.ℝ-Solver in
     solve 1 (λ a → ((a ⊗ a) ⊖ (a ⊗ a)) ⊜ Κ 0ℚᵘ)
       BP.≃-refl c)

doubleAngleSinFourZero :
  ∀ s c →
  B._≃_ s B.1ℝ →
  B._≃_ c B.0ℝ →
  B._≃_ (doubleSin s c) B.0ℝ
doubleAngleSinFourZero s c sOne cZero =
  BP.≃-trans
    (BP.*-congʳ (BP.*-cong sOne cZero))
    (let open BP.ℝ-Solver in
     solve 0
       ((Κ (+ 2 / 1) ⊗ (Κ 1ℚᵘ ⊗ Κ 0ℚᵘ))
         ⊜ Κ 0ℚᵘ)
       BP.≃-refl)

doubleAngleCosFourMinusOne :
  ∀ s c →
  B._≃_ s B.1ℝ →
  B._≃_ c B.0ℝ →
  B._≃_ (doubleCos s c) (B.- B.1ℝ)
doubleAngleCosFourMinusOne s c sOne cZero =
  BP.≃-trans
    (BP.-cong
      (BP.*-cong cZero cZero)
      (BP.*-cong sOne sOne))
    (let open BP.ℝ-Solver in
     solve 0
       (((Κ 0ℚᵘ ⊗ Κ 0ℚᵘ)
          ⊖ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ))
         ⊜ (⊝ Κ 1ℚᵘ))
       BP.≃-refl)

machinQuarterToFourAngleAlgebra :
  ∀ s c →
  B._≃_ s c →
  B._≃_ (B._+_ (square s) (square c)) B.1ℝ →
  B._≃_ (doubleSin (doubleSin s c) (doubleCos s c)) B.0ℝ
machinQuarterToFourAngleAlgebra s c same unit =
  doubleAngleSinFourZero
    (doubleSin s c)
    (doubleCos s c)
    (quarterSinCosEqualityGivesDoubleSinOne s c same unit)
    (quarterSinCosEqualityGivesDoubleCosZero s c same)

machinQuarterToFourAngleCosMinusOne :
  ∀ s c →
  B._≃_ s c →
  B._≃_ (B._+_ (square s) (square c)) B.1ℝ →
  B._≃_
    (doubleCos (doubleSin s c) (doubleCos s c))
    (B.- B.1ℝ)
machinQuarterToFourAngleCosMinusOne s c same unit =
  doubleAngleCosFourMinusOne
    (doubleSin s c)
    (doubleCos s c)
    (quarterSinCosEqualityGivesDoubleSinOne s c same unit)
    (quarterSinCosEqualityGivesDoubleCosZero s c same)
