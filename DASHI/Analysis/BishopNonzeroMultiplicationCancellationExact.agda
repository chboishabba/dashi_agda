module DASHI.Analysis.BishopNonzeroMultiplicationCancellationExact where

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

------------------------------------------------------------------------
-- NONZERO MULTIPLICATION CANCELLATION ON THE IMPORTED BISHOP REAL
--
-- If A is apart from zero and A*x is extensionally zero, multiply by A^-1.
-- Every step is an imported checked Bishop theorem:
--   inverse, associativity, congruence, identity, and annihilating zero.
------------------------------------------------------------------------

nonzeroLeftFactorCancellationToZero :
  (A x : BishopReal.ℝ) →
  A BishopReal.≄0 →
  BishopReal._≃_ (BishopReal._*_ A x) BishopReal.0ℝ →
  BishopReal._≃_ x BishopReal.0ℝ
nonzeroLeftFactorCancellationToZero A x A≄0 Ax≃0 =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm (BishopProperties.*-identityˡ x))
    (BishopProperties.≃-trans
      (BishopProperties.*-congʳ
        (BishopProperties.≃-symm
          (BishopInverse.*-inverseˡ A A≄0)))
      (BishopProperties.≃-trans
        (BishopProperties.*-assoc ((A BishopInverse.⁻¹) A≄0) A x)
        (BishopProperties.≃-trans
          (BishopProperties.*-congˡ Ax≃0)
          (BishopProperties.*-zeroʳ ((A BishopInverse.⁻¹) A≄0)))))

nonzeroRightFactorCancellationToZero :
  (x A : BishopReal.ℝ) →
  A BishopReal.≄0 →
  BishopReal._≃_ (BishopReal._*_ x A) BishopReal.0ℝ →
  BishopReal._≃_ x BishopReal.0ℝ
nonzeroRightFactorCancellationToZero x A A≄0 xA≃0 =
  nonzeroLeftFactorCancellationToZero
    A x A≄0
    (BishopProperties.≃-trans
      (BishopProperties.*-comm A x)
      xA≃0)
