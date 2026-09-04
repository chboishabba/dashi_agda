module DASHI.Analysis.BishopRightDivisionTransportExact where

import Real as BishopReal
import RealProperties as BishopProperties
import Inverse as BishopInverse

------------------------------------------------------------------------
-- SOLVE x*d = y FOR x ON THE IMPORTED BISHOP REAL
------------------------------------------------------------------------

solveRightMultiplication :
  (x d y : BishopReal.ℝ) →
  d BishopReal.≄0 →
  BishopReal._≃_ (BishopReal._*_ x d) y →
  BishopReal._≃_
    x
    (BishopReal._*_ y ((d BishopInverse.⁻¹) _))
solveRightMultiplication x d y d≄0 xd≃y =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm (BishopProperties.*-identityʳ x))
    (BishopProperties.≃-trans
      (BishopProperties.*-congˡ
        (BishopProperties.≃-symm
          (BishopInverse.*-inverseʳ d d≄0)))
      (BishopProperties.≃-trans
        (BishopProperties.≃-symm
          (BishopProperties.*-assoc x d ((d BishopInverse.⁻¹) d≄0)))
        (BishopProperties.*-congʳ xd≃y)))

solveLeftMultiplication :
  (d x y : BishopReal.ℝ) →
  d BishopReal.≄0 →
  BishopReal._≃_ (BishopReal._*_ d x) y →
  BishopReal._≃_
    x
    (BishopReal._*_ ((d BishopInverse.⁻¹) _) y)
solveLeftMultiplication d x y d≄0 dx≃y =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm (BishopProperties.*-identityˡ x))
    (BishopProperties.≃-trans
      (BishopProperties.*-congʳ
        (BishopProperties.≃-symm
          (BishopInverse.*-inverseˡ d d≄0)))
      (BishopProperties.≃-trans
        (BishopProperties.*-assoc ((d BishopInverse.⁻¹) d≄0) d x)
        (BishopProperties.*-congˡ dx≃y)))
