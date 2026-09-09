module DASHI.Foundations.BishopGoldenRatioCarrierExact where

------------------------------------------------------------------------
-- GOLDEN RATIO ON THE EXISTING BISHOP REAL CARRIER
--
-- No second real implementation is introduced.  Define
--
--     phi_B := (1/2) * (1 + sqrt_B(5))
--
-- using the already-constructed canonical Nat square root, then prove
--
--     phi_B^2 ~= phi_B + 1
--
-- from the machine-checked sqrt(5)^2 ~= 5 theorem.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as NatRoot
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as NatRootSquare
open import DASHI.Physics.YangMills.CompactLieProofLevel

halfRational oneRational fiveRational : ℚᵘ
halfRational = + 1 / 2
oneRational = + 1 / 1
fiveRational = + 5 / 1

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

half one five : BishopReal.ℝ
half = embed halfRational
one = embed oneRational
five = embed fiveRational

sqrtFive : BishopReal.ℝ
sqrtFive = NatRoot.canonicalFloorSquareRootReal 5

bishopPhi : BishopReal.ℝ
bishopPhi =
  BishopReal._*_ half (BishopReal._+_ one sqrtFive)

sqrtFiveSquaresToFive :
  BishopReal._≃_
    (BishopReal._*_ sqrtFive sqrtFive)
    five
sqrtFiveSquaresToFive =
  NatRootSquare.canonicalFloorSquareRootSquaresToNat 5

phiSquareExpand :
  BishopReal._≃_
    (BishopReal._*_ bishopPhi bishopPhi)
    (BishopReal._*_
      (BishopReal._*_ half half)
      (BishopReal._+_
        (BishopReal._+_ one (BishopReal._+_ sqrtFive sqrtFive))
        (BishopReal._*_ sqrtFive sqrtFive)))
phiSquareExpand =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ h o r →
      ((h ⊗ (o ⊕ r)) ⊗ (h ⊗ (o ⊕ r)))
      ⊜
      ((h ⊗ h) ⊗ ((o ⊕ (r ⊕ r)) ⊕ (r ⊗ r))))
    BishopP.≃-refl
    half one sqrtFive

replaceSqrtFiveSquare :
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ half half)
      (BishopReal._+_
        (BishopReal._+_ one (BishopReal._+_ sqrtFive sqrtFive))
        (BishopReal._*_ sqrtFive sqrtFive)))
    (BishopReal._*_
      (BishopReal._*_ half half)
      (BishopReal._+_
        (BishopReal._+_ one (BishopReal._+_ sqrtFive sqrtFive))
        five))
replaceSqrtFiveSquare =
  BishopP.*-cong
    BishopP.≃-refl
    (BishopP.+-cong BishopP.≃-refl sqrtFiveSquaresToFive)

phiSquareAfterRootLaw :
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ half half)
      (BishopReal._+_
        (BishopReal._+_ one (BishopReal._+_ sqrtFive sqrtFive))
        five))
    (BishopReal._+_ bishopPhi one)
phiSquareAfterRootLaw =
  let open BishopP.ℝ-Solver
  in solve 4
    (λ h o f r →
      ((h ⊗ h) ⊗ ((o ⊕ (r ⊕ r)) ⊕ f))
      ⊜ ((h ⊗ (o ⊕ r)) ⊕ o))
    BishopP.≃-refl
    half one five sqrtFive

bishopPhiMinimalPolynomial :
  BishopReal._≃_
    (BishopReal._*_ bishopPhi bishopPhi)
    (BishopReal._+_ bishopPhi one)
bishopPhiMinimalPolynomial =
  BishopP.≃-trans
    phiSquareExpand
    (BishopP.≃-trans replaceSqrtFiveSquare phiSquareAfterRootLaw)

bishopGoldenRatioCarrierConstructionLevel : ProofLevel
bishopGoldenRatioCarrierConstructionLevel = machineChecked

bishopGoldenRatioMinimalPolynomialLevel : ProofLevel
bishopGoldenRatioMinimalPolynomialLevel = machineChecked
