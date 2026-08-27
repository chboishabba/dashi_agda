module DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact where

------------------------------------------------------------------------
-- THE ERDOS CONSTANT FROM THE CONSTRUCTED NAT ROOT AND MACHIN PI
--
-- We do not need a second rational square-root construction.  Define
--
--     sqrt(2/3) := (1/3) * sqrt(6).
--
-- The already-constructed Nat square root gives sqrt(6)^2 ~= 6, hence the
-- scaled value squares to 2/3.  The Erdos constant is then definitionally
--
--     c := pi_M * sqrt(2/3),
--
-- where pi_M is the genuine Bishop Machin real.  No claim that pi_M has already
-- been identified with a trigonometric period is needed for this construction.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinPiRationalWindowExact as PiWindow
import DASHI.Foundations.BishopNatSquareRootApproximationExact as NatRootApprox
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as NatRoot
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as NatRootSquare
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneThird twoThirds sixRational : ℚᵘ
oneThird = + 1 / 3
twoThirds = + 2 / 3
sixRational = + 6 / 1

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

sqrtSix : BishopReal.ℝ
sqrtSix = NatRoot.canonicalFloorSquareRootReal 6

sqrtTwoThirds : BishopReal.ℝ
sqrtTwoThirds = BishopReal._*_ (embed oneThird) sqrtSix

erdosMachinConstant : BishopReal.ℝ
erdosMachinConstant =
  BishopReal._*_ Machin.bishopMachinPi sqrtTwoThirds

sqrtSixSquaresToSix :
  BishopReal._≃_
    (BishopReal._*_ sqrtSix sqrtSix)
    (embed sixRational)
sqrtSixSquaresToSix =
  NatRootSquare.canonicalFloorSquareRootSquaresToNat 6

sqrtTwoThirdsSquareNormalization :
  BishopReal._≃_
    (BishopReal._*_ sqrtTwoThirds sqrtTwoThirds)
    (BishopReal._*_
      (BishopReal._*_ (embed oneThird) (embed oneThird))
      (BishopReal._*_ sqrtSix sqrtSix))
sqrtTwoThirdsSquareNormalization =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ third root →
      ((third ⊗ root) ⊗ (third ⊗ root))
      ⊜ ((third ⊗ third) ⊗ (root ⊗ root)))
    BishopP.≃-refl
    (embed oneThird)
    sqrtSix

sqrtTwoThirdsSquaresToTwoThirds :
  BishopReal._≃_
    (BishopReal._*_ sqrtTwoThirds sqrtTwoThirds)
    (embed twoThirds)
sqrtTwoThirdsSquaresToTwoThirds =
  BishopP.≃-trans
    sqrtTwoThirdsSquareNormalization
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        sqrtSixSquaresToSix)
      (let open BishopP.ℝ-Solver
       in solve 0
         (((Κ oneThird ⊗ Κ oneThird) ⊗ Κ sixRational)
           ⊜ Κ twoThirds)
         BishopP.≃-refl))

machinPiPositive : BishopReal._<_ BishopReal.0ℝ Machin.bishopMachinPi
machinPiPositive =
  BishopP.<-trans
    (BishopP.p<q⇒p⋆<q⋆
      (+ 0 / 1) (+ 3 / 1)
      (ℚP.positive⁻¹ (+ 3 / 1)))
    PiWindow.threeBelowMachinPi

sqrtTwoThirdsNonnegative : BishopReal.NonNegative sqrtTwoThirds
sqrtTwoThirdsNonnegative =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.0≤x⇒nonNegx
      (BishopP.p≤q⇒p⋆≤q⋆
        (+ 0 / 1) oneThird
        (ℚP.nonNegative⁻¹ oneThird)))
    (importedRootNonnegative 6)
  where
  importedRootNonnegative :
    (n : Agda.Builtin.Nat.Nat) →
    BishopReal.NonNegative (NatRoot.canonicalFloorSquareRootReal n)
  importedRootNonnegative n =
    let open import DASHI.Foundations.BishopNatSquareRootNonnegativeExact
    in canonicalFloorSquareRootNonnegative n

bishopSqrtTwoThirdsConstructionLevel : ProofLevel
bishopSqrtTwoThirdsConstructionLevel = machineChecked

bishopSqrtTwoThirdsSquareLevel : ProofLevel
bishopSqrtTwoThirdsSquareLevel = machineChecked

bishopErdosMachinConstantDefinitionLevel : ProofLevel
bishopErdosMachinConstantDefinitionLevel = machineChecked
