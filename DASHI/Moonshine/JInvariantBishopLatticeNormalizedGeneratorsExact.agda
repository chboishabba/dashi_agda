module DASHI.Moonshine.JInvariantBishopLatticeNormalizedGeneratorsExact where

-- Classical normalization of the actual raw lattice limits, with the
-- original constructed Machin real.  Fourier equality is NOT assumed.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Sum.Base using (inj₂)
import Real as R
open R using (ℝ; _*_; _⋆)
import Inverse as I
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
open C using (_≈C_)
open A using (_*C_)
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open Comp using (complexTrans; complexSym)
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopPuncturedShellSummabilityExact as Sum
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U

piInverse : ℝ
piInverse = I._⁻¹ M.bishopMachinPi (inj₂ MP.machinPiPositive)

factor4 factor6 : C.BishopComplex
factor4 = C.complex (((+ 45 / 1) ⋆) * R.pow piInverse 4) R.0ℝ
factor6 = C.complex (((+ 945 / 2) ⋆) * R.pow piInverse 6) R.0ℝ

E4 E6 : U.BishopUpperHalfPlanePoint → C.BishopComplex
E4 p = factor4 *C Sum.At.G4 p
E6 p = factor6 *C Sum.At.G6 p

commuteWeight : ∀ a w z → (a *C (w *C z)) ≈C (w *C (a *C z))
commuteWeight a w z = complexTrans
  (complexSym (L.complexMultiplyAssociative a w z))
  (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative a w) (C.≈C-refl z))
    (L.complexMultiplyAssociative w a z))

E4S : ∀ p → E4 (G.actS p) ≈C (A.powC (U.tau p) 4 *C E4 p)
E4S p = complexTrans
  (A.mulCCongruent (C.≈C-refl factor4) (Mod.At.G4S p))
  (commuteWeight factor4 (A.powC (U.tau p) 4) (Sum.At.G4 p))

E6S : ∀ p → E6 (G.actS p) ≈C (A.powC (U.tau p) 6 *C E6 p)
E6S p = complexTrans
  (A.mulCCongruent (C.≈C-refl factor6) (Mod.At.G6S p))
  (commuteWeight factor6 (A.powC (U.tau p) 6) (Sum.At.G6 p))

E4T : ∀ p → E4 (G.actT p) ≈C E4 p
E4T p = A.mulCCongruent (C.≈C-refl factor4) (Mod.At.G4T p)

E6T : ∀ p → E6 (G.actT p) ≈C E6 p
E6T p = A.mulCCongruent (C.≈C-refl factor6) (Mod.At.G6T p)

-- The exact remaining same-object premise is Fourier equality to THESE
-- normalized limits.  No claim is made that it is already discharged.
