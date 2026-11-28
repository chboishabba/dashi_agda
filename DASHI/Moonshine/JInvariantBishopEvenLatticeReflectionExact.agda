module DASHI.Moonshine.JInvariantBishopEvenLatticeReflectionExact where

-- SOURCE-WRITTEN, kernel pending. The simultaneous reversal (m,n) ->
-- (-m,-n) preserves the actual even reciprocal powers, not the individual
-- signed denominator. Includes the zero-axis puncture.
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import Data.Integer.Properties as ZP
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopLatticeEvenPowerShellMajorantExact as E
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open Comp using (complexTrans; complexSym)

negPoint : L.LatticePoint → L.LatticePoint
negPoint (L.lattice-point m n) = L.lattice-point (Z.- m) (Z.- n)

negPointTwice : ∀ p → negPoint (negPoint p) ≡ p
negPointTwice (L.lattice-point m n) =
  L.lattice-ext (ZP.neg-involutive m) (ZP.neg-involutive n)

negIndex : K.NonzeroLatticePoint → K.NonzeroLatticePoint
negIndex i = K.nonzero-lattice-point (negPoint (K.point i))
  (λ eq → K.notOrigin i (trans (sym (negPointTwice (K.point i))) (cong negPoint eq)))

negDenom : ∀ p q → K.latticeDenominator (negPoint q) (U.tau p) ≈C
  G.negC (K.latticeDenominator q (U.tau p))
negDenom p (L.lattice-point m n) =
  let x = C.re (U.tau p); y = C.im (U.tau p)
      a = K.embedInteger m; b = K.embedInteger n
      open P.ℝ-Solver
  in P.≃-trans (P.+-cong (P.*-congʳ (G.intNeg m)) (G.intNeg n))
       (solve 3 (λ a b x → (⊝ a) ⊗ x ⊕ (⊝ b) ⊜ ⊝ (a ⊗ x ⊕ b)) P.≃-refl a b x) ,
     P.≃-trans (P.+-cong (P.*-congʳ (G.intNeg m)) P.≃-refl)
       (solve 2 (λ a y → (⊝ a) ⊗ y ⊕ Κ 0ℚᵘ ⊜ ⊝ (a ⊗ y ⊕ Κ 0ℚᵘ)) P.≃-refl a y)

negMulBoth : ∀ x y → (G.negC x *C G.negC y) ≈C (x *C y)
negMulBoth (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 4
    (λ a b c d → (⊝ a) ⊗ (⊝ c) ⊖ (⊝ b) ⊗ (⊝ d) ⊜ a ⊗ c ⊖ b ⊗ d) P.≃-refl a b c d) ,
  (let open P.ℝ-Solver in solve 4
    (λ a b c d → (⊝ a) ⊗ (⊝ d) ⊕ (⊝ b) ⊗ (⊝ c) ⊜ a ⊗ d ⊕ b ⊗ c) P.≃-refl a b c d)

negRecip : ∀ p i → E.reciprocal p (negIndex i) ≈C G.negC (E.reciprocal p i)
negRecip p i = G.reciprocalUnique _ _ _
  (complexTrans (A.mulCCongruent (negDenom p (K.point i)) (C.≈C-refl _))
    (complexTrans (negMulBoth _ _) (Rec.multiplyReciprocal _ (U.upperHalfPlaneDenominatorNonzero p i))))

squareCong : ∀ {x y} → x ≈C y → Rat.square x ≈C Rat.square y
squareCong h = A.mulCCongruent h h

cubeCong : ∀ {x y} → x ≈C y → Rat.cube x ≈C Rat.cube y
cubeCong h = A.mulCCongruent h (squareCong h)

negPow4 : ∀ z → powC (G.negC z) 4 ≈C powC z 4
negPow4 z = complexTrans (complexSym (LR.powFour (G.negC z)))
  (complexTrans (squareCong (negMulBoth z z)) (LR.powFour z))

negPow6 : ∀ z → powC (G.negC z) 6 ≈C powC z 6
negPow6 z = complexTrans (complexSym (LR.powSix (G.negC z)))
  (complexTrans (cubeCong (negMulBoth z z)) (LR.powSix z))

data EvenWeight : Nat → Set where
  four : EvenWeight 4
  six : EvenWeight 6

negSummand : ∀ {w} → EvenWeight w → ∀ p i → E.summand w p (negIndex i) ≈C E.summand w p i
negSummand four p i = complexTrans (A.powCCongruent (negRecip p i) 4) (negPow4 _)
negSummand six p i = complexTrans (A.powCCongruent (negRecip p i) 6) (negPow6 _)

rawNeg : ∀ {w} → EvenWeight w → ∀ p q →
  Mod.rawC (E.summand w p) (negPoint q) ≈C Mod.rawC (E.summand w p) q
rawNeg {w} even p q with Ex.origin? q
... | yes refl = C.≈C-refl _
... | no neq =
  let i = K.nonzero-lattice-point q (λ h → ⊥-elim (neq h))
      f = E.summand w p
      h = Re.summandRespect w p
  in complexTrans (Mod.rawCRead f h (negIndex i))
    (complexTrans (negSummand even p i) (complexSym (Mod.rawCRead f h i)))
