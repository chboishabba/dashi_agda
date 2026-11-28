module DASHI.Moonshine.CM163BishopHecke41ActualJLocalDerivativeExact where

-- SOURCE-WRITTEN, kernel pending. Use the EXISTING dyadic q geometry
-- to supply the strict inner/outer reference at EVERY original point.
-- No arbitrary larger disk or fitted J. The guarded quotient j=J/q
-- inherits the same divided-difference factor on its actual chart.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≤_; _≃_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41NormalizedProductExact as Original
import DASHI.Moonshine.CM163BishopHecke41StrictDiskDerivativeExact as Strict
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as B
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as Jet
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_)
open Comp using (complexTrans; complexSym)

module At (inputs : Round11.BishopCutset) where
  module O = Original.At inputs
  module G = O.G
  module Ph = O.Ph
  open O using (q; junit; Jvalue; qj)

  radius : U.BishopUpperHalfPlanePoint → ℝ
  radius p = Radius.machinQRadius (C.im (U.tau p))

  unit : ∀ p → Unit.BishopUnitIntervalRatio (radius p)
  unit p = Disk.unitInterval (Ph.disk p)

  referenceEval : ∀ p → Eval.Eval (q p) (E.lift D.Junit)
  referenceEval p = Eval.fromReal (junit p)

  normBelowOne : ∀ p → Norm.normSqC (q p) ≤ R.1ℝ
  normBelowOne p = P.≤-respˡ-≃ (P.≃-symm (Disk.normSquareAgreement (Ph.disk p)))
    (P.≤-respʳ-≃ (P.*-identityʳ R.1ℝ)
      (P.*-mono-≤ (Unit.ratioNonnegativeWitness (unit p)) (Unit.ratioNonnegativeWitness (unit p))
        (P.<⇒≤ (Unit.ratioBelowOne (unit p))) (P.<⇒≤ (Unit.ratioBelowOne (unit p)))))

  module Around (p : U.BishopUpperHalfPlanePoint) where
    innerPoint = Phase.left p
    outerPoint = Phase.left innerPoint
    inner = q innerPoint
    outer = q outerPoint
    inz = G.qNonzero innerPoint
    onz = G.qNonzero outerPoint
    s = radius outerPoint

    -- Outer phase squared is exactly inner, so their quotient is
    -- the outer phase itself. This is the existing dyadic chart weld.
    ratioRead : B.relative inner outer onz ≈C outer
    ratioRead = Cancel.cancelLeft outer _ _ onz
      (complexTrans (B.relativeRead inner outer onz) (complexSym (Ph.squareQ innerPoint)))

    ratioUpper : Upper.BishopComplexNormSquareUpperRadius (B.relative inner outer onz) s
    ratioUpper = record
      { Upper.radiusNonnegative = Unit.ratioNonnegativeWitness (unit outerPoint)
      ; Upper.normSqBelowRadiusSquare = P.≤-reflexive
          (P.≃-trans (B.normCong ratioRead) (Disk.normSquareAgreement (Ph.disk outerPoint))) }

    module S = Strict.Shrink outer inner onz inz s
      (Unit.ratioNonnegative (unit outerPoint)) (Unit.ratioBelowOne (unit outerPoint)) ratioUpper
      (E.lift D.Junit) (referenceEval outerPoint)

    centerInside : S.Inside (q p)
    centerInside =
      let n = Norm.normSqC inner
          read = P.≃-trans (P.≃-symm (B.normCong (Ph.squareQ p))) (Norm.normSqMultiply inner inner)
      in P.≤-respˡ-≃ (P.≃-symm read)
        (P.≤-respʳ-≃ (P.*-identityʳ n)
          (P.*-monoˡ-≤-nonNeg (normBelowOne innerPoint) (Upper.normSquareNonnegative inner)))

    Jquot : ∀ v → S.Inside (q v) → BishopComplex
    Jquot v h = S.quotient (q p) (q v) centerInside h

    Jincrement : ∀ v h → (Jvalue v -C Jvalue p) ≈C ((q v -C q p) *C Jquot v h)
    Jincrement v h = S.increment (q p) (q v) centerInside h (referenceEval p) (referenceEval v)

    jquot : ∀ v → S.Inside (q v) → BishopComplex
    jquot v h = Rec.reciprocalC (q v) (G.qNonzero v) *C (Jquot v h -C G.j p)

    jincrement : ∀ v h → (G.j v -C G.j p) ≈C ((q v -C q p) *C jquot v h)
    jincrement v h =
      let qv = q v; qu = q p; jv = G.j v; ju = G.j p
          e = qv -C qu; jD = Jquot v h; a = jD -C ju
          qinv = Rec.reciprocalC qv (G.qNonzero v)
          -- qv*(jv-ju) = (Jv-Ju)-(qv-qu)*ju.
          clear = complexTrans (Alg.mulSub qv jv ju)
            (complexTrans (clearRearrange qv qu jv ju)
              (complexTrans (A.subCCongruent (A.subCCongruent (qj v) (qj p)) (C.≈C-refl _))
                (complexTrans (A.subCCongruent (Jincrement v h) (C.≈C-refl _))
                  (complexSym (Alg.mulSub e jD ju)))))
          rhs = complexTrans (complexSym (L.complexMultiplyAssociative qv e (qinv *C a)))
            (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative qv e) (C.≈C-refl _))
              (complexTrans (L.complexMultiplyAssociative e qv (qinv *C a))
                (A.mulCCongruent (C.≈C-refl _)
                  (complexTrans (complexSym (L.complexMultiplyAssociative qv qinv a))
                    (complexTrans (A.mulCCongruent (Rec.multiplyReciprocal qv (G.qNonzero v)) (C.≈C-refl _))
                      (L.complexMultiplyLeftIdentity a))))))
      in Cancel.cancelLeft qv _ _ (G.qNonzero v) (complexTrans clear (complexSym rhs))
      where
      clearRearrange : ∀ a b x y → (a *C x -C a *C y) ≈C ((a *C x -C b *C y) -C (a -C b) *C y)
      clearRearrange (C.complex ar ai) (C.complex br bi) (C.complex xr xi) (C.complex yr yi) =
        (let open P.ℝ-Solver in solve 8
          (λ a b c d x y u v →
            (a ⊗ x ⊖ b ⊗ y) ⊖ (a ⊗ u ⊖ b ⊗ v)
            ⊜ ((a ⊗ x ⊖ b ⊗ y) ⊖ (c ⊗ u ⊖ d ⊗ v))
              ⊖ ((a ⊖ c) ⊗ u ⊖ (b ⊖ d) ⊗ v)) P.≃-refl ar ai br bi xr xi yr yi) ,
        (let open P.ℝ-Solver in solve 8
          (λ a b c d x y u v →
            (a ⊗ y ⊕ b ⊗ x) ⊖ (a ⊗ v ⊕ b ⊗ u)
            ⊜ ((a ⊗ y ⊕ b ⊗ x) ⊖ (c ⊗ v ⊕ d ⊗ u))
              ⊖ ((a ⊖ c) ⊗ v ⊕ (b ⊖ d) ⊗ u)) P.≃-refl ar ai br bi xr xi yr yi)

    jquotLimit : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (inside : ∀ n → S.Inside (q (v n))) → Lim.Conv (λ n → q (v n)) (q p) →
      Lim.Conv (λ n → jquot (v n) (inside n)) (jquot p centerInside)
    jquotLimit v inside cv = Conv.mulConv
      (Conv.inverseLimit (G.qNonzero p) cv (λ n → Rec.multiplyReciprocal (q (v n)) (G.qNonzero (v n))))
      (Lim.subConv (S.quotientLimit (q p) centerInside (λ n → q (v n)) inside cv) (Lim.constantC (G.j p)))

    actualJet : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (inside : ∀ n → S.Inside (q (v n))) → Lim.Conv (λ n → q (v n)) (q p) →
      Jet.Jet (λ n → q (v n) -C q p) (λ n → G.j (v n)) (G.j p) (jquot p centerInside)
    actualJet v inside cv = record
      { Jet.quotient = λ n → jquot (v n) (inside n)
      ; Jet.factor = λ n → jincrement (v n) (inside n)
      ; Jet.limit = jquotLimit v inside cv }

    actualContinuous : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (inside : ∀ n → S.Inside (q (v n))) → Lim.Conv (λ n → q (v n)) (q p) →
      Lim.Conv (λ n → G.j (v n)) (G.j p)
    actualContinuous v inside cv = Jet.continuous
      (Lim.limitTransport (Prod.differenceSelf (q p)) (Lim.subConv cv (Lim.constantC (q p))))
      (actualJet v inside cv)
