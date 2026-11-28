module DASHI.Moonshine.CM163BishopHecke41ActualJLocalSecondJetExact where

-- SOURCE-WRITTEN, kernel pending. Reuse the actual dyadic inner/outer
-- chart and J=q*j readout from the original first derivative owner.
-- No new modular function or independently assumed derivative.
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ActualJLocalDerivativeExact as First
import DASHI.Moonshine.CM163BishopHecke41StrictDiskSecondMomentExact as Strict
import DASHI.Moonshine.CM163BishopHecke41AffineQuotientJetExact as Divide
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _-C_)
open Comp using (complexSym)

module At (inputs : Round11.BishopCutset) where
  module F = First.At inputs
  module O = F.O
  module G = F.G
  open O using (q; Jvalue; qj)

  module Around (p : U.BishopUpperHalfPlanePoint) where
    module Ref = F.Around p
    module S = Strict.Shrink Ref.outer Ref.inner Ref.onz Ref.inz Ref.s
      (Unit.ratioNonnegative (F.unit Ref.outerPoint))
      (Unit.ratioBelowOne (F.unit Ref.outerPoint)) Ref.ratioUpper
      (E.lift D.Junit) (F.referenceEval Ref.outerPoint)

    J1 J2c : BishopComplex
    J1 = S.inv *C S.firstCoefficient (q p) Ref.centerInside
    J2c = S.inv *C (S.inv *C S.secondCoefficient (q p) Ref.centerInside)

    j1 j2 : BishopComplex
    j1 = Rec.reciprocalC (q p) (G.qNonzero p) *C (J1 -C G.j p)
    j2 = Rec.reciprocalC (q p) (G.qNonzero p) *C (J2c -C j1)

    actualJUnit : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (inside : ∀ n → Ref.S.Inside (q (v n))) →
      Lim.Conv (λ n → q (v n)) (q p) →
      J2.Jet2 (λ n → q (v n) -C q p) (λ n → Jvalue (v n))
        (Jvalue p) J1 J2c
    actualJUnit v inside cv = S.originalTwoJet (q p) Ref.centerInside
      (λ n → q (v n)) inside cv (F.referenceEval p)
      (λ n → F.referenceEval (v n))

    actualJ : (v : Nat → U.BishopUpperHalfPlanePoint) →
      (inside : ∀ n → Ref.S.Inside (q (v n))) →
      Lim.Conv (λ n → q (v n)) (q p) →
      J2.Jet2 (λ n → q (v n) -C q p) (λ n → G.j (v n))
        (G.j p) j1 j2
    actualJ v inside cv =
      Divide.At.actual (λ n → q (v n)) (q p) (λ n → G.qNonzero (v n))
        (G.qNonzero p) cv (λ n → Jvalue (v n)) (λ n → G.j (v n))
        (Jvalue p) (G.j p) J1 J2c (λ n → qj (v n)) (qj p)
        (actualJUnit v inside cv)
