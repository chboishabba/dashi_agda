module DASHI.Moonshine.JInvariantBishopDiskSetoidTransportExact where

-- Source-written, kernel pending. The canonical disk completions are
-- extensional in their literal q parameter, even when the radii and
-- convergence witnesses differ. This is a theorem of the actual sums.
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; _/_)
open import Data.Integer.Base using (+_)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.JInvariantBishopEvenZetaNormalizationExact as Z
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorModularityExact as Mod
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeFourierSameObjectExact as Same
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)

prefix : (Nat → BishopComplex) → Nat → BishopComplex
prefix f n = C.complex (Seq.SeriesOf (C.realTerms f) n) (Seq.SeriesOf (C.imagTerms f) n)

prefixCong : ∀ f g → (∀ n → f n ≈C g n) → ∀ n → prefix f n ≈C prefix g n
prefixCong f g h n =
  Z.prefixCong (C.realTerms f) (C.realTerms g) (λ k → proj₁ (h k)) n ,
  Z.prefixCong (C.imagTerms f) (C.imagTerms g) (λ k → proj₂ (h k)) n

sameSeries : ∀ f g v w → (∀ n → f n ≈C g n) →
  C.ComplexSeriesConvergesTo f v → C.ComplexSeriesConvergesTo g w → v ≈C w
sameSeries f g v w h cv cw = Mod.limitUnique (prefix g) v w
  (Mod.limitCong (prefix f) (prefix g) v (prefixCong f g h)
    (C.realConverges cv , C.imagConverges cv))
  (C.realConverges cw , C.imagConverges cw)

module Disks {q q' : BishopComplex} {r r' : R.ℝ}
  (d : Disk.BishopUnitDiskQ q r) (d' : Disk.BishopUnitDiskQ q' r')
  (eq : q ≈C q') where

  u = Disk.unitInterval d
  u' = Disk.unitInterval d'
  e = Disk.powerEnvelope d
  e' = Disk.powerEnvelope d'

  tail4 : E.e4BishopTailLimit q u e ≈C E.e4BishopTailLimit q' u' e'
  tail4 = sameSeries (E.e4BishopTerm q) (E.e4BishopTerm q') _ _
    (λ n → A.scaleCCongruent (A.powCCongruent eq (suc n)) (E.e4CoefficientReal n))
    (E.e4BishopTailConvergence q u e) (E.e4BishopTailConvergence q' u' e')

  tail6 : E.e6BishopUnsignedTailLimit q u e ≈C E.e6BishopUnsignedTailLimit q' u' e'
  tail6 = sameSeries (E.e6BishopUnsignedTerm q) (E.e6BishopUnsignedTerm q') _ _
    (λ n → A.scaleCCongruent (A.powCCongruent eq (suc n)) (E.e6CoefficientReal n))
    (E.e6BishopUnsignedTailConvergence q u e) (E.e6BishopUnsignedTailConvergence q' u' e')

  e4 : E.e4BishopLimit q u e ≈C E.e4BishopLimit q' u' e'
  e4 = A.addCCongruent (C.≈C-refl _) tail4

  e6 : E.e6BishopLimit q u e ≈C E.e6BishopLimit q' u' e'
  e6 = A.subCCongruent (C.≈C-refl _) tail6

module At (inputs : Round11.BishopCutset) where
  module Ph = Phase.At inputs
  module Q = Same.For inputs
  module K = J.At inputs

  exponentCong : ∀ p p' → U.tau p ≈C U.tau p' →
    Ph.exponent p ≈C Ph.exponent p'
  exponentCong p p' (hr , hi) = P.-‿cong (P.*-congˡ hi) , P.*-congˡ hr

  qCong : ∀ p p' → U.tau p ≈C U.tau p' → Ph.q p ≈C Ph.q p'
  qCong p p' h = Weld.originalBishopExpOnSeriesCongruent Ph.T (exponentCong p p' h)

  e4Cong : ∀ p p' → U.tau p ≈C U.tau p' → Q.qE4 p ≈C Q.qE4 p'
  e4Cong p p' h = Disks.e4 (Ph.disk p) (Ph.disk p') (qCong p p' h)

  e6Cong : ∀ p p' → U.tau p ≈C U.tau p' → Q.qE6 p ≈C Q.qE6 p'
  e6Cong p p' h = Disks.e6 (Ph.disk p) (Ph.disk p') (qCong p p' h)

  nCong : ∀ p p' → U.tau p ≈C U.tau p' → K.N p ≈C K.N p'
  nCong p p' h = J.cubeCong (e4Cong p p' h)

  dCong : ∀ p p' → U.tau p ≈C U.tau p' → K.D p ≈C K.D p'
  dCong p p' h = J.deltaCong (e4Cong p p' h) (e6Cong p p' h)

  guardCong : ∀ p p' → U.tau p ≈C U.tau p' → K.Guard p → K.Guard p'
  guardCong p p' h = Phase.guardCong (dCong p p' h)

  jCong : ∀ p p' → U.tau p ≈C U.tau p' →
    (a : K.Guard p) (b : K.Guard p') → K.j p a ≈C K.j p' b
  jCong p p' h a b = J.quotCong (nCong p p' h) (dCong p p' h) a b
