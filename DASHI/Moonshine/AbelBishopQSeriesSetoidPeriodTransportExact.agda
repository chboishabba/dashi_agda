module DASHI.Moonshine.AbelBishopQSeriesSetoidPeriodTransportExact where

-- Literal Bishop q-series extensionality, not a new abstract E4/E6.
-- The two q values and both unit-disk convergence witnesses are ORIGINAL
-- Bishop complex objects. Periodicity requires a genuine q(tau+1)≈q(tau)
-- proof on the selected source domain; this module does not assume exp(2πi)=1.

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as Bishop
import RealProperties as BishopP
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext

originalE4TermCongruent :
  ∀ {q r : Complex.BishopComplex} →
  Complex._≈C_ q r →
  (n : Nat) →
  Complex._≈C_ (E.e4BishopTerm q n) (E.e4BishopTerm r n)
originalE4TermCongruent equivalent n =
  Algebra.scaleCCongruent (Algebra.powCCongruent equivalent (suc n))
    (E.e4CoefficientReal n)

originalE6TermCongruent :
  ∀ {q r : Complex.BishopComplex} →
  Complex._≈C_ q r →
  (n : Nat) →
  Complex._≈C_ (E.e6BishopUnsignedTerm q n)
                 (E.e6BishopUnsignedTerm r n)
originalE6TermCongruent equivalent n =
  Algebra.scaleCCongruent (Algebra.powCCongruent equivalent (suc n))
    (E.e6CoefficientReal n)

originalComplexSeriesLimitExtensional :
  ∀ {left right : Nat → Complex.BishopComplex}
    {leftLimit rightLimit : Complex.BishopComplex} →
  (∀ n → Complex._≈C_ (left n) (right n)) →
  Complex.ComplexSeriesConvergesTo left leftLimit →
  Complex.ComplexSeriesConvergesTo right rightLimit →
  Complex._≈C_ leftLimit rightLimit
originalComplexSeriesLimitExtensional {left} {right}
    termwise leftProof rightProof =
  Seq.uniqueness-of-limits
    (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n {{_}} →
        Ext.seriesPartialSumsCongruent
          (λ k → proj₁ (termwise k)) n)
      (Complex.realConverges leftProof))
    (Complex.realConverges rightProof)
  ,
  Seq.uniqueness-of-limits
    (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n {{_}} →
        Ext.seriesPartialSumsCongruent
          (λ k → proj₂ (termwise k)) n)
      (Complex.imagConverges leftProof))
    (Complex.imagConverges rightProof)

originalBishopE4TailSetoidInvariant :
  ∀ {q r : Complex.BishopComplex}
    {rq rr : Bishop.ℝ} →
  (qDisk : Disk.BishopUnitDiskQ q rq) →
  (rDisk : Disk.BishopUnitDiskQ r rr) →
  Complex._≈C_ q r →
  Complex._≈C_
    (E.e4BishopTailLimit q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e4BishopTailLimit r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))
originalBishopE4TailSetoidInvariant {q} {r} qDisk rDisk eq =
  originalComplexSeriesLimitExtensional
    (originalE4TermCongruent eq)
    (E.e4BishopTailConvergence q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e4BishopTailConvergence r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))

originalBishopE6TailSetoidInvariant :
  ∀ {q r : Complex.BishopComplex}
    {rq rr : Bishop.ℝ} →
  (qDisk : Disk.BishopUnitDiskQ q rq) →
  (rDisk : Disk.BishopUnitDiskQ r rr) →
  Complex._≈C_ q r →
  Complex._≈C_
    (E.e6BishopUnsignedTailLimit q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e6BishopUnsignedTailLimit r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))
originalBishopE6TailSetoidInvariant {q} {r} qDisk rDisk eq =
  originalComplexSeriesLimitExtensional
    (originalE6TermCongruent eq)
    (E.e6BishopUnsignedTailConvergence q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e6BishopUnsignedTailConvergence r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))

originalBishopE4SetoidInvariant :
  ∀ {q r : Complex.BishopComplex}
    {rq rr : Bishop.ℝ} →
  (qDisk : Disk.BishopUnitDiskQ q rq) →
  (rDisk : Disk.BishopUnitDiskQ r rr) →
  Complex._≈C_ q r →
  Complex._≈C_
    (E.e4BishopLimit q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e4BishopLimit r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))
originalBishopE4SetoidInvariant qDisk rDisk eq =
  Algebra.addCCongruent (Complex.≈C-refl Algebra.oneC)
    (originalBishopE4TailSetoidInvariant qDisk rDisk eq)

originalBishopE6SetoidInvariant :
  ∀ {q r : Complex.BishopComplex}
    {rq rr : Bishop.ℝ} →
  (qDisk : Disk.BishopUnitDiskQ q rq) →
  (rDisk : Disk.BishopUnitDiskQ r rr) →
  Complex._≈C_ q r →
  Complex._≈C_
    (E.e6BishopLimit q
      (Disk.unitInterval qDisk) (Disk.powerEnvelope qDisk))
    (E.e6BishopLimit r
      (Disk.unitInterval rDisk) (Disk.powerEnvelope rDisk))
originalBishopE6SetoidInvariant qDisk rDisk eq =
  Algebra.subCCongruent (Complex.≈C-refl Algebra.oneC)
    (originalBishopE6TailSetoidInvariant qDisk rDisk eq)

record OriginalBishopQPeriodSource : Set₁ where
  field
    Height : Set
    translate : Height → Height
    qAt : Height → Complex.BishopComplex
    radius : Height → Bishop.ℝ
    unitDisk : ∀ tau → Disk.BishopUnitDiskQ (qAt tau) (radius tau)
    actualQPeriod : ∀ tau →
      Complex._≈C_ (qAt (translate tau)) (qAt tau)

open OriginalBishopQPeriodSource public

originalBishopQSeriesTPeriodE4 :
  (S : OriginalBishopQPeriodSource) →
  (tau : Height S) →
  Complex._≈C_
    (E.e4BishopLimit (qAt S (translate S tau))
      (Disk.unitInterval (unitDisk S (translate S tau)))
      (Disk.powerEnvelope (unitDisk S (translate S tau))))
    (E.e4BishopLimit (qAt S tau)
      (Disk.unitInterval (unitDisk S tau))
      (Disk.powerEnvelope (unitDisk S tau)))
originalBishopQSeriesTPeriodE4 S tau =
  originalBishopE4SetoidInvariant
    (unitDisk S (translate S tau)) (unitDisk S tau)
    (actualQPeriod S tau)

originalBishopQSeriesTPeriodE6 :
  (S : OriginalBishopQPeriodSource) →
  (tau : Height S) →
  Complex._≈C_
    (E.e6BishopLimit (qAt S (translate S tau))
      (Disk.unitInterval (unitDisk S (translate S tau)))
      (Disk.powerEnvelope (unitDisk S (translate S tau))))
    (E.e6BishopLimit (qAt S tau)
      (Disk.unitInterval (unitDisk S tau))
      (Disk.powerEnvelope (unitDisk S tau)))
originalBishopQSeriesTPeriodE6 S tau =
  originalBishopE6SetoidInvariant
    (unitDisk S (translate S tau)) (unitDisk S tau)
    (actualQPeriod S tau)
