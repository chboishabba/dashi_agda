module DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerExact where

------------------------------------------------------------------------
-- BISHOP q-SERIES <-> LATTICE EISENSTEIN SAME-OBJECT COMPILER
--
-- CROSS-POLLINATION
--
-- The unit-disk E4/E6 theorem now lives on the concrete Bishop setoid complex
-- carrier.  The repository's SL2(Z) lattice-index proof is reusable once its
-- equality boundary is weakened from propositional equality to the same Bishop
-- complex setoid relation.
--
-- This module does two things:
--
--   1. specializes the generic setoid Eisenstein reindexing theorem to the
--      Bishop complex algebra already used by the q-series convergence proof;
--
--   2. isolates the genuine remaining Fourier/same-object theorem:
--
--        E4_q(tau) ~= G4_lattice(tau)
--        E6_q(tau) ~= G6_lattice(tau).
--
-- Once those two witnesses are supplied pointwise, the weight-4 and weight-6
-- transformation laws for the q-series side compile automatically.  No second
-- modularity theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)

import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.SetoidEisensteinTransformationExact as Setoid
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Legacy

bishopComplexTrans :
  ∀ {x y z : Complex.BishopComplex} →
  Complex._≈C_ x y →
  Complex._≈C_ y z →
  Complex._≈C_ x z
bishopComplexTrans (xr , xi) (yr , yi) =
  BishopP.≃-trans xr yr , BishopP.≃-trans xi yi

bishopComplexSym :
  ∀ {x y : Complex.BishopComplex} →
  Complex._≈C_ x y →
  Complex._≈C_ y x
bishopComplexSym (xr , xi) =
  BishopP.≃-sym xr , BishopP.≃-sym xi

record BishopLatticeEisensteinModel : Set₁ where
  field
    Parameter : Set
    actParameter : Legacy.SL2Z → Parameter → Parameter
    denominator : Legacy.SL2Z → Parameter → Complex.BishopComplex

    summand :
      Nat → Legacy.LatticePoint → Parameter → Complex.BishopComplex
    latticeSum :
      (Legacy.LatticePoint → Complex.BishopComplex) →
      Complex.BishopComplex

    pointwiseCongruence :
      ∀ {f h : Legacy.LatticePoint → Complex.BishopComplex} →
      ((p : Legacy.LatticePoint) → Complex._≈C_ (f p) (h p)) →
      Complex._≈C_ (latticeSum f) (latticeSum h)

    reindexInvariant :
      (g : Legacy.SL2Z) →
      (f : Legacy.LatticePoint → Complex.BishopComplex) →
      Complex._≈C_
        (latticeSum (λ p → f (Legacy.forwardIndex g p)))
        (latticeSum f)

    factorOut :
      (factor : Complex.BishopComplex) →
      (f : Legacy.LatticePoint → Complex.BishopComplex) →
      Complex._≈C_
        (latticeSum (λ p → Algebra._*C_ factor (f p)))
        (Algebra._*C_ factor (latticeSum f))

    summandTransformation :
      (weight : Nat) →
      (g : Legacy.SL2Z) →
      (tau : Parameter) →
      (p : Legacy.LatticePoint) →
      Complex._≈C_
        (summand weight p (actParameter g tau))
        (Algebra._*C_
          (Algebra.powC (denominator g tau) weight)
          (summand weight (Legacy.forwardIndex g p) tau))

open BishopLatticeEisensteinModel public

asSetoidEisensteinModel :
  BishopLatticeEisensteinModel →
  Setoid.SetoidEisensteinAnalyticModel
asSetoidEisensteinModel M =
  record
    { Setoid.Scalar = Complex.BishopComplex
    ; Setoid._≈ˢ_ = Complex._≈C_
    ; Setoid.equivTrans = bishopComplexTrans
    ; Setoid._*ˢ_ = Algebra._*C_
    ; Setoid.Parameter = Parameter M
    ; Setoid.actParameter = actParameter M
    ; Setoid.denominator = denominator M
    ; Setoid.power = Algebra.powC
    ; Setoid.summand = summand M
    ; Setoid.eisensteinSum = latticeSum M
    ; Setoid.pointwiseCongruence = pointwiseCongruence M
    ; Setoid.reindexInvariant = reindexInvariant M
    ; Setoid.factorOut = factorOut M
    ; Setoid.summandTransformation = summandTransformation M
    }

BishopLatticeEisensteinSeries :
  (M : BishopLatticeEisensteinModel) →
  Nat → Parameter M → Complex.BishopComplex
BishopLatticeEisensteinSeries M =
  Setoid.SetoidEisensteinSeries (asSetoidEisensteinModel M)

bishopLatticeEisensteinTransformation :
  (M : BishopLatticeEisensteinModel) →
  (weight : Nat) →
  (g : Legacy.SL2Z) →
  (tau : Parameter M) →
  Complex._≈C_
    (BishopLatticeEisensteinSeries M weight (actParameter M g tau))
    (Algebra._*C_
      (Algebra.powC (denominator M g tau) weight)
      (BishopLatticeEisensteinSeries M weight tau))
bishopLatticeEisensteinTransformation M =
  Setoid.setoidEisensteinTransformation (asSetoidEisensteinModel M)

------------------------------------------------------------------------
-- The actual same-object/Fourier-expansion seam.
------------------------------------------------------------------------

record BishopQSeriesLatticeSameObject
    (M : BishopLatticeEisensteinModel)
    (qE4 qE6 : Parameter M → Complex.BishopComplex) : Set₁ where
  field
    e4SameObject :
      (tau : Parameter M) →
      Complex._≈C_
        (qE4 tau)
        (BishopLatticeEisensteinSeries M 4 tau)

    e6SameObject :
      (tau : Parameter M) →
      Complex._≈C_
        (qE6 tau)
        (BishopLatticeEisensteinSeries M 6 tau)

open BishopQSeriesLatticeSameObject public

qSeriesE4Transformation :
  (M : BishopLatticeEisensteinModel) →
  (qE4 qE6 : Parameter M → Complex.BishopComplex) →
  (same : BishopQSeriesLatticeSameObject M qE4 qE6) →
  (g : Legacy.SL2Z) →
  (tau : Parameter M) →
  Complex._≈C_
    (qE4 (actParameter M g tau))
    (Algebra._*C_
      (Algebra.powC (denominator M g tau) 4)
      (qE4 tau))
qSeriesE4Transformation M qE4 qE6 same g tau =
  bishopComplexTrans
    (e4SameObject same (actParameter M g tau))
    (bishopComplexTrans
      (bishopLatticeEisensteinTransformation M 4 g tau)
      (Algebra.mulCCongruent
        (Complex.≈C-refl
          (Algebra.powC (denominator M g tau) 4))
        (bishopComplexSym (e4SameObject same tau))))

qSeriesE6Transformation :
  (M : BishopLatticeEisensteinModel) →
  (qE4 qE6 : Parameter M → Complex.BishopComplex) →
  (same : BishopQSeriesLatticeSameObject M qE4 qE6) →
  (g : Legacy.SL2Z) →
  (tau : Parameter M) →
  Complex._≈C_
    (qE6 (actParameter M g tau))
    (Algebra._*C_
      (Algebra.powC (denominator M g tau) 6)
      (qE6 tau))
qSeriesE6Transformation M qE4 qE6 same g tau =
  bishopComplexTrans
    (e6SameObject same (actParameter M g tau))
    (bishopComplexTrans
      (bishopLatticeEisensteinTransformation M 6 g tau)
      (Algebra.mulCCongruent
        (Complex.≈C-refl
          (Algebra.powC (denominator M g tau) 6))
        (bishopComplexSym (e6SameObject same tau))))

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

record BishopLatticeEisensteinCrossPollinationFrontier : Set where
  field
    existingSL2ZLatticeBijectionReused : Bool
    setoidNativeReindexingTheoremExact : Bool
    bishopComplexCarrierSpecialized : Bool
    qSeriesModularityCompilesFromSameObject : Bool
    concreteBishopLatticeSummandAndAbsoluteSumPaidHere : Bool
    qSeriesEqualsLatticeE4E6PaidHere : Bool

canonicalBishopLatticeEisensteinCrossPollinationFrontier :
  BishopLatticeEisensteinCrossPollinationFrontier
canonicalBishopLatticeEisensteinCrossPollinationFrontier = record
  { existingSL2ZLatticeBijectionReused = true
  ; setoidNativeReindexingTheoremExact = true
  ; bishopComplexCarrierSpecialized = true
  ; qSeriesModularityCompilesFromSameObject = true
  ; concreteBishopLatticeSummandAndAbsoluteSumPaidHere = false
  ; qSeriesEqualsLatticeE4E6PaidHere = false
  }
