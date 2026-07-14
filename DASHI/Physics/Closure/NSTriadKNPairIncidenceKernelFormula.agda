module DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Nat using (_≤_; _+_; z≤n)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation

------------------------------------------------------------------------
-- Finite fiber support used by the fail-closed target below.

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

weightedListSum :
  {A : Set} →
  (A → Nat) →
  List A → Nat
weightedListSum weight [] = zero
weightedListSum weight (x ∷ xs) =
  weight x + weightedListSum weight xs

------------------------------------------------------------------------
-- The old kernel-formula surface was too strong: it called the diagonal
-- non-residual count an actual physical kernel and stored both the formula
-- and nonnegativity claims as untyped Set markers.  The constructive object
-- below is explicitly only the legacy proxy.  It is useful for compatibility
-- and arithmetic tests, but it is not an actual triad enumeration.

record ActualPairIncidenceKernelFormulaData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkActualPairIncidenceKernelFormulaData
  field
    FiniteIndex : Set
    TailIndex : Set

    proxyKernel : FiniteIndex → TailIndex → Nat

    proxyTriadWeight : FiniteIndex → TailIndex → Nat

    proxyKernelFormula :
      (f : FiniteIndex) →
      (t : TailIndex) →
      proxyKernel f t ≡ proxyTriadWeight f t

    proxyKernelNonnegative :
      (f : FiniteIndex) →
      (t : TailIndex) →
      zero ≤ proxyKernel f t

open ActualPairIncidenceKernelFormulaData public

UnitShellActualPairIncidenceKernelFormulaDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellActualPairIncidenceKernelFormulaDataTarget residueNormModel =
  ActualPairIncidenceKernelFormulaData residueNormModel (suc zero)

------------------------------------------------------------------------
-- Exact missing upstream inputs.
--
-- A physical formula needs a retained positive-sector fiber for every
-- source/target pair, a way to map fiber elements to triad incidences, and a
-- finite weighted aggregate for that fiber.  The completeness map is
-- deliberately a field of the target rather than an unproved proposition.

record RetainedTriadFiberEnumerationInputs
    (FiniteIndex : Set)
    (TailIndex : Set)
    (TriadIncidence : Set)
    (sourceIndex : TriadIncidence → FiniteIndex)
    (targetIndex : TriadIncidence → TailIndex)
    (retainedPositiveSector : TriadIncidence → Set)
    (triadWeight : TriadIncidence → Nat) : Set₁ where
  constructor mkRetainedTriadFiberEnumerationInputs
  field
    fiber : FiniteIndex → TailIndex → List TriadIncidence

    fiberSourceAgreement :
      {f : FiniteIndex} →
      {t : TailIndex} →
      (r : TriadIncidence) →
      r ∈ fiber f t →
      sourceIndex r ≡ f

    fiberTargetAgreement :
      {f : FiniteIndex} →
      {t : TailIndex} →
      (r : TriadIncidence) →
      r ∈ fiber f t →
      targetIndex r ≡ t

    fiberRetainedAgreement :
      {f : FiniteIndex} →
      {t : TailIndex} →
      (r : TriadIncidence) →
      r ∈ fiber f t →
      retainedPositiveSector r

    triadToFiber :
      {f : FiniteIndex} →
      {t : TailIndex} →
      (r : TriadIncidence) →
      sourceIndex r ≡ f →
      targetIndex r ≡ t →
      retainedPositiveSector r →
      r ∈ fiber f t

    fiberAggregate :
      FiniteIndex → TailIndex → Nat

    fiberAggregateIsFiniteWeightedSum :
      (f : FiniteIndex) →
      (t : TailIndex) →
      fiberAggregate f t
        ≡ weightedListSum triadWeight (fiber f t)

------------------------------------------------------------------------
-- Fail-closed physical formula target.
--
-- There is intentionally no canonical inhabitant.  In particular, the
-- diagonal proxy above is not used here.  A future proof must supply the
-- actual retained-sector fiber data, its finite weighted aggregation, and
-- the formula/nonnegativity equalities below.

record ActualPairIncidenceKernelFormulaTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkActualPairIncidenceKernelFormulaTarget
  field
    FiniteIndex : Set
    TailIndex : Set
    TriadIncidence : Set

    sourceIndex : TriadIncidence → FiniteIndex
    targetIndex : TriadIncidence → TailIndex
    retainedPositiveSector : TriadIncidence → Set

    triadWeight : TriadIncidence → Nat

    enumeration :
      RetainedTriadFiberEnumerationInputs
        FiniteIndex
        TailIndex
        TriadIncidence
        sourceIndex
        targetIndex
        retainedPositiveSector
        triadWeight

    actualKernel : FiniteIndex → TailIndex → Nat

    actualKernelFormula :
      (f : FiniteIndex) →
      (t : TailIndex) →
      actualKernel f t
        ≡ RetainedTriadFiberEnumerationInputs.fiberAggregate enumeration f t

    actualKernelNonnegative :
      (f : FiniteIndex) →
      (t : TailIndex) →
      zero ≤ actualKernel f t

------------------------------------------------------------------------
-- Constructive proxy only.  The name is retained for compatibility with
-- older import surfaces; its fields and comments make its status explicit.

canonicalPairIncidenceKernelProxyFormulaData :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellActualPairIncidenceKernelFormulaDataTarget residueNormModel
canonicalPairIncidenceKernelProxyFormulaData residueNormModel =
  mkActualPairIncidenceKernelFormulaData
    (Relation.ConcreteNonResidualFiniteIndex (suc zero))
    (Relation.ConcreteNonResidualTailIndex (suc zero))
    Relation.concreteNonResidualPairIncidenceCount
    Relation.concreteNonResidualPairIncidenceCount
    (λ f t → refl)
    (λ f t → z≤n)

------------------------------------------------------------------------
-- The physical formula remains open.  These flags are intentionally false;
-- the proxy must not promote the actual-kernel or Clay-facing lanes.

actualPairIncidenceKernelFormulaDataClosed : Bool
actualPairIncidenceKernelFormulaDataClosed = false

actualPairIncidenceKernelFormulaDataClosedIsFalse :
  actualPairIncidenceKernelFormulaDataClosed ≡ false
actualPairIncidenceKernelFormulaDataClosedIsFalse = refl

actualUnitShellPairIncidenceKernelFormulaDataClosed : Bool
actualUnitShellPairIncidenceKernelFormulaDataClosed = false

actualUnitShellPairIncidenceKernelFormulaDataClosedIsFalse :
  actualUnitShellPairIncidenceKernelFormulaDataClosed ≡ false
actualUnitShellPairIncidenceKernelFormulaDataClosedIsFalse = refl
