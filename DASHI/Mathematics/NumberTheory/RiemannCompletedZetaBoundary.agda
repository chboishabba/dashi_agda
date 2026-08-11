module DASHI.Mathematics.NumberTheory.RiemannCompletedZetaBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Bernhard Riemann,
-- "Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse" (1859).
-- No DOI was assigned to the original publication.
--
-- Enrico Bombieri,
-- "Problems of the Millennium: The Riemann Hypothesis",
-- Clay Mathematics Institute problem description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Type the analytic zeta/xi package that was missing from the repository's
-- finite Abel-value and Maaß-candidate modules.  Given actual continuation,
-- completion, functional-equation and conjugation laws, the package constructs
-- the exact zero-symmetry interface from RiemannXiSymmetryExact.
--
-- The module also states nontrivial zeros, critical-strip exclusion of trivial
-- zeros, zero counting, the explicit prime/zero formula and RH itself.  None of
-- the analytic fields is filled merely by importing AbelZeta or a Maaß spectral
-- enclosure.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as RX

record CompletedZetaData : Setω where
  field
    Value : Set
    zeta : RX.ComplexCoordinate → Value
    gammaFactor : RX.ComplexCoordinate → Value
    completedXi : RX.ComplexCoordinate → Value
    multiplyValue : Value → Value → Value

    meromorphicContinuation : Set
    uniquePoleAtOne : Set
    dirichletSeriesForRealPartGreaterThanOne : Set
    eulerProductForRealPartGreaterThanOne : Set
    completionFormula : ∀ point →
      completedXi point
      ≡ multiplyValue (gammaFactor point) (zeta point)
    functionalEquation : ∀ point →
      completedXi point
      ≡ completedXi (RX.functionalReflection point)

    conjugateValue : Value → Value
    conjugationLaw : ∀ point →
      completedXi (RX.conjugateCoordinate point)
      ≡ conjugateValue (completedXi point)

    isZeroValue : Value → Set
    zeroTransport : ∀ {left right} →
      left ≡ right → isZeroValue left → isZeroValue right
    conjugatePreservesZero : ∀ value →
      isZeroValue value → isZeroValue (conjugateValue value)

open CompletedZetaData public
open RX.XiZeroSymmetry

completedZetaZeroSymmetry : CompletedZetaData → RX.XiZeroSymmetry
completedZetaZeroSymmetry data = record
  { isXiZero = λ point → isZeroValue data (completedXi data point)
  ; functionalEquationPreservesZero = λ point zeroAtPoint →
      zeroTransport data
        (functionalEquation data point)
        zeroAtPoint
  ; conjugationPreservesZero = λ point zeroAtPoint →
      zeroTransport data
        (sym (conjugationLaw data point))
        (conjugatePreservesZero data (completedXi data point) zeroAtPoint)
  }

record TrivialZeroData (data : CompletedZetaData) : Set₁ where
  field
    isTrivialZero : RX.ComplexCoordinate → Set
    trivialZerosAreNegativeEvenIntegers : Set
    trivialZeroIsZetaZero : ∀ point →
      isTrivialZero point → isZeroValue data (zeta data point)

record NontrivialZeroData (data : CompletedZetaData) : Set₁ where
  field
    coordinate : RX.ComplexCoordinate
    xiZero : RX.isXiZero (completedZetaZeroSymmetry data) coordinate
    inCriticalStrip : RX.CriticalStrip coordinate

open NontrivialZeroData public

record RiemannHypothesis (data : CompletedZetaData) : Set₁ where
  field
    everyNontrivialZeroOnCriticalLine :
      (zero : NontrivialZeroData data) →
      RX.CriticalLine (coordinate zero)

record RiemannZeroCounting (data : CompletedZetaData) : Set₁ where
  field
    Height : Set
    heightOrder : Height → Height → Set
    countNontrivialZeros : Height → Nat
    finiteAtEveryHeight : Set
    riemannVonMangoldtMainTerm : Set
    explicitErrorBound : Set

record RiemannPrimeZeroExplicitFormula (data : CompletedZetaData) : Setω where
  field
    PrimePowerDatum : Set
    TestFunction : Set
    Scalar : Set
    primePowerSide : TestFunction → PrimePowerDatum → Scalar
    nontrivialZeroSide : TestFunction → NontrivialZeroData data → Scalar
    trivialAndArchimedeanSide : TestFunction → Scalar
    explicitFormulaIdentity : Set

record RiemannWeilHilbertPolyaBridge (data : CompletedZetaData) : Setω where
  field
    weilCriterion : RX.WeilPositivityCriterion
    hilbertPolyaCandidate : RX.HilbertPolyaCandidate
    candidateEigenvaluesGiveActualXiZeros : ∀ eigenvector →
      RX.isXiZero (completedZetaZeroSymmetry data)
        (RX.associatedZero hilbertPolyaCandidate eigenvector)
    candidateExhaustsAllNontrivialZeros : Set
    selfAdjointnessProof : Set
    weilPositivityProof : Set
    equivalenceToRH : Set

candidateZerosAreCritical :
  ∀ data (bridge : RiemannWeilHilbertPolyaBridge data) eigenvector →
  RX.CriticalLine
    (RX.associatedZero
      (RiemannWeilHilbertPolyaBridge.hilbertPolyaCandidate bridge)
      eigenvector)
candidateZerosAreCritical data bridge eigenvector =
  RX.hilbertPolyaCandidateZerosLieOnCriticalLine
    (RiemannWeilHilbertPolyaBridge.hilbertPolyaCandidate bridge)
    eigenvector
