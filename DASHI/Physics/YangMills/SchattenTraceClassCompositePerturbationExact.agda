module DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact where

------------------------------------------------------------------------
-- ROUND77: TRACE IDEALS, RELATIVE TRACE CLASS, AND SPECTRAL SHIFT
--
-- SOURCES
--
-- Fuad Kittaneh,
-- "Inequalities for the Schatten p-Norm",
-- Glasgow Mathematical Journal 26 (1985), 141--143.
-- DOI: 10.1017/S0017089500005905.
--
-- Julio Delgado and Michael Ruzhansky,
-- "Schatten-von Neumann Classes of Integral Operators",
-- Journal de Mathematiques Pures et Appliquees 154 (2021), 1--29.
-- DOI: 10.1016/j.matpur.2021.08.006.
-- Their (1.5) gives S_p subset S_q for 0<p<q<=infinity, with S_infinity the
-- compact operators. Thus trace class -> Hilbert--Schmidt -> compact.
--
-- A. B. Aleksandrov and V. V. Peller,
-- "Functions of Compact Operators under Trace Class Perturbations",
-- St. Petersburg Mathematical Journal 36(4) (2025).
-- DOI: 10.1090/spmj/1843. arXiv:2402.09843.
-- For compact self-adjoint A,B, preservation of trace-class differences by f
-- is characterized by operator-Lipschitz behaviour near zero.
--
-- A. B. Aleksandrov and V. V. Peller,
-- "Functions of Self-Adjoint Operators under Relatively Bounded and Relatively
-- Trace Class Perturbations", Mathematische Nachrichten 298(9) (2025),
-- 3027--3048. DOI: 10.1002/mana.70000.
--
-- Companion short note:
-- A. B. Aleksandrov and V. V. Peller,
-- "Relatively Bounded and Relatively Trace Class Perturbations",
-- Comptes Rendus. Mathematique 363 (2025), 377--382.
-- DOI: 10.5802/crmath.722.
--
-- In this setting K=B-A is relatively trace class with respect to A when the
-- resolvent-weighted perturbation K(A+iI)^(-1) is trace class. They introduce
-- relatively operator-Lipschitz functions and obtain a trace formula for
-- relatively trace-class perturbations. This is the appropriate abstract lane
-- for unbounded self-adjoint Hamiltonian/generator comparisons when its
-- hypotheses can actually be proved.
--
-- V. V. Peller,
-- "Multiple Operator Integrals in Perturbation Theory",
-- Bulletin of Mathematical Sciences 6 (2016), 15--88.
-- DOI: 10.1007/s13373-015-0073-y.
-- Section 1.6 reviews the Lifshits--Krein trace formula: for self-adjoint A,B
-- with A-B in S_1 there is a real spectral-shift function xi with
--
--   trace(f(B)-f(A)) = integral f'(s) xi(s) ds
--
-- for the stated admissible function class.
--
-- D. R. Yafaev,
-- "The Schrodinger Operator: Perturbation Determinants, the Spectral Shift
-- Function, Trace Identities, and All That",
-- Functional Analysis and Its Applications 41(3) (2007), 217--236.
-- DOI: 10.1007/s10688-007-0019-6.
-- Yafaev reviews Krein spectral-shift / perturbation-determinant machinery.
--
-- AUTHORITY BOUNDARY
--
-- None of these theorems is a generic Yang--Mills OPE theorem. The functional
-- transport below applies only when the physical coordinate is genuinely a
-- self-adjoint spectral operator and the required absolute/relative trace-class
-- hypothesis is proved. The finite lattice FP log-det remains finite-dimensional
-- and does not need Krein theory merely to justify its existing trace-log step.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record SchattenHierarchyAuthority : Set₁ where
  field
    Operator : Set
    TraceClass HilbertSchmidt Compact : Operator → Set

    traceToHilbertSchmidt : ∀ {A} → TraceClass A → HilbertSchmidt A
    hilbertSchmidtToCompact : ∀ {A} → HilbertSchmidt A → Compact A

open SchattenHierarchyAuthority public

traceClassToCompact :
  (A : SchattenHierarchyAuthority) →
  ∀ {op} → TraceClass A op → Compact A op
traceClassToCompact A trace =
  hilbertSchmidtToCompact A (traceToHilbertSchmidt A trace)

------------------------------------------------------------------------
-- Compact self-adjoint absolute trace-class transport.
------------------------------------------------------------------------

record SelfAdjointTraceClassFunctionalTransport : Set₁ where
  field
    Operator Function : Set

    CompactSelfAdjoint : Operator → Set
    TraceClassDifference : Operator → Operator → Set
    Apply : Function → Operator → Operator
    OperatorLipschitzNearZero : Function → Set

    sourceTransport :
      ∀ f A B →
      OperatorLipschitzNearZero f →
      CompactSelfAdjoint A →
      CompactSelfAdjoint B →
      TraceClassDifference A B →
      TraceClassDifference (Apply f A) (Apply f B)

open SelfAdjointTraceClassFunctionalTransport public

record CompositeSpectralPerturbation
    (T : SelfAdjointTraceClassFunctionalTransport) : Set₁ where
  field
    left right : Operator T
    compositeFunction : Function T

    leftCompactSelfAdjoint : CompactSelfAdjoint T left
    rightCompactSelfAdjoint : CompactSelfAdjoint T right
    baseTraceClassDifference : TraceClassDifference T left right
    compositeOperatorLipschitz :
      OperatorLipschitzNearZero T compositeFunction

open CompositeSpectralPerturbation public

compositeSpectralDifferenceIsTraceClass :
  (T : SelfAdjointTraceClassFunctionalTransport) →
  (dataSet : CompositeSpectralPerturbation T) →
  TraceClassDifference T
    (Apply T (compositeFunction dataSet) (left dataSet))
    (Apply T (compositeFunction dataSet) (right dataSet))
compositeSpectralDifferenceIsTraceClass T dataSet =
  sourceTransport T
    (compositeFunction dataSet)
    (left dataSet)
    (right dataSet)
    (compositeOperatorLipschitz dataSet)
    (leftCompactSelfAdjoint dataSet)
    (rightCompactSelfAdjoint dataSet)
    (baseTraceClassDifference dataSet)

------------------------------------------------------------------------
-- Unbounded/self-adjoint relative trace-class transport.
--
-- The source's resolvent-weighted definition is represented explicitly by the
-- `RelativeTraceClassDifference` predicate rather than weakened to ordinary
-- trace class. The source theorem owns the analytic DOI/double-operator-integral
-- work; the compiler below only applies it to a declared composite function.
------------------------------------------------------------------------

record RelativeTraceClassFunctionalTransport : Set₁ where
  field
    Operator Function : Set

    SelfAdjoint : Operator → Set
    RelativeTraceClassDifference : Operator → Operator → Set
    TraceClassDifference : Operator → Operator → Set
    Apply : Function → Operator → Operator
    RelativelyOperatorLipschitz : Function → Set

    -- Source-native interpretation: for B=A+K, this means the appropriate
    -- resolvent-weighted perturbation K(A+iI)^(-1) belongs to S_1.
    resolventWeightedMeaning : ∀ A B →
      RelativeTraceClassDifference A B → Set

    sourceRelativeTransport :
      ∀ f A B →
      RelativelyOperatorLipschitz f →
      SelfAdjoint A →
      SelfAdjoint B →
      RelativeTraceClassDifference A B →
      TraceClassDifference (Apply f A) (Apply f B)

open RelativeTraceClassFunctionalTransport public

record RelativeCompositeSpectralPerturbation
    (T : RelativeTraceClassFunctionalTransport) : Set₁ where
  field
    reference perturbed : Operator T
    compositeFunction : Function T

    referenceSelfAdjoint : SelfAdjoint T reference
    perturbedSelfAdjoint : SelfAdjoint T perturbed
    relativeTraceClass :
      RelativeTraceClassDifference T reference perturbed
    relativeTraceClassHasResolventMeaning :
      resolventWeightedMeaning T reference perturbed relativeTraceClass
    compositeRelativelyOperatorLipschitz :
      RelativelyOperatorLipschitz T compositeFunction

open RelativeCompositeSpectralPerturbation public

relativeCompositeDifferenceIsTraceClass :
  (T : RelativeTraceClassFunctionalTransport) →
  (dataSet : RelativeCompositeSpectralPerturbation T) →
  TraceClassDifference T
    (Apply T (compositeFunction dataSet) (reference dataSet))
    (Apply T (compositeFunction dataSet) (perturbed dataSet))
relativeCompositeDifferenceIsTraceClass T dataSet =
  sourceRelativeTransport T
    (compositeFunction dataSet)
    (reference dataSet)
    (perturbed dataSet)
    (compositeRelativelyOperatorLipschitz dataSet)
    (referenceSelfAdjoint dataSet)
    (perturbedSelfAdjoint dataSet)
    (relativeTraceClass dataSet)

------------------------------------------------------------------------
-- Spectral-shift trace-formula interface.
--
-- This keeps the computable scalar consumer separate from the operator-ideal
-- theorem. A concrete application must build the spectral-shift object for the
-- SAME operator pair and identify its integral with the trace consumer.
------------------------------------------------------------------------

record LifshitsKreinTraceFormulaAuthority : Set₁ where
  field
    Operator Function SpectralShift Scalar : Set

    SelfAdjoint : Operator → Set
    TraceClassDifference : Operator → Operator → Set
    AdmissibleFunction : Function → Set
    spectralShift : Operator → Operator → SpectralShift
    functionDifferenceTrace : Function → Operator → Operator → Scalar
    derivativeAgainstShiftIntegral :
      Function → SpectralShift → Scalar

    sourceTraceFormula : ∀ f A B →
      SelfAdjoint A →
      SelfAdjoint B →
      TraceClassDifference A B →
      AdmissibleFunction f →
      functionDifferenceTrace f A B
      ≡ derivativeAgainstShiftIntegral f (spectralShift A B)

open LifshitsKreinTraceFormulaAuthority public

record SpectralShiftCompositeTrace
    (T : LifshitsKreinTraceFormulaAuthority) : Set₁ where
  field
    reference perturbed : Operator T
    compositeFunction : Function T
    referenceSelfAdjoint : SelfAdjoint T reference
    perturbedSelfAdjoint : SelfAdjoint T perturbed
    baseTraceClassDifference : TraceClassDifference T reference perturbed
    compositeFunctionAdmissible : AdmissibleFunction T compositeFunction

open SpectralShiftCompositeTrace public

compositeTraceEqualsSpectralShiftIntegral :
  (T : LifshitsKreinTraceFormulaAuthority) →
  (dataSet : SpectralShiftCompositeTrace T) →
  functionDifferenceTrace T
    (compositeFunction dataSet) (reference dataSet) (perturbed dataSet)
  ≡ derivativeAgainstShiftIntegral T
      (compositeFunction dataSet)
      (spectralShift T (reference dataSet) (perturbed dataSet))
compositeTraceEqualsSpectralShiftIntegral T dataSet =
  sourceTraceFormula T
    (compositeFunction dataSet)
    (reference dataSet)
    (perturbed dataSet)
    (referenceSelfAdjoint dataSet)
    (perturbedSelfAdjoint dataSet)
    (baseTraceClassDifference dataSet)
    (compositeFunctionAdmissible dataSet)

------------------------------------------------------------------------
-- Perturbation determinant / spectral-shift relation is kept as its own source
-- authority. This can later calibrate a continuum ghost determinant if the SAME
-- reduced FP operator pair satisfies the required self-adjoint trace-class or
-- relative-trace-class hypotheses. It is not needed for the finite determinant.
------------------------------------------------------------------------

record PerturbationDeterminantSpectralShiftAuthority : Set₁ where
  field
    Operator SpectralParameter DeterminantValue SpectralShiftValue : Set
    SelfAdjoint : Operator → Set
    TraceClassDifference : Operator → Operator → Set
    perturbationDeterminant :
      Operator → Operator → SpectralParameter → DeterminantValue
    spectralShiftValue :
      Operator → Operator → SpectralParameter → SpectralShiftValue
    determinantBoundaryArgumentGivesShift : ∀ A B λ →
      SelfAdjoint A →
      SelfAdjoint B →
      TraceClassDifference A B → Set

open PerturbationDeterminantSpectralShiftAuthority public

------------------------------------------------------------------------
-- Normal/non-self-adjoint boundary.
------------------------------------------------------------------------

record NormalOperatorExtensionBoundary : Set₁ where
  field
    NormalOperator : Set
    TraceClassDifferenceNormal : NormalOperator → NormalOperator → Set
    CandidateFunctionalTransport : Set

open NormalOperatorExtensionBoundary public

schattenHierarchySourceLevel : ProofLevel
schattenHierarchySourceLevel = standardImported

operatorLipschitzTraceClassSourceLevel : ProofLevel
operatorLipschitzTraceClassSourceLevel = standardImported

relativeOperatorLipschitzTraceClassSourceLevel : ProofLevel
relativeOperatorLipschitzTraceClassSourceLevel = standardImported

lifshitsKreinTraceFormulaSourceLevel : ProofLevel
lifshitsKreinTraceFormulaSourceLevel = standardImported

perturbationDeterminantSpectralShiftSourceLevel : ProofLevel
perturbationDeterminantSpectralShiftSourceLevel = standardImported

traceClassToCompactCompositionLevel : ProofLevel
traceClassToCompactCompositionLevel = machineChecked

compositeSpectralTraceClassTransportLevel : ProofLevel
compositeSpectralTraceClassTransportLevel = machineChecked

relativeCompositeSpectralTraceClassTransportLevel : ProofLevel
relativeCompositeSpectralTraceClassTransportLevel = machineChecked

spectralShiftTraceFormulaCompilerLevel : ProofLevel
spectralShiftTraceFormulaCompilerLevel = machineChecked

normalOperatorFunctionalTransportLevel : ProofLevel
normalOperatorFunctionalTransportLevel = conditional
