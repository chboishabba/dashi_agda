module DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact where

------------------------------------------------------------------------
-- ROUND76: TRACE-IDEAL FACTS USED ONLY WHERE THEIR HYPOTHESES ACTUALLY MATCH
--
-- SOURCES
--
-- Fuad Kittaneh,
-- "Inequalities for the Schatten p-Norm",
-- Glasgow Mathematical Journal 26 (1985), 141--143.
-- DOI: 10.1017/S0017089500005905.
--
-- Kittaneh uses C_1 for trace class, C_2 for Hilbert--Schmidt and C_infty
-- for compact operators.  This is calibration for the hierarchy only.
--
-- Julio Delgado and Michael Ruzhansky,
-- "Schatten-von Neumann Classes of Integral Operators",
-- Journal de Mathematiques Pures et Appliquees 154 (2021), 1--29.
-- DOI: 10.1016/j.matpur.2021.08.006.
--
-- Their equation (1.5) records S_p subset S_q for 0<p<q<=infinity and
-- S_infinity as the compact operators; (1.6)--(1.8) give the Schatten product
-- rule and norm estimate.  Thus trace class -> Hilbert--Schmidt -> compact.
--
-- A. B. Aleksandrov and V. V. Peller,
-- "Functions of Compact Operators under Trace Class Perturbations",
-- St. Petersburg Mathematical Journal 36(4) (2025).
-- DOI: 10.1090/spmj/1843.  arXiv:2402.09843.
--
-- Their Theorem 3.5 states that for compact self-adjoint A,B, preservation of
-- trace-class differences by f is equivalent to operator-Lipschitz behaviour of
-- f on a neighbourhood of zero.  The paper explicitly warns that the analogous
-- compact NORMAL-operator problem is not settled by their method.
--
-- AUTHORITY BOUNDARY
--
-- This theorem is useful for composite observables that are literally spectral
-- functions of a compact SELF-ADJOINT operator coordinate.  It is not a generic
-- OPE theorem and it is not silently applied to nonnormal gauge operators.
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
-- Exact logical form of the Aleksandrov--Peller transport consumed downstream.
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
-- The normal/non-self-adjoint case remains explicitly separate.  This prevents
-- a useful trace-ideal theorem from being over-promoted into a generic gauge
-- composite/OPE stability claim.
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

traceClassToCompactCompositionLevel : ProofLevel
traceClassToCompactCompositionLevel = machineChecked

compositeSpectralTraceClassTransportLevel : ProofLevel
compositeSpectralTraceClassTransportLevel = machineChecked

normalOperatorFunctionalTransportLevel : ProofLevel
normalOperatorFunctionalTransportLevel = conditional
