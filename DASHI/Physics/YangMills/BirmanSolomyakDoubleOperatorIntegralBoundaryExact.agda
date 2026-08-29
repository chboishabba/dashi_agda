module DASHI.Physics.YangMills.BirmanSolomyakDoubleOperatorIntegralBoundaryExact where

------------------------------------------------------------------------
-- ROUND80: DOUBLE OPERATOR INTEGRALS AS A SUPPORTING CALCULUS
--
-- PRIMARY / SURVEY SOURCES
--
-- V. V. Peller,
-- "Multiple Operator Integrals in Perturbation Theory",
-- Bulletin of Mathematical Sciences 6 (2016), 15--88.
-- DOI: 10.1007/s13373-015-0073-y.
--
-- A. B. Aleksandrov and V. V. Peller,
-- "Functions of Self-Adjoint Operators under Relatively Bounded and Relatively
-- Trace Class Perturbations", Mathematische Nachrichten 298(9) (2025),
-- 3027--3048. DOI: 10.1002/mana.70000.
--
-- A. B. Aleksandrov and V. V. Peller,
-- "Relatively Bounded and Relatively Trace Class Perturbations",
-- Comptes Rendus. Mathematique 363 (2025), 377--382.
-- DOI: 10.5802/crmath.722.
--
-- Birman--Solomyak double operator integrals are the underlying perturbative
-- functional calculus reviewed by Peller.  For self-adjoint A,B and a divided
-- difference Df that acts as an appropriate Schur multiplier, the bounded
-- difference regime has the schematic identity
--
--   f(A)-f(B)
--     = integral integral Df(s,t) dE_A(s) (A-B) dE_B(t).
--
-- This is a SUPPORTING operator-theoretic tool.  It is not a nonperturbative
-- Yang--Mills OPE theorem and does not manufacture composite local fields.
--
-- CRITICAL REGIME BOUNDARY
--
-- The classical bounded-difference DOI identity must not be silently applied
-- to an unbounded continuum Hamiltonian difference.  The three regimes below
-- are kept distinct:
--
--   1. bounded self-adjoint difference;
--   2. trace-class self-adjoint difference;
--   3. relatively trace-class self-adjoint perturbation, expressed through a
--      resolvent-weighted trace-class condition.
--
-- The existing `SchattenTraceClassCompositePerturbationExact` module owns the
-- trace-ideal / relative-trace-class transport and Lifshits--Krein boundaries.
-- This module adds the DOI factorization vocabulary and makes the no-promotion
-- rule executable at the theorem-interface level.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.SchattenTraceClassCompositePerturbationExact as Schatten

record BoundedSelfAdjointDOIAuthority : Set₁ where
  field
    Operator Function SpectralMeasure Kernel : Set
    SelfAdjoint : Operator → Set
    BoundedDifference : Operator → Operator → Set
    DividedDifferenceSchurMultiplier : Function → Set

    spectralMeasure : Operator → SpectralMeasure
    dividedDifference : Function → Kernel
    apply : Function → Operator → Operator

    DoubleOperatorIntegral :
      Kernel → SpectralMeasure → Operator → SpectralMeasure → Operator

    differenceOperator : Operator → Operator → Operator

    birmanSolomyakIdentity : ∀ f A B →
      SelfAdjoint A →
      SelfAdjoint B →
      BoundedDifference A B →
      DividedDifferenceSchurMultiplier f →
      Set

open BoundedSelfAdjointDOIAuthority public

record TraceClassDOIAuthority : Set₁ where
  field
    Operator Function : Set
    SelfAdjoint : Operator → Set
    TraceClassDifference : Operator → Operator → Set
    OperatorLipschitz : Function → Set
    FunctionalDifferenceTraceClass : Function → Operator → Operator → Set

    traceClassTransport : ∀ f A B →
      SelfAdjoint A →
      SelfAdjoint B →
      TraceClassDifference A B →
      OperatorLipschitz f →
      FunctionalDifferenceTraceClass f A B

open TraceClassDOIAuthority public

record RelativeDOIRegime
    (T : Schatten.RelativeTraceClassFunctionalTransport) : Set₁ where
  field
    reference perturbed : Schatten.Operator T
    referenceSelfAdjoint : Schatten.SelfAdjoint T reference
    perturbedSelfAdjoint : Schatten.SelfAdjoint T perturbed
    relativeTraceClass :
      Schatten.RelativeTraceClassDifference T reference perturbed
    resolventWeightedCondition :
      Schatten.resolventWeightedMeaning T
        reference perturbed relativeTraceClass

open RelativeDOIRegime public

record SpectralFunctionalCoordinateBoundary : Set₁ where
  field
    PhysicalCoordinate : Set
    SpectralOperatorCoordinate : PhysicalCoordinate → Set
    LocalCompositeFieldCoordinate : PhysicalCoordinate → Set

    -- A coordinate may genuinely be spectral without thereby being a local
    -- composite field.  This distinction blocks DOI machinery from being used
    -- as an automatic OPE/locality promotion.
    spectralDoesNotPromoteToLocalComposite : ∀ coordinate →
      SpectralOperatorCoordinate coordinate →
      Set

open SpectralFunctionalCoordinateBoundary public

record FiniteGhostVsContinuumGeneratorBoundary : Set where
  field
    finiteReducedFaddeevPopovUsesFiniteTraceLog : Set
    continuumGeneratorRequiresDeclaredPerturbationRegime : Set
    finiteTraceLogDoesNotRequireDOI : Set

open FiniteGhostVsContinuumGeneratorBoundary public

boundedSelfAdjointDOISourceLevel : ProofLevel
boundedSelfAdjointDOISourceLevel = standardImported

traceClassDOISourceLevel : ProofLevel
traceClassDOISourceLevel = standardImported

relativeTraceClassDOISourceLevel : ProofLevel
relativeTraceClassDOISourceLevel = standardImported

-- The DOI calculus can support L6/L7 only after the relevant Yang--Mills
-- coordinate has actually been identified as a self-adjoint spectral
-- functional with the declared perturbation regime.  It does not reduce the
-- seven-leaf analytic frontier by itself.
doiToPhysicalCompositeOperatorLevel : ProofLevel
doiToPhysicalCompositeOperatorLevel = conditional
