module DASHI.Moonshine.Y443DGLUniquenessSelectedFLMExact where

------------------------------------------------------------------------
-- ACTUAL DONG--GRIESS--LAM UNIQUENESS, REDUCING THE FLM VOa ISO GATE
--
-- Dong, Griess and Lam, Amer. J. Math. 129 (2007), 583-609,
-- arXiv:math/0506321, DOI: 10.1353/ajm.2007.0009.
--
-- Two *published* uniqueness routes:
--   (a) the only irreducible V-module is V, and V is C2-cofinite;
--   (a') V is simple, with dim V_n <= dim (Vnatural)_n for n>=3.
-- Both routes require c=24, V_1=0 and the EXACT V_2 first-product
-- algebra isomorphic to the Griess algebra (not merely same dimension).
--
-- This theorem interface yields the already implemented FULL MODE
-- isomorphism directly. It is a legitimate substitute for explicitly
-- constructing an FLM state map on every infinite-dimensional grade,
-- only once the actual selected hypotheses and published theorem are
-- themselves inhabited. A source citation is not an Agda proof.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.Y443FLMConcreteVOAGroupTransportExact as Transport
import DASHI.Moonshine.Y443FLMGriessFullAutSelectedVOAExact as Griess

data LessOrEqual : Nat → Nat → Set where
  zeroLe : ∀ {n} → LessOrEqual zero n
  sucLe : ∀ {m n} → LessOrEqual m n → LessOrEqual (suc m) (suc n)

module Selected (V canonicalFLM : VOA.VertexOperatorAlgebra) where
  module T = Transport.Transport V canonicalFLM
  module S = Griess.Selected V
  module P = Griess.Selected canonicalFLM

  record ActualCommonHypotheses : Setω where
    field
      sourceProduct : S.ConcreteGriessProduct
      canonicalProduct : P.ConcreteGriessProduct
      -- Actual mode-one product-preserving Griess algebra equivalence.
      toGriess : S.WeightTwo → P.WeightTwo
      fromGriess : P.WeightTwo → S.WeightTwo
      leftInverse : (x : S.WeightTwo) →
        fromGriess (toGriess x) ≡ x
      rightInverse : (y : P.WeightTwo) →
        toGriess (fromGriess y) ≡ y
      preservesFirstProduct : (x y : S.WeightTwo) →
        toGriess (S.firstProduct sourceProduct x y)
        ≡ P.firstProduct canonicalProduct (toGriess x) (toGriess y)
      preservesConformal :
        toGriess (S.conformalWeightTwo sourceProduct)
        ≡ P.conformalWeightTwo canonicalProduct
      preservesAddition : (x y : S.WeightTwo) →
        toGriess (S.weightTwoAdd sourceProduct x y)
        ≡ P.weightTwoAdd canonicalProduct (toGriess x) (toGriess y)
      toScalar : S.Scalar → P.Scalar
      preservesScale : (k : S.Scalar) (x : S.WeightTwo) →
        toGriess (S.weightTwoScale sourceProduct k x)
        ≡ P.weightTwoScale canonicalProduct (toScalar k) (toGriess x)

      -- Correct c=24 on THIS selected VOA conformal structure.
      sourceNatScalar : Nat → S.Scalar
      centralCharge24 :
        VOA.ConformalAxioms.centralCharge
          (VOA.VertexOperatorAlgebra.conformalAxioms V)
        ≡ sourceNatScalar 24

      -- The actual vector space V_1 consists only of its zero vector.
      gradeOneZero : VOA.GradedModule.gradePiece S.GM 1
      allGradeOneZero : (x : VOA.GradedModule.gradePiece S.GM 1) →
        x ≡ gradeOneZero
  open ActualCommonHypotheses public

  -- External theorem's C2-/module theory must be tied to THIS VOA.
  -- These are actual proposition implementations supplied by the
  -- canonical module-theoretic source, not arbitrary Set-valued labels.
  record HolomorphicC2Certificate : Setω where
    field
      IrreducibleModuleOfSelected : Set
      selectedVacuumModule : IrreducibleModuleOfSelected
      allIrreduciblesAreVacuum :
        (W : IrreducibleModuleOfSelected) → W ≡ selectedVacuumModule

      C2QuotientOfSelected : Set
      c2FiniteDimension : Nat
      c2Basis : Fin c2FiniteDimension → C2QuotientOfSelected
      -- The actual quotient linear operations and spanning certificate
      -- must come from a separate honest source. Merely displaying
      -- c2FiniteDimension is never sufficient.
      c2SpanningCertificate : Set
      c2SpanningIsProved : c2SpanningCertificate

  record HigherGradeBoundCertificate : Setω where
    field
      selectedDimension canonicalDimension : Nat → Nat
      -- Original grading owners must connect these counts with
      -- the selected and canonical gradePiece carriers.
      gradeDimensionIdentification : Set
      gradeDimensionIdentificationProved : gradeDimensionIdentification
      selectedSimpleVOA : Set
      selectedSimpleVOAProved : selectedSimpleVOA
      eachGradeBoundFromThree : (k : Nat) →
        LessOrEqual (selectedDimension (3 + k))
                    (canonicalDimension (3 + k))

  -- These functions denote the *published theorem specialized to the
  -- exact underlying objects*, not a new theorem assumed about every
  -- abstract VOA or every numerical 196884 chart.
  record DongGriessLamTheoremAuthority : Setω where
    field
      uniquenessFromC2 :
        ActualCommonHypotheses →
        HolomorphicC2Certificate →
        T.ExactFLMVOAIsomorphism
      uniquenessFromDimensionBound :
        ActualCommonHypotheses →
        HigherGradeBoundCertificate →
        T.ExactFLMVOAIsomorphism
  open DongGriessLamTheoremAuthority public

  completeFLMIsoFromC2 :
    (authority : DongGriessLamTheoremAuthority)
    (common : ActualCommonHypotheses)
    (certificate : HolomorphicC2Certificate) →
    T.ExactFLMVOAIsomorphism
  completeFLMIsoFromC2 authority common certificate =
    uniquenessFromC2 authority common certificate

  completeFLMIsoFromDimensions :
    (authority : DongGriessLamTheoremAuthority)
    (common : ActualCommonHypotheses)
    (certificate : HigherGradeBoundCertificate) →
    T.ExactFLMVOAIsomorphism
  completeFLMIsoFromDimensions authority common certificate =
    uniquenessFromDimensionBound authority common certificate
