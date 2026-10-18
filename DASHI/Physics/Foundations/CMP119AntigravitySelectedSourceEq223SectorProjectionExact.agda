{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedSourceEq223SectorProjectionExact where

------------------------------------------------------------------------
-- SOURCE-FIRST projector: the CMP119 Sect.2 native state is the authority.
-- Do not reconstruct its action from the desired beta answer.
--
-- Bałaban CMP119 (1988), Sect.2 Eq.(2.23), Eqs.(2.25)-(2.42):
-- Wilson coefficient, E/R/B/vacuum terms of ONE selected complete density.
-- A single algebra interpretation of its Eq.(2.23) assembly into T4's
-- LocalizedAction is the remaining action-side representation obligation.
--
-- With the actual source action held fixed, the non-Wilson projection and
-- its four-sector drift are deductions rather than postulated equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.Foundations.CMP119AntigravityRawActionIncrementResidualExact as CanonicalSourceEdge
import DASHI.Physics.Foundations.CMP119AntigravityCMP109WilsonDifferenceOrientationExact as Orientation
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

module _
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  record SelectedEq223RationalActionInterpretation : Set where
    field
      -- This is an algebra homomorphism law for the ALREADY SELECTED action
      -- assembly, not an arbitrary equality between unrelated actions.
      sourceAssemblyPreservesLocalizedAction :
        ∀ coefficient wilson regular r b vacuum →
        CMP119.assemble (CMP119.actionAlgebra source)
          coefficient wilson regular r b vacuum
        ≡ Canonical.canonicalAssemble
          coefficient wilson regular r b vacuum

      -- The published source Wilson term has the unit relevant coefficient.
      -- Its physical normalization is a separate same-source statement.
      sourceWilsonBasisUnit : ∀ k →
        T4.plaquetteCoefficientProjector
          (CMP119.wilsonActionTerm source k) ≡ 1ℚ

  open SelectedEq223RationalActionInterpretation public

  projectedNode : Nat → ℚ
  projectedNode k =
    T4.plaquetteCoefficientProjector (CMP119.effectiveAction source k)

  nonWilsonNode : Nat → ℚ
  nonWilsonNode k = projectedNode k - CMP119.wilsonCoefficient source k

  sectorProjection : Nat → ℚ
  sectorProjection k =
    T4.plaquetteCoefficientProjector (CMP119.regularSmallFieldTerm source k)
    + (T4.plaquetteCoefficientProjector (CMP119.rOperationTerm source k)
    + (T4.plaquetteCoefficientProjector (CMP119.boundaryTerm source k)
    + T4.plaquetteCoefficientProjector (CMP119.vacuumEnergy source k)))

  projectedEq223SourceAction :
    (meaning : SelectedEq223RationalActionInterpretation) →
    ∀ k →
    projectedNode k ≡
      T4.plaquetteCoefficientProjector
        (Canonical.canonicalAssemble
          (CMP119.wilsonCoefficient source k)
          (CMP119.wilsonActionTerm source k)
          (CMP119.regularSmallFieldTerm source k)
          (CMP119.rOperationTerm source k)
          (CMP119.boundaryTerm source k)
          (CMP119.vacuumEnergy source k))
  projectedEq223SourceAction meaning k =
    trans
      (cong T4.plaquetteCoefficientProjector
        (CMP119.equation223 source k))
      (cong T4.plaquetteCoefficientProjector
        (sourceAssemblyPreservesLocalizedAction meaning
          (CMP119.wilsonCoefficient source k)
          (CMP119.wilsonActionTerm source k)
          (CMP119.regularSmallFieldTerm source k)
          (CMP119.rOperationTerm source k)
          (CMP119.boundaryTerm source k)
          (CMP119.vacuumEnergy source k)))

  nonWilsonNodeIsActualFourSectors :
    (meaning : SelectedEq223RationalActionInterpretation) →
    ∀ k →
    nonWilsonNode k ≡ sectorProjection k
  nonWilsonNodeIsActualFourSectors meaning k
    rewrite projectedEq223SourceAction meaning k
          | sourceWilsonBasisUnit meaning k =
    ℚRing.solve-∀
      (CMP119.wilsonCoefficient source k)
      (T4.plaquetteCoefficientProjector
        (CMP119.regularSmallFieldTerm source k))
      (T4.plaquetteCoefficientProjector
        (CMP119.rOperationTerm source k))
      (T4.plaquetteCoefficientProjector
        (CMP119.boundaryTerm source k))
      (T4.plaquetteCoefficientProjector
        (CMP119.vacuumEnergy source k))

  nonWilsonSourceDriftIsActualSectorDrift :
    (meaning : SelectedEq223RationalActionInterpretation) →
    ∀ k →
    nonWilsonNode k - nonWilsonNode (suc k)
    ≡ sectorProjection k - sectorProjection (suc k)
  nonWilsonSourceDriftIsActualSectorDrift meaning k
    rewrite nonWilsonNodeIsActualFourSectors meaning k
          | nonWilsonNodeIsActualFourSectors meaning (suc k) =
    Agda.Builtin.Equality.refl

  -- This projects the genuine source-native pair of consecutive actions.
  -- There is deliberately no action equality with an independently chosen
  -- T4 one-step action and no assumption that the E/R/B/V drift cancels.
  selectedProjectedEdge : Nat → ℚ
  selectedProjectedEdge k =
    T4.plaquetteCoefficientProjector
      (CanonicalSourceEdge.actionDifference
        (CMP119.effectiveAction source k)
        (CMP119.effectiveAction source (suc k)))

  selectedProjectedEdgeIsNodeDifference :
    ∀ k →
    selectedProjectedEdge k
      ≡ projectedNode k - projectedNode (suc k)
  selectedProjectedEdgeIsNodeDifference k =
    CanonicalSourceEdge.projectorDifference
      (CMP119.effectiveAction source k)
      (CMP119.effectiveAction source (suc k))

  projectedEdgeIsWilsonPlusFourSectorDrift :
    (meaning : SelectedEq223RationalActionInterpretation) →
    ∀ k →
    selectedProjectedEdge k
    ≡ (CMP119.wilsonCoefficient source k
       - CMP119.wilsonCoefficient source (suc k))
      + (sectorProjection k - sectorProjection (suc k))
  projectedEdgeIsWilsonPlusFourSectorDrift meaning k =
    trans
      (selectedProjectedEdgeIsNodeDifference k)
      (trans
        (ℚRing.solve-∀
          (projectedNode k) (projectedNode (suc k))
          (CMP119.wilsonCoefficient source k)
          (CMP119.wilsonCoefficient source (suc k)))
        (cong
          (λ drift →
            (CMP119.wilsonCoefficient source k
              - CMP119.wilsonCoefficient source (suc k))
              + drift)
          (nonWilsonSourceDriftIsActualSectorDrift meaning k)))

  -- The CMP119 Sect.2 comment identifies the published action convention
  -- with the negative inverse-square coefficient, but a concrete selected
  -- normalization witness is STILL required for an instantiated theorem.
  -- This is the one source-facing sign/normalization leaf, not an assumed
  -- identity between a projected action and an RG beta.
  selectedSourceNegativeWilsonBeta :
    (meaning : SelectedEq223RationalActionInterpretation)
    (trajectory : Flow.SourceNormalizedCouplingTrajectory)
    (wilsonIsNegativeInverse : ∀ k →
      CMP119.wilsonCoefficient source k
      ≡ - Flow.inverseCoupling trajectory k) →
    ∀ k →
    Flow.beta trajectory (suc k)
    ≡ - selectedProjectedEdge k
      + (sectorProjection k - sectorProjection (suc k))
  selectedSourceNegativeWilsonBeta meaning trajectory nodeMeaning k =
    trans
      (Orientation.sourceBetaIsNegativeWilsonCoefficientDifference
        trajectory (CMP119.wilsonCoefficient source)
        nodeMeaning k)
      (trans
        (ℚRing.solve-∀
          (CMP119.wilsonCoefficient source k)
          (CMP119.wilsonCoefficient source (suc k))
          (sectorProjection k)
          (sectorProjection (suc k)))
        (cong
          (λ x → - x +
            (sectorProjection k - sectorProjection (suc k)))
          (sym (projectedEdgeIsWilsonPlusFourSectorDrift meaning k))))
