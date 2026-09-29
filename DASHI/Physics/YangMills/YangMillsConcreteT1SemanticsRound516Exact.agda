{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact where

------------------------------------------------------------------------
-- GOAL-1 T1 / ROUND516: SOURCE-BACKED FINITE/RG ENDPOINT SEMANTICS
--
-- The old T1 Clay predicates were opaque.  This module gives them concrete
-- meanings on the SAME finite CMP119 family already used by R499/R511:
--
--   finite cutoff measure       = exact selected finite family;
--   RP regularization           = published Wilson finite RP on that family;
--   UV normalization            = E_n(1)=1 + source-normalized recurrence;
--   AF trajectory               = the proved two-sided UV tube;
--   gauge/locality preservation = CMP119 Section-2 inductive bounds;
--   Euclidean covariance        = published whole-lattice covariance;
--   RP preservation             = finite RP at every cutoff;
--   positivity normalization    = E_n(1)=1 and positivity;
--   cutoff compatibility        = R499's SAME projective event consistency.
--
-- The rich source records remain constructor inputs.  The Set-valued Clay
-- predicates do not pretend to contain Set1 theorem packages.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_; _≤_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; 1ℝ; _≤ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as R511
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.YangMillsPositiveProjectiveCylinderProbabilityRound538Exact as R538
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsClayPublishedWilsonRPRound461Exact as R461
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteT1SourceBundle
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Algebra Event Projection EuclideanAction
     Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
     SmallFieldScale BlockRadius AnalyticRadius Decay : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (endpoint :
      R511.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    : Set₂ where
  field
    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    publishedWilsonRP :
      ∀ group →
      R461.PublishedWilsonRPApplication
        Configuration
        (R511.family endpoint group)
        observableAlgebra

    euclidean :
      ∀ group →
      Euclidean.CMP119WholeLatticeEuclideanCovariance
        Configuration EuclideanAction
        (R511.family endpoint group)

    trajectory :
      G → Flow.SourceNormalizedCouplingTrajectory

    betaEnclosure :
      ∀ group →
      Flow.UniformBetaEnclosure (trajectory group)

    completeDensityAt :
      G → Nat →
      CMP119.CMP119Section2CompleteDensity
        ℚ Density Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay

    inductiveBounds :
      ∀ group cutoff →
      CMP119.CMP119Section2InductiveBounds
        (completeDensityAt group cutoff)

open ConcreteT1SourceBundle public

------------------------------------------------------------------------
-- Concrete finite/RG meanings.
------------------------------------------------------------------------

ConcreteFiniteVolumeCutoffMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ → Set
ConcreteFiniteVolumeCutoffMeasure {endpoint = endpoint} source group cutoff measure =
  measure ≡ Limit.finiteMeasure (R511.family endpoint group) cutoff

ConcreteFiniteReflectionPositive :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Nat → Set
ConcreteFiniteReflectionPositive {endpoint = endpoint} source group cutoff =
  ∀ testFamily →
  0ℝ ≤ℝ
    Gram.physicalReflectedGramQuadraticForm
      (OS2.operations (observableAlgebra source))
      (λ observable →
        Limit.finiteExpectation
          (R511.family endpoint group)
          cutoff observable)
      testFamily

ConcreteReflectionPositiveRegularization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ → Set
ConcreteReflectionPositiveRegularization source group cutoff measure =
  ConcreteFiniteVolumeCutoffMeasure source group cutoff measure
  × ConcreteFiniteReflectionPositive source group cutoff

ConcreteUVNormalization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → (Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ) → Set
ConcreteUVNormalization {endpoint = endpoint} source group finite =
  (∀ cutoff →
    finite cutoff ≡ Limit.finiteMeasure (R511.family endpoint group) cutoff)
  ×
  (∀ cutoff →
    Limit.finiteExpectation
      (R511.family endpoint group)
      cutoff Finite.oneObservable
    ≡
    1ℝ)
  ×
  (∀ depth →
    Flow.inverseCoupling (trajectory source group) depth
    ≡
    Flow.inverseCoupling (trajectory source group) (suc depth)
      + Flow.beta (trajectory source group) (suc depth))

ConcreteAsymptoticallyFreeTrajectory :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → (Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ) → Set
ConcreteAsymptoticallyFreeTrajectory {endpoint = endpoint} source group finite =
  (∀ cutoff →
    finite cutoff ≡ Limit.finiteMeasure (R511.family endpoint group) cutoff)
  ×
  (∀ depth →
    (Sums.natAsRational depth
      * Flow.betaLower (betaEnclosure source group)
      ≤
      Flow.inverseCoupling (trajectory source group) 0
        -
        Flow.inverseCoupling (trajectory source group) depth)
    ×
    (Flow.inverseCoupling (trajectory source group) 0
        -
        Flow.inverseCoupling (trajectory source group) depth
      ≤
      Sums.natAsRational depth
        * Flow.betaUpper (betaEnclosure source group)))

ConcreteGaugePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcreteGaugePreserved source group =
  ∀ cutoff →
  CMP119.GaugeCovariance (inductiveBounds source group cutoff)

ConcreteLocalityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcreteLocalityPreserved source group =
  ∀ cutoff →
    CMP119.RegularLocalizedAnalyticBound (inductiveBounds source group cutoff)
    ×
    CMP119.ROperationLocalizedDecayBound (inductiveBounds source group cutoff)
    ×
    CMP119.BoundaryLocalizedDecayBound (inductiveBounds source group cutoff)

ConcreteEuclideanCovariancePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcreteEuclideanCovariancePreserved {endpoint = endpoint} source group =
  ∀ cutoff action observable →
  Limit.finiteExpectation (R511.family endpoint group) cutoff
    (Euclidean.actObservable (euclidean source group) action observable)
  ≡
  Limit.finiteExpectation (R511.family endpoint group) cutoff observable

ConcreteReflectionPositivityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcreteReflectionPositivityPreserved source group =
  ∀ cutoff → ConcreteFiniteReflectionPositive source group cutoff

ConcretePositivityNormalizationPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcretePositivityNormalizationPreserved {endpoint = endpoint} source group =
  (∀ cutoff →
    Limit.finiteExpectation (R511.family endpoint group)
      cutoff Finite.oneObservable
    ≡ 1ℝ)
  ×
  (∀ cutoff observable →
    Finite.PointwiseNonnegative observable →
    0ℝ ≤ℝ
      Limit.finiteExpectation (R511.family endpoint group)
        cutoff observable)

ConcreteVolumeCutoffCompatibility :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  G → Set
ConcreteVolumeCutoffCompatibility {endpoint = endpoint} source group =
  let projective =
        R535.projectiveEvents (R511.representationInputs endpoint group)
  in
  ∀ lower upper
    (restriction : R538.Restricts projective lower upper)
    event →
  Limit.finiteExpectation (R511.family endpoint group) lower
    (R498.indicator (R538.events (R538.positiveEvents projective))
      (R538.restrictEvent projective lower upper restriction event))
  ≡
  Limit.finiteExpectation (R511.family endpoint group) upper
    (R498.indicator (R538.events (R538.positiveEvents projective)) event)

------------------------------------------------------------------------
-- Proofs from the source bundle.
------------------------------------------------------------------------

finiteReflectionPositive :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group cutoff →
  ConcreteFiniteReflectionPositive source group cutoff
finiteReflectionPositive source group cutoff =
  R461.finiteReflectionPositiveFromPublishedWilson
    (publishedWilsonRP source group) cutoff

gaugePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteGaugePreserved source group
gaugePreserved source group cutoff =
  CMP119.gaugeCovariance (inductiveBounds source group cutoff)

localityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteLocalityPreserved source group
localityPreserved source group cutoff =
  ( CMP119.regularLocalizedAnalyticBound (inductiveBounds source group cutoff)
  , CMP119.rOperationLocalizedDecayBound (inductiveBounds source group cutoff)
  , CMP119.boundaryLocalizedDecayBound (inductiveBounds source group cutoff)
  )

euclideanCovariancePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteEuclideanCovariancePreserved source group
euclideanCovariancePreserved source group =
  Euclidean.finiteEuclideanInvariant (euclidean source group)

positivityNormalizationPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcretePositivityNormalizationPreserved source group
positivityNormalizationPreserved {endpoint = endpoint} source group =
  ( Limit.finiteExpectationOne (R511.family endpoint group)
  , Limit.finiteExpectationPositive (R511.family endpoint group)
  )

volumeCutoffCompatibility :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteVolumeCutoffCompatibility source group
volumeCutoffCompatibility {endpoint = endpoint} source group =
  R538.projectiveEventExpectationConsistency
    (R535.projectiveEvents (R511.representationInputs endpoint group))

selectedUVNormalization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteUVNormalization source group
    (λ cutoff → Limit.finiteMeasure (R511.family endpoint group) cutoff)
selectedUVNormalization {endpoint = endpoint} source group =
  ( (λ cutoff → refl)
  , ( Limit.finiteExpectationOne (R511.family endpoint group)
    , Flow.sourceRecurrence (trajectory source group)
    )
  )

selectedAsymptoticallyFreeTrajectory :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteAsymptoticallyFreeTrajectory source group
    (λ cutoff → Limit.finiteMeasure (R511.family endpoint group) cutoff)
selectedAsymptoticallyFreeTrajectory source group =
  ( (λ cutoff → refl)
  , Flow.sourceNormalizedTwoSidedUVTube (betaEnclosure source group)
  )

reflectionPositivityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteReflectionPositivityPreserved source group
reflectionPositivityPreserved source group =
  finiteReflectionPositive source group

selectedFiniteVolumeCutoffMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group cutoff →
  ConcreteFiniteVolumeCutoffMeasure source group cutoff
    (Limit.finiteMeasure (R511.family endpoint group) cutoff)
selectedFiniteVolumeCutoffMeasure source group cutoff = refl

selectedReflectionPositiveRegularization :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group cutoff →
  ConcreteReflectionPositiveRegularization source group cutoff
    (Limit.finiteMeasure (R511.family endpoint group) cutoff)
selectedReflectionPositiveRegularization source group cutoff =
  refl , finiteReflectionPositive source group cutoff

selectedGaugePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteGaugePreserved source group
selectedGaugePreserved = gaugePreserved

selectedLocalityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteLocalityPreserved source group
selectedLocalityPreserved = localityPreserved

selectedEuclideanCovariancePreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteEuclideanCovariancePreserved source group
selectedEuclideanCovariancePreserved = euclideanCovariancePreserved

selectedReflectionPositivityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteReflectionPositivityPreserved source group
selectedReflectionPositivityPreserved = reflectionPositivityPreserved

selectedPositivityNormalizationPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcretePositivityNormalizationPreserved source group
selectedPositivityNormalizationPreserved = positivityNormalizationPreserved

selectedVolumeCutoffCompatibility :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division endpoint}
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    group →
  ConcreteVolumeCutoffCompatibility source group
selectedVolumeCutoffCompatibility = volumeCutoffCompatibility

------------------------------------------------------------------------
-- Semantics overlay: non-T1 meanings are inherited from R511.
------------------------------------------------------------------------

concreteT1Semantics :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit limitLaws quotient division}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (endpoint :
      R511.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    (source :
      ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint) →
  Top.LiteralYangMillsSemantics
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vacuum)
concreteT1Semantics base endpoint source =
  let old = R511.concreteEndpointSemantics base endpoint in
  record
  { Top.LiteralYangMillsSemantics.IsCompactSimple =
      Top.IsCompactSimple old
  ; Top.LiteralYangMillsSemantics.IsFourDimensionalEuclidean =
      Top.IsFourDimensionalEuclidean old
  ; Top.LiteralYangMillsSemantics.IsFiniteVolumeCutoffMeasure =
      ConcreteFiniteVolumeCutoffMeasure source
  ; Top.LiteralYangMillsSemantics.IsReflectionPositiveRegularization =
      ConcreteReflectionPositiveRegularization source
  ; Top.LiteralYangMillsSemantics.HasUltravioletYangMillsNormalization =
      ConcreteUVNormalization source
  ; Top.LiteralYangMillsSemantics.HasAsymptoticallyFreeScaleTrajectory =
      ConcreteAsymptoticallyFreeTrajectory source
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantObservable =
      Top.IsGaugeInvariantObservable old
  ; Top.LiteralYangMillsSemantics.IsLocalObservable =
      Top.IsLocalObservable old
  ; Top.LiteralYangMillsSemantics.IsContinuumLimitOf =
      Top.IsContinuumLimitOf old
  ; Top.LiteralYangMillsSemantics.SchwingerBelongsToMeasure =
      Top.SchwingerBelongsToMeasure old
  ; Top.LiteralYangMillsSemantics.IsNontrivialQuantumYangMills =
      Top.IsNontrivialQuantumYangMills old
  ; Top.LiteralYangMillsSemantics.CurvatureOperatorCorrespondence =
      Top.CurvatureOperatorCorrespondence old
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantLocalOperator =
      Top.IsGaugeInvariantLocalOperator old
  ; Top.LiteralYangMillsSemantics.IsLocalOperator =
      Top.IsLocalOperator old
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPECoefficient =
      Top.IsPhysicalOPECoefficient old
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPERemainder =
      Top.IsPhysicalOPERemainder old
  ; Top.LiteralYangMillsSemantics.HasShortDistanceAsymptoticFreedom =
      Top.HasShortDistanceAsymptoticFreedom old
  ; Top.LiteralYangMillsSemantics.HasStressTensorAndOPE =
      Top.HasStressTensorAndOPE old
  ; Top.LiteralYangMillsSemantics.SatisfiesAcceptedWightmanOrOSAxioms =
      Top.SatisfiesAcceptedWightmanOrOSAxioms old
  ; Top.LiteralYangMillsSemantics.IsReconstructedHilbertSpace =
      Top.IsReconstructedHilbertSpace old
  ; Top.LiteralYangMillsSemantics.IsPositiveSelfAdjointHamiltonian =
      Top.IsPositiveSelfAdjointHamiltonian old
  ; Top.LiteralYangMillsSemantics.IsVacuumSectorAndPositiveEnergyComplement =
      Top.IsVacuumSectorAndPositiveEnergyComplement old
  ; Top.LiteralYangMillsSemantics.IsStrictlyPositiveFiniteMassGap =
      Top.IsStrictlyPositiveFiniteMassGap old
  ; Top.LiteralYangMillsSemantics.GaugeSymmetryPreservedAlongConstruction =
      ConcreteGaugePreserved source
  ; Top.LiteralYangMillsSemantics.LocalityPreservedAlongConstruction =
      ConcreteLocalityPreserved source
  ; Top.LiteralYangMillsSemantics.EuclideanCovariancePreservedAlongConstruction =
      ConcreteEuclideanCovariancePreserved source
  ; Top.LiteralYangMillsSemantics.ReflectionPositivityPreservedAlongConstruction =
      ConcreteReflectionPositivityPreserved source
  ; Top.LiteralYangMillsSemantics.PositivityNormalizationPreservedAlongConstruction =
      ConcretePositivityNormalizationPreserved source
  ; Top.LiteralYangMillsSemantics.VolumeCutoffCompatibilityPreserved =
      ConcreteVolumeCutoffCompatibility source
  ; Top.LiteralYangMillsSemantics.PhysicalScaleLowerBoundUniform =
      Top.PhysicalScaleLowerBoundUniform old
  ; Top.LiteralYangMillsSemantics.NoSpectralPollutionBelowGap =
      Top.NoSpectralPollutionBelowGap old
  ; Top.LiteralYangMillsSemantics.NontrivialityPreservedInLimit =
      Top.NontrivialityPreservedInLimit old
  ; Top.LiteralYangMillsSemantics.GapAndClusteringAreDerivedNotAssumed =
      Top.GapAndClusteringAreDerivedNotAssumed old
  ; Top.LiteralYangMillsSemantics.CompactSimpleParameterizationPreserved =
      Top.CompactSimpleParameterizationPreserved old
  }

round516ConcreteT1SemanticsCompilerLevel : ProofLevel
round516ConcreteT1SemanticsCompilerLevel = machineChecked

round516FiniteNormalizationCompilerLevel : ProofLevel
round516FiniteNormalizationCompilerLevel = machineChecked

round516PublishedFiniteRPCompilerLevel : ProofLevel
round516PublishedFiniteRPCompilerLevel = machineChecked

round516ProjectiveCutoffCompatibilityCompilerLevel : ProofLevel
round516ProjectiveCutoffCompatibilityCompilerLevel = machineChecked

-- Source-facing T1 inputs still required to build ConcreteT1SourceBundle:
-- published Wilson-RP application, finite Euclidean application, source
-- beta-enclosure, and the literal CMP119 Section-2 complete-density/bounds
-- family.  Endpoint predicate names no longer constitute separate research
-- leaves once this bundle exists.
literalRound516ConcreteT1SourceBundleLevel : ProofLevel
literalRound516ConcreteT1SourceBundleLevel = conditional
