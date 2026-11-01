{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralFiniteOSSourceTheoremExact where

------------------------------------------------------------------------
-- T1 theorem-bearing constructor.
--
-- The supplied T1 bundle already owns the published finite Wilson RP,
-- whole-lattice Euclidean covariance, literal RG trajectory/beta enclosure,
-- complete CMP119 density, and Section-2 inductive bounds on one finite family.
-- This module adds only the remaining SAME-family bosonic witness and terminates
-- directly in R545.ConcreteT1FiniteOSSource.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as T1
import DASHI.Physics.YangMills.YangMillsConcreteT1FiniteOSSourceRound545Exact as R545
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as Endpoint
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

literalConcreteT1FiniteOSSource :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection EuclideanAction Permutation
      Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay
      sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {endpoint :
      Endpoint.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division}
    (t1 :
      T1.ConcreteT1SourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection EuclideanAction
        Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division endpoint)
    (bosonic :
      ∀ group →
      Bosonic.LiteralCMP119BosonicPermutationSymmetry
        Configuration Permutation
        (Endpoint.family endpoint group)) →
  R545.ConcreteT1FiniteOSSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection EuclideanAction Permutation
    Density Operation Action Field RegularTerm RTerm BoundaryTerm VacuumTerm
    SmallFieldScale BlockRadius AnalyticRadius Decay
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division endpoint
literalConcreteT1FiniteOSSource t1 bosonic = record
  { R545.ConcreteT1FiniteOSSource.t1 = t1
  ; R545.ConcreteT1FiniteOSSource.bosonic = bosonic
  }
