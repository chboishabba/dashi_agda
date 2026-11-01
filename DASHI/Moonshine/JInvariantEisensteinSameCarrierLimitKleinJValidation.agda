module DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitKleinJValidation where

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConcreteComplexSequenceConvergenceExact as ComplexConvergence
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as FiniteKlein
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as Klein
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact as Limit
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitKleinJExact as P

------------------------------------------------------------------------
-- RED owner: once literal E4/E6 truncation sequences are supplied with
-- componentwise Cauchy evidence, their same-carrier limits must feed the
-- existing proof-relevant Klein-j backend.  This validation intentionally says
-- nothing about analytic lattice-sum identity or modularity.
------------------------------------------------------------------------

e4LimitUsesConcreteCarrier :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (Limit.e4TruncationSequence C S kernel tau) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e4LimitUsesConcreteCarrier = P.e4Limit

e6LimitUsesConcreteCarrier :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  ComplexConvergence.ComplexIsCauchy
    (Limit.e6TruncationSequence C S kernel tau) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
e6LimitUsesConcreteCarrier = P.e6Limit

limitKleinUsesExistingBackend :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  FiniteKlein.EisensteinNormalizationData C D F ->
  Klein.ProofRelevantKleinJAlgebra
limitKleinUsesExistingBackend = P.eisensteinLimitKlein
