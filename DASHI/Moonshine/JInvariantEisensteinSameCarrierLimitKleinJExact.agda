module DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitKleinJExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Product using (proj₁; proj₂)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConstructiveSeries as Series
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConcreteComplexSequenceConvergenceExact as ComplexConvergence
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Q
import DASHI.Moonshine.JInvariantConstructedComplexKleinJBackendExact as CKlein
import DASHI.Moonshine.JInvariantEisensteinConstructedKleinJExact as FiniteKlein
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as Klein
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact as Limit

------------------------------------------------------------------------
-- SAME-CARRIER EISENSTEIN LIMITS -> EXISTING PROOF-RELEVANT KLEIN-j
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- `JInvariantEisensteinSameCarrierLimitCompilerExact` turns explicit Cauchy
-- evidence for the literal finite E4/E6 truncation sequences into limits on
-- exactly the same `ConcreteComplex.ComplexPair` carrier.  This owner now feeds
-- those limits through the already-existing constructed-complex Klein-j
-- backend.  No second complex carrier and no second quotient implementation are
-- introduced.
--
-- IMPORTANT AUTHORITY BOUNDARY
--
-- This is a conditional limit-level algebraic compiler only.  It does NOT:
-- * prove the E4/E6 Cauchy estimates;
-- * identify these limits with the analytic lattice-sum Eisenstein functions;
-- * derive modular transformation laws from finite prefixes;
-- * prove discriminant nonvanishing on the upper half-plane.
--
-- Serre/Miyake attribution and OEIS finite-prefix parity remain owned by the
-- existing source-atlas lane.  Nothing in this composition upgrades OEIS or
-- Python observations into analytic or proof authority.
------------------------------------------------------------------------

private
  ComplexCarrier :
    (C : Complex.ConstructedComplexPackage) -> Set
  ComplexCarrier C =
    Complex.ComplexPair (Real.real (Complex.realPackage C))

------------------------------------------------------------------------
-- Canonical same-carrier limits selected by the constructed-real completeness
-- compiler.
------------------------------------------------------------------------

e4Limit :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : ComplexCarrier C) ->
  ComplexConvergence.ComplexIsCauchy
    (Limit.e4TruncationSequence C S kernel tau) ->
  ComplexCarrier C
e4Limit C S kernel tau cauchy =
  proj₁ (Limit.e4TruncationLimit C S kernel tau cauchy)

e4LimitConvergence :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : ComplexCarrier C) ->
  (cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e4TruncationSequence C S kernel tau)) ->
  ComplexConvergence.ComplexConvergesTo
    (Limit.e4TruncationSequence C S kernel tau)
    (e4Limit C S kernel tau cauchy)
e4LimitConvergence C S kernel tau cauchy =
  proj₂ (Limit.e4TruncationLimit C S kernel tau cauchy)

e6Limit :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : ComplexCarrier C) ->
  ComplexConvergence.ComplexIsCauchy
    (Limit.e6TruncationSequence C S kernel tau) ->
  ComplexCarrier C
e6Limit C S kernel tau cauchy =
  proj₁ (Limit.e6TruncationLimit C S kernel tau cauchy)

e6LimitConvergence :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : ComplexCarrier C) ->
  (cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e6TruncationSequence C S kernel tau)) ->
  ComplexConvergence.ComplexConvergesTo
    (Limit.e6TruncationSequence C S kernel tau)
    (e6Limit C S kernel tau cauchy)
e6LimitConvergence C S kernel tau cauchy =
  proj₂ (Limit.e6TruncationLimit C S kernel tau cauchy)

------------------------------------------------------------------------
-- Limit-level discriminant numerator and normalized Delta.
------------------------------------------------------------------------

limitDiscriminantNumerator :
  (C : Complex.ConstructedComplexPackage) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (tau : ComplexCarrier C) ->
  (e4Cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e4TruncationSequence C S kernel tau)) ->
  (e6Cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e6TruncationSequence C S kernel tau)) ->
  ComplexCarrier C
limitDiscriminantNumerator C S kernel tau e4Cauchy e6Cauchy =
  Complex._-C_
    (Q.cubeC (e4Limit C S kernel tau e4Cauchy))
    (Q.squareC (e6Limit C S kernel tau e6Cauchy))

limitNormalizedDelta :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (normalization : FiniteKlein.EisensteinNormalizationData C D F) ->
  (tau : ComplexCarrier C) ->
  (e4Cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e4TruncationSequence C S kernel tau)) ->
  (e6Cauchy : ComplexConvergence.ComplexIsCauchy
    (Limit.e6TruncationSequence C S kernel tau)) ->
  ComplexCarrier C
limitNormalizedDelta C D F S kernel normalization tau e4Cauchy e6Cauchy =
  CKlein.quotientC F
    (limitDiscriminantNumerator C S kernel tau e4Cauchy e6Cauchy)
    (FiniteKlein.scalar1728 C)
    (FiniteKlein.scalar1728Nonzero normalization)

------------------------------------------------------------------------
-- Certified points make every remaining proof-relevant input explicit.
------------------------------------------------------------------------

record CertifiedEisensteinLimitPoint
  (C : Complex.ConstructedComplexPackage)
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C)))
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D)
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C)))
  (kernel : Q.DivisorPowerKernel)
  (normalization : FiniteKlein.EisensteinNormalizationData C D F) : Set where
  constructor certified-eisenstein-limit-point
  field
    tau : ComplexCarrier C

    e4Cauchy :
      ComplexConvergence.ComplexIsCauchy
        (Limit.e4TruncationSequence C S kernel tau)

    e6Cauchy :
      ComplexConvergence.ComplexIsCauchy
        (Limit.e6TruncationSequence C S kernel tau)

    discriminantNumeratorNonzero :
      Polar.NonzeroC F
        (limitDiscriminantNumerator
          C S kernel tau e4Cauchy e6Cauchy)

    normalizedDeltaNonzero :
      Polar.NonzeroC F
        (limitNormalizedDelta
          C D F S kernel normalization tau e4Cauchy e6Cauchy)

open CertifiedEisensteinLimitPoint public

------------------------------------------------------------------------
-- Instantiate the existing proof-relevant Klein backend at the selected
-- same-carrier limits.
------------------------------------------------------------------------

eisensteinLimitKleinData :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (normalization : FiniteKlein.EisensteinNormalizationData C D F) ->
  CKlein.ConstructedComplexKleinData C D F
eisensteinLimitKleinData C D F S kernel normalization =
  record
    { CKlein.Point =
        CertifiedEisensteinLimitPoint C D F S kernel normalization
    ; CKlein.tau = tau
    ; CKlein.g2 =
        λ point ->
          e4Limit C S kernel (tau point) (e4Cauchy point)
    ; CKlein.delta =
        λ point ->
          limitNormalizedDelta
            C D F S kernel normalization
            (tau point) (e4Cauchy point) (e6Cauchy point)
    ; CKlein.deltaNonzero = normalizedDeltaNonzero
    }

eisensteinLimitKlein :
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
eisensteinLimitKlein C D F S kernel normalization =
  CKlein.constructedComplexKleinJ C D F
    (eisensteinLimitKleinData C D F S kernel normalization)

------------------------------------------------------------------------
-- Direct limit-level evaluator, still conditional on the explicit nonzero
-- witness carried by the point.
------------------------------------------------------------------------

directJLimit :
  (C : Complex.ConstructedComplexPackage) ->
  (D : Polar.RealDivisionAndSquareRoot
        (Real.real (Complex.realPackage C))) ->
  (F : Polar.ComplexFieldAuthority
        (Real.real (Complex.realPackage C)) D) ->
  (S : Series.FunctionSequenceRealization
         (Real.real (Complex.realPackage C))) ->
  (kernel : Q.DivisorPowerKernel) ->
  (normalization : FiniteKlein.EisensteinNormalizationData C D F) ->
  CertifiedEisensteinLimitPoint C D F S kernel normalization ->
  ComplexCarrier C
directJLimit C D F S kernel normalization point =
  Q.scaleNatC 1728
    (CKlein.quotientC F
      (Q.cubeC
        (e4Limit C S kernel (tau point) (e4Cauchy point)))
      (limitDiscriminantNumerator
        C S kernel (tau point) (e4Cauchy point) (e6Cauchy point))
      (discriminantNumeratorNonzero point))

------------------------------------------------------------------------
-- Exact frontier after this payment.
------------------------------------------------------------------------

record EisensteinSameCarrierLimitKleinFrontier : Set where
  constructor eisenstein-same-carrier-limit-klein-frontier
  field
    exactFiniteTruncationSequencesConsumed : Bool
    sameConcreteComplexCarrierPreserved : Bool
    cauchyEvidenceRequired : Bool
    cauchyLimitsConstructed : Bool
    proofRelevantKleinBackendReused : Bool
    discriminantNonzeroRequired : Bool
    quantitativeCauchyEstimatePaidHere : Bool
    analyticLatticeSumIdentityPaidHere : Bool
    modularityTransferredToLimitHere : Bool
    analyticKleinJIdentityPaidHere : Bool

canonicalEisensteinSameCarrierLimitKleinFrontier :
  EisensteinSameCarrierLimitKleinFrontier
canonicalEisensteinSameCarrierLimitKleinFrontier =
  eisenstein-same-carrier-limit-klein-frontier
    true true true true true true false false false false
