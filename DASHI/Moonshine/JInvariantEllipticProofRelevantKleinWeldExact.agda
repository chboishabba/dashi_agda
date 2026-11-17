module DASHI.Moonshine.JInvariantEllipticProofRelevantKleinWeldExact where

------------------------------------------------------------------------
-- ORIGINAL PROOF-RELEVANT KLEIN-j: certified points ONLY.
--
-- Avoid the total quotient as the public theorem carrier: each point
-- retains its own proof that the original normalized Delta is safe
-- to divide by. The underlying arithmetic quotient is the SAME
-- existing standard-j algebra. No extra modular function is defined.
--
-- Sources: Serre (1973), Miyake (2006); original DASHI
-- JInvariantProofRelevantKleinJExact / AnalyticNormalizedKleinAdapter.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as E
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as D
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as N
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as Q
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as J
import DASHI.Moonshine.JInvariantProofRelevantKleinJExact as Klein
import DASHI.Moonshine.JInvariantEllipticFixedPointCompilerExact as Fixed
import DASHI.Moonshine.JInvariantEllipticStandardJValuesCompilerExact as Values

record CertifiedKleinPoint
    (M : E.EisensteinAnalyticModel)
    (A : D.DiscriminantAlgebra M)
    (Norm : N.WeightCompatibleNormalization M)
    (Div : Q.QuotientCancellationAlgebra M) : Set where
  constructor certified-klein-point
  field
    tau : E.Parameter M
    deltaSafe :
      Q.DenominatorSafe Div
        (N.normalizedDelta M A Norm tau)

open CertifiedKleinPoint public

originalProofRelevantKlein :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  Klein.ProofRelevantKleinJAlgebra
originalProofRelevantKlein M A Norm Div = record
  { Klein.Point = CertifiedKleinPoint M A Norm Div
  ; Klein.Value = E.Scalar M
  ; Klein.g2 = λ point → D.E4 M (tau point)
  ; Klein.delta = λ point →
      N.normalizedDelta M A Norm (tau point)
  ; Klein.cube = D.cube M
  ; Klein.Nonzero = Q.DenominatorSafe Div
  ; Klein.deltaNonzero = deltaSafe
  ; Klein.quotient = λ numerator denominator witness →
      Q._/ˢ_ Div numerator denominator
  }

proofRelevantJIsOriginalStandardJ :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (point : CertifiedKleinPoint M A Norm Div) →
  Klein.KleinJ (originalProofRelevantKlein M A Norm Div) point
  ≡ J.standardJ M A Norm Div (tau point)
proofRelevantJIsOriginalStandardJ M A Norm Div point = refl

certifiedIPoint :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  Values.EllipticValueFieldEvidence M A Norm Div W →
  CertifiedKleinPoint M A Norm Div
certifiedIPoint M A Norm Div W F =
  certified-klein-point (Fixed.iPoint W) (Values.deltaSafeAtI F)

certifiedOmegaPoint :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  Values.EllipticValueFieldEvidence M A Norm Div W →
  CertifiedKleinPoint M A Norm Div
certifiedOmegaPoint M A Norm Div W F =
  certified-klein-point (Fixed.omegaPoint W) (Values.deltaSafeAtOmega F)

originalProofRelevantJAtIIs1728 :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  (F : Values.EllipticValueFieldEvidence M A Norm Div W) →
  Klein.KleinJ (originalProofRelevantKlein M A Norm Div)
    (certifiedIPoint M A Norm Div W F)
  ≡ Values.scalar1728 F
originalProofRelevantJAtIIs1728 M A Norm Div W F =
  trans
    (proofRelevantJIsOriginalStandardJ M A Norm Div
      (certifiedIPoint M A Norm Div W F))
    (Values.jAtIIs1728 M A Norm Div W F)

originalProofRelevantJAtOmegaIsZero :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  (F : Values.EllipticValueFieldEvidence M A Norm Div W) →
  Klein.KleinJ (originalProofRelevantKlein M A Norm Div)
    (certifiedOmegaPoint M A Norm Div W F)
  ≡ E.zero M
originalProofRelevantJAtOmegaIsZero M A Norm Div W F =
  trans
    (proofRelevantJIsOriginalStandardJ M A Norm Div
      (certifiedOmegaPoint M A Norm Div W F))
    (Values.jAtOmegaIsZero M A Norm Div W F)

------------------------------------------------------------------------
-- No claimed Bishop/Agda kernel acceptance: the W/F witnesses are
-- still the exact concrete analytic wall, and the code is currently
-- source-written pending pinned agda --safe typechecking.
------------------------------------------------------------------------
