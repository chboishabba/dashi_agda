module DASHI.Moonshine.JInvariantLiteralQBishopRadiusSameObjectReductionExact where

------------------------------------------------------------------------
-- LITERAL LEGACY |q(tau)| -> BISHOP q-RADIUS SAME-OBJECT REDUCTION
--
-- DASHI CONTRIBUTION
--
-- The complex-analytic side is already owned on the legacy ConcreteComplex
-- carrier:
--
--   |q(tau)| = exp(Re((2*pi*i)tau))
--
-- on the admitted principal strip.
--
-- The Bishop side is also already owned:
--
--   r_B = exp_B(-(2*pi_B*Im_B tau_B))
--   0 < r_B < 1
--
-- for positive pi_B and positive imaginary coordinate.
--
-- Therefore the remaining same-object theorem does not need to compare two
-- complex exponentials.  It is enough to transport only:
--
--   (1) the single real exponent object;
--   (2) the real exponential at that object.
--
-- This owner makes that reduction proof-relevant.  It does not manufacture
-- either transport witness, identify Bishop Machin pi with legacy pi, or
-- identify the two imaginary coordinates.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; trans)

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as BishopExp
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as FiniteQ
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as QModulus
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as BishopRadius
import DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact as Exponent
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantEisensteinBishopRadiusWeldExact as RadiusWeld

qExponent :
  (C : Complex.ConstructedComplexPackage) →
  Complex.ComplexPair (Real.real (Complex.realPackage C)) →
  Complex.ComplexPair (Real.real (Complex.realPackage C))
qExponent = QModulus.qExponent

record LiteralQBishopRadiusTransport
    (C : Complex.ConstructedComplexPackage)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    (piB imagB : BishopReal.ℝ) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
    E = Real.exponential (Complex.realPackage C)

  field
    toLegacy : BishopReal.ℝ → Real.Real R

    exponentAgreement :
      toLegacy
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB))
      ≡
      Complex.re (qExponent C tau)

    exponentialAgreement :
      toLegacy
        (BishopExp.bishopExp
          (BishopReal.-_
            (BishopRadius.qExponentMagnitude piB imagB)))
      ≡
      Real.exp E
        (toLegacy
          (BishopReal.-_
            (BishopRadius.qExponentMagnitude piB imagB)))

open LiteralQBishopRadiusTransport public


transportFromMagnitudeAndExponential :
  ∀ {C : Complex.ConstructedComplexPackage}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (magnitude :
      Exponent.QBishopExponentMagnitudeTransport C tau piB imagB) →
  (Exponent.toLegacy magnitude
      (BishopExp.bishopExp
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB)))
    ≡
    Real.exp
      (Real.exponential (Complex.realPackage C))
      (Exponent.toLegacy magnitude
        (BishopReal.-_
          (BishopRadius.qExponentMagnitude piB imagB)))) →
  LiteralQBishopRadiusTransport C tau piB imagB
transportFromMagnitudeAndExponential N tau magnitude expAgreement = record
  { toLegacy = Exponent.toLegacy magnitude
  ; exponentAgreement =
      Exponent.compileExponentAgreement N tau magnitude
  ; exponentialAgreement = expAgreement
  }

LegacyRadiusRelation :
  ∀ {C tau piB imagB} →
  LiteralQBishopRadiusTransport C tau piB imagB →
  Real.Real (Real.real (Complex.realPackage C)) →
  BishopReal.ℝ →
  Set
LegacyRadiusRelation transport legacyRadius bishopRadius =
  legacyRadius ≡ toLegacy transport bishopRadius

bishopRadiusMapsToLegacyRealExponential :
  ∀ {C tau piB imagB}
    (transport : LiteralQBishopRadiusTransport C tau piB imagB) →
  toLegacy transport (BishopRadius.qRadius piB imagB)
  ≡
  Real.exp
    (Real.exponential (Complex.realPackage C))
    (Complex.re (qExponent C tau))
bishopRadiusMapsToLegacyRealExponential
  {C} {tau} {piB} {imagB} transport =
  trans
    (exponentialAgreement transport)
    (cong
      (Real.exp (Real.exponential (Complex.realPackage C)))
      (exponentAgreement transport))

literalQModulusMatchesBishopRadius :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (polar : Polar.OrdinaryPolarData C D F)
    (branch : Polar.OrdinaryPrincipalBranchLaws C D F polar)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : LiteralQBishopRadiusTransport C tau piB imagB)
    (strip : Polar.PrincipalStrip polar (qExponent C tau)) →
  Polar.modulus F (FiniteQ.qOf C tau)
  ≡
  toLegacy transport (BishopRadius.qRadius piB imagB)
literalQModulusMatchesBishopRadius
  {C} polar branch tau {piB} {imagB} transport strip =
  trans
    (QModulus.qModulusOnPrincipalStrip polar branch tau strip)
    (sym (bishopRadiusMapsToLegacyRealExponential transport))

compileLiteralQRadiusWeld :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D}
    (polar : Polar.OrdinaryPolarData C D F)
    (branch : Polar.OrdinaryPrincipalBranchLaws C D F polar)
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : LiteralQBishopRadiusTransport C tau piB imagB)
    (strip : Polar.PrincipalStrip polar (qExponent C tau))
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB) →
  RadiusWeld.LiteralRadiusBishopWeld
    (LegacyRadiusRelation transport)
    (Polar.modulus F (FiniteQ.qOf C tau))
compileLiteralQRadiusWeld
  polar branch tau {piB} {imagB} transport strip piPositive imagPositive = record
  { RadiusWeld.bishopRadius = BishopRadius.qRadius piB imagB
  ; RadiusWeld.sameRadius =
      literalQModulusMatchesBishopRadius
        polar branch tau transport strip
  ; RadiusWeld.unitInterval =
      BishopRadius.qRadiusUnitInterval piPositive imagPositive
  }
