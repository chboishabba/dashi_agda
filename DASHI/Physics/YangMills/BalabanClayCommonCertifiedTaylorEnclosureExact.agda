module DASHI.Physics.YangMills.BalabanClayCommonCertifiedTaylorEnclosureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Sergio Blanes, Fernando Casas, José A. Oteo and José Ros,
-- "Magnus and Fer Expansions for Matrix Differential Equations: The
-- Convergence Problem", Journal of Physics A: Mathematical and General 31
-- (1998), 259--268. DOI: 10.1088/0305-4470/31/1/023
--
-- Sergio Blanes and Fernando Casas, "On the Convergence and Optimization of
-- the Baker--Campbell--Hausdorff Formula", Linear Algebra and its Applications
-- 378 (2004), 135--158. DOI: 10.1016/j.laa.2003.09.010
--
-- Sergio Blanes, Fernando Casas, José A. Oteo and José Ros, "The Magnus
-- Expansion and Some of Its Applications", Physics Reports 470 (2009),
-- 151--238. DOI: 10.1016/j.physrep.2008.11.001
--
-- Anirban Dey, Davide Lonigro, Kazuya Yuasa and Daniel Burgarth, "Error Bounds
-- for the Floquet--Magnus Expansion and Their Application to the Semiclassical
-- Quantum Rabi Model", Physical Review A 112 (2025), 053723.
-- DOI: 10.1103/6bgj-s987; arXiv:2504.20533
--
-- Relationship: these papers provide comparison radii and truncation-error
-- architecture.  The SU(2) chart proofs below are intended to use the sharper
-- closed-form quaternion/rotation formulas; generic Magnus/BCH estimates are
-- retained only as sanity checks.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Horner polynomial carrier.  Coefficients are supplied in ascending degree.
------------------------------------------------------------------------

record ScalarSemiring (Scalar : Set) : Set₁ where
  field
    zero one : Scalar
    add multiply : Scalar → Scalar → Scalar

open ScalarSemiring public

polynomialValue :
  ∀ {Scalar} → ScalarSemiring Scalar → List Scalar → Scalar → Scalar
polynomialValue algebra [] point = zero algebra
polynomialValue algebra (coefficient ∷ coefficients) point =
  add algebra coefficient
    (multiply algebra point (polynomialValue algebra coefficients point))

------------------------------------------------------------------------
-- A proof-producing enclosure.  The transcendental function is never replaced
-- by the polynomial definitionally: lower/upper correctness are explicit
-- obligations on the chosen interval.
------------------------------------------------------------------------

record CertifiedTaylorEnclosure (Scalar : Set) : Set₁ where
  field
    algebra : ScalarSemiring Scalar
    function : Scalar → Scalar
    lowerCoefficients upperCoefficients : List Scalar
    intervalLower intervalUpper : Scalar
    InInterval : Scalar → Set
    LessEqual : Scalar → Scalar → Set

    lowerCorrect : ∀ point → InInterval point →
      LessEqual
        (polynomialValue algebra lowerCoefficients point)
        (function point)

    upperCorrect : ∀ point → InInterval point →
      LessEqual
        (function point)
        (polynomialValue algebra upperCoefficients point)

open CertifiedTaylorEnclosure public

lowerPolynomial :
  ∀ {Scalar} → CertifiedTaylorEnclosure Scalar → Scalar → Scalar
lowerPolynomial certificate =
  polynomialValue (algebra certificate) (lowerCoefficients certificate)

upperPolynomial :
  ∀ {Scalar} → CertifiedTaylorEnclosure Scalar → Scalar → Scalar
upperPolynomial certificate =
  polynomialValue (algebra certificate) (upperCoefficients certificate)

------------------------------------------------------------------------
-- Shared sinc/cosine/log infrastructure for T3 chart control and T2 Haar loss.
------------------------------------------------------------------------

record CommonSincIntervalCertificate (Scalar : Set) : Set₁ where
  field
    zero one two radius piLower logTwo : Scalar
    add multiply divide subtract negate sine cosine logarithm :
      Scalar → Scalar → Scalar
    square sinc inverseSinc negativeLogSinc : Scalar → Scalar

    LessEqual StrictLess : Scalar → Scalar → Set
    InRadius : Scalar → Set

    sineEnclosure cosineEnclosure sincEnclosure negativeLogSincEnclosure :
      CertifiedTaylorEnclosure Scalar

    radiusPositive : StrictLess zero radius
    radiusBelowPi : StrictLess radius piLower
    radiusInsideAllEnclosures : InRadius radius

    sincPositiveOnRadius : ∀ point → InRadius point →
      StrictLess zero (sinc point)

    sincLowerBound : ∀ point → InRadius point →
      LessEqual (sincLower point) (sinc point)
    sincLower : Scalar → Scalar

    inverseSincDefinition : ∀ point →
      inverseSinc point ≡ divide one (sinc point)

    inverseSincMonotoneRadiusBound : ∀ point → InRadius point →
      LessEqual (inverseSinc point) (inverseSinc radius)

    negativeLogSincQuadratic : ∀ point → InRadius point →
      LessEqual (negativeLogSinc point)
        (multiply (negativeLogQuadraticConstant point) (square point))
    negativeLogQuadraticConstant : Scalar → Scalar

    -- Generic BCH/Magnus sanity-check radius.  It is not consumed by the SU(2)
    -- quaternion proof, but prevents a generic-series fallback from silently
    -- operating outside its certified domain.
    genericBCHRadiusSafe : LessEqual radius logTwo

open CommonSincIntervalCertificate public

rightJacobianInverseScalarBound :
  ∀ {Scalar} → CommonSincIntervalCertificate Scalar → Scalar
rightJacobianInverseScalarBound certificate = inverseSinc certificate (radius certificate)

haarNegativeLogScalarBound :
  ∀ {Scalar} → CommonSincIntervalCertificate Scalar → Scalar → Scalar
haarNegativeLogScalarBound certificate point =
  multiply certificate
    (negativeLogQuadraticConstant certificate point)
    (square certificate point)

------------------------------------------------------------------------
-- Finite certificate audit data.  A generated interval certificate can record
-- exactly which polynomial, interval and arithmetic backend established it.
------------------------------------------------------------------------

record TaylorCertificateReceipt : Set where
  field
    theoremName sourceReference coefficientEncoding intervalEncoding : Set
    lowerPolynomialChecked upperPolynomialChecked denominatorPositiveChecked : Set

open TaylorCertificateReceipt public

hornerPolynomialReductionLevel : ProofLevel
hornerPolynomialReductionLevel = machineChecked

certifiedEnclosureCompositionLevel : ProofLevel
certifiedEnclosureCompositionLevel = machineChecked

literalTranscendentalCoefficientInputsLevel : ProofLevel
literalTranscendentalCoefficientInputsLevel = conditional
