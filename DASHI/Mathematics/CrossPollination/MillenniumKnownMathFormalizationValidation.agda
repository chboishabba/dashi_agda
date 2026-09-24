module DASHI.Mathematics.CrossPollination.MillenniumKnownMathFormalizationValidation where

------------------------------------------------------------------------
-- VALIDATION RECEIPTS FOR THE PAYABLE FORMALISATION TRANCHE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHodgeReopeningCompilerExact as HodgeCP
import DASHI.Mathematics.AlgebraicGeometry.HodgeAlgebraicCycleClayCoreExact as HodgeCore
import DASHI.Mathematics.Arithmetic.EllipticCurveGlobalLocalCoefficientExact as BSDLocal
import DASHI.Mathematics.Automorphic.TruncatedLFunctionExact as Truncated
import DASHI.Mathematics.Complexity.RSAQuantumShorPvsNPCrossPollinationExact as PNP

projectiveSpaceReopeningCompilerPresent :
  HodgeCP.hyperplanePowerReopeningCompilerPaid
    HodgeCP.canonicalProjectiveSpaceLiteralReopeningBoundary
  ≡ true
projectiveSpaceReopeningCompilerPresent = refl

projectiveSpaceGeometryStillExplicit :
  HodgeCP.actualCPnGeometricIdentificationPaid
    HodgeCP.canonicalProjectiveSpaceLiteralReopeningBoundary
  ≡ false
projectiveSpaceGeometryStillExplicit = refl

generalHodgeStillOpen :
  HodgeCP.generalHodgeConjecturePaid
    HodgeCP.canonicalProjectiveSpaceLiteralReopeningBoundary
  ≡ false
generalHodgeStillOpen = refl

costAwarePvsNPFactorisationPresent :
  PNP.costAwareFactorisationCompilerPresent
    PNP.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
costAwarePvsNPFactorisationPresent = refl

satDecisionSearchPresent :
  PNP.booleanFormulaSATSelfReductionInstantiationPaid
    PNP.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ true
satDecisionSearchPresent = refl

genericCookLevinStillExplicit :
  PNP.genericCookLevinCNFPolynomialityPaid
    PNP.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
genericCookLevinStillExplicit = refl

pvsnpStillOpen :
  PNP.classicalPvsNPResolved
    PNP.canonicalPvsNPRSAQuantumCrossPollinationBoundary
  ≡ false
pvsnpStillOpen = refl

------------------------------------------------------------------------
-- Type-level smoke tests: the global-local BSD owner exposes one prime-indexed
-- family, explicit good-prime restrictions, and the local-factor restriction
-- theorem without supplying a fictitious all-prime arithmetic inhabitant.
------------------------------------------------------------------------

globalLocalFamilyTypeAvailable :
  ∀ curve →
  Set₁
globalLocalFamilyTypeAvailable curve =
  BSDLocal.EllipticCurveGlobalLocalCoefficient curve

goodPrimeRestrictionTheoremAvailable :
  ∀ {curve}
    (family : BSDLocal.EllipticCurveGlobalLocalCoefficient curve)
    (p : Nat)
    (restriction : BSDLocal.FiniteGoodPrimeRestriction family p)
    T →
  Truncated.localEulerFactorValue
    (BSDLocal.goodPrimeCoefficientData family)
    (BSDLocal.restrictedPrimeNorm restriction)
    T
  ≡ BSDLocal.localPolynomialValue (BSDLocal.localAtPrime family p) T
goodPrimeRestrictionTheoremAvailable =
  BSDLocal.restrictedLocalFactorIsGlobal


------------------------------------------------------------------------
-- Hodge Clay freeze receipts: the remaining conjectural endpoint is now
-- typed on literal RationalAlgebraicCycle, while comparison/cycle-class
-- construction remains established-background debt.
------------------------------------------------------------------------

hodgeRationalIntersectionTypedExactly :
  HodgeCore.rationalIntersectionTypedExactly
    HodgeCore.canonicalHodgeClayFreezeBoundary
  ≡ true
hodgeRationalIntersectionTypedExactly = refl

hodgeLiteralAlgebraicCycleCarrierPaid :
  HodgeCore.algebraicCycleCarrierTypedLiterally
    HodgeCore.canonicalHodgeClayFreezeBoundary
  ≡ true
hodgeLiteralAlgebraicCycleCarrierPaid = refl

hodgeCycleComparisonRemainsBackground :
  HodgeCore.cycleComparisonStillBackground
    HodgeCore.canonicalHodgeClayFreezeBoundary
  ≡ true
hodgeCycleComparisonRemainsBackground = refl

hodgeUniversalReopeningStillOpen :
  HodgeCore.universalAlgebraicReopeningProved
    HodgeCore.canonicalHodgeClayFreezeBoundary
  ≡ false
hodgeUniversalReopeningStillOpen = refl
