module DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic where

-- Local arithmetic boundary for the supplied YM-A/Killing constants.
--
-- This file is intentionally standalone under:
--
--   agda --no-libraries DASHI/Physics/Closure/YMAKillingBoundaryLocalArithmetic.agda
--
-- It records Nat-rational arithmetic rows only.  It accepts the King lower
-- bound as an arithmetic input row, records the concrete SU2/SU3 numerics,
-- and keeps every analytic/domain/promotion obligation fail-closed.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Nat-rational carrier.

record RationalNat : Set where
  constructor rat
  field
    numerator :
      Nat

    denominator :
      Nat

open RationalNat public

data PositiveNat : Nat -> Set where
  positive-suc :
    {n : Nat} ->
    PositiveNat (Agda.Builtin.Nat.suc n)

scaleRat :
  Nat ->
  Nat ->
  RationalNat ->
  RationalNat
scaleRat a b q =
  rat
    (a * numerator q)
    (b * denominator q)

------------------------------------------------------------------------
-- Supplied YM-A constants.

piSquaredApprox :
  RationalNat
piSquaredApprox =
  rat 98696 10000

piSquaredApproxNumeratorRecorded :
  numerator piSquaredApprox ≡ 98696
piSquaredApproxNumeratorRecorded =
  refl

piSquaredApproxDenominatorRecorded :
  denominator piSquaredApprox ≡ 10000
piSquaredApproxDenominatorRecorded =
  refl

data GaugeGroup : Set where
  SU2 :
    GaugeGroup

  SU3 :
    GaugeGroup

groupN :
  GaugeGroup ->
  Nat
groupN SU2 =
  2
groupN SU3 =
  3

casimirAdjoint :
  GaugeGroup ->
  Nat
casimirAdjoint SU2 =
  2
casimirAdjoint SU3 =
  3

bochnerConstant :
  GaugeGroup ->
  Nat
bochnerConstant SU2 =
  2
bochnerConstant SU3 =
  3

su2GammaLowerBound :
  RationalNat
su2GammaLowerBound =
  rat 49348 10000

su3GammaLowerBound :
  RationalNat
su3GammaLowerBound =
  rat 74022 10000

su2C1MarginAtEpsilonOneTenthEpsilonMax :
  RationalNat
su2C1MarginAtEpsilonOneTenthEpsilonMax =
  scaleRat 9 20 su2GammaLowerBound

su3C1MarginAtEpsilonOneTenthEpsilonMax :
  RationalNat
su3C1MarginAtEpsilonOneTenthEpsilonMax =
  scaleRat 9 20 su3GammaLowerBound

------------------------------------------------------------------------
-- Refl arithmetic certificates.

-- gamma_d >= N*pi^2/4 is recorded as equality after clearing
-- denominators for the supplied approximate rows.

KingGammaLowerBoundCleared :
  Nat ->
  RationalNat ->
  Set
KingGammaLowerBoundCleared n gamma =
  numerator gamma * (4 * denominator piSquaredApprox)
    ≡
  (n * numerator piSquaredApprox) * denominator gamma

su2KingGammaLowerBoundCleared :
  KingGammaLowerBoundCleared 2 su2GammaLowerBound
su2KingGammaLowerBoundCleared =
  refl

su3KingGammaLowerBoundCleared :
  KingGammaLowerBoundCleared 3 su3GammaLowerBound
su3KingGammaLowerBoundCleared =
  refl

su2KingNumeratorScaled :
  2 * numerator piSquaredApprox ≡ 197392
su2KingNumeratorScaled =
  refl

su3KingNumeratorScaled :
  3 * numerator piSquaredApprox ≡ 296088
su3KingNumeratorScaled =
  refl

kingQuarterDenominatorScaled :
  4 * denominator piSquaredApprox ≡ 40000
kingQuarterDenominatorScaled =
  refl

su2GammaRowEquivalentToNpiSquaredOverFour :
  numerator su2GammaLowerBound * 40000
    ≡
  197392 * denominator su2GammaLowerBound
su2GammaRowEquivalentToNpiSquaredOverFour =
  refl

su3GammaRowEquivalentToNpiSquaredOverFour :
  numerator su3GammaLowerBound * 40000
    ≡
  296088 * denominator su3GammaLowerBound
su3GammaRowEquivalentToNpiSquaredOverFour =
  refl

su2CasimirAdjointRecorded :
  casimirAdjoint SU2 ≡ 2
su2CasimirAdjointRecorded =
  refl

su3CasimirAdjointRecorded :
  casimirAdjoint SU3 ≡ 3
su3CasimirAdjointRecorded =
  refl

su2BochnerConstantRecorded :
  bochnerConstant SU2 ≡ 2
su2BochnerConstantRecorded =
  refl

su3BochnerConstantRecorded :
  bochnerConstant SU3 ≡ 3
su3BochnerConstantRecorded =
  refl

su2C1MarginNumeratorRecorded :
  numerator su2C1MarginAtEpsilonOneTenthEpsilonMax ≡ 444132
su2C1MarginNumeratorRecorded =
  refl

su2C1MarginDenominatorRecorded :
  denominator su2C1MarginAtEpsilonOneTenthEpsilonMax ≡ 200000
su2C1MarginDenominatorRecorded =
  refl

su3C1MarginNumeratorRecorded :
  numerator su3C1MarginAtEpsilonOneTenthEpsilonMax ≡ 666198
su3C1MarginNumeratorRecorded =
  refl

su3C1MarginDenominatorRecorded :
  denominator su3C1MarginAtEpsilonOneTenthEpsilonMax ≡ 200000
su3C1MarginDenominatorRecorded =
  refl

su2C1MarginEqualsNineTwentiethsGamma :
  su2C1MarginAtEpsilonOneTenthEpsilonMax
    ≡
  scaleRat 9 20 su2GammaLowerBound
su2C1MarginEqualsNineTwentiethsGamma =
  refl

su3C1MarginEqualsNineTwentiethsGamma :
  su3C1MarginAtEpsilonOneTenthEpsilonMax
    ≡
  scaleRat 9 20 su3GammaLowerBound
su3C1MarginEqualsNineTwentiethsGamma =
  refl

su2C1MarginPositive :
  PositiveNat (numerator su2C1MarginAtEpsilonOneTenthEpsilonMax)
su2C1MarginPositive =
  positive-suc

su3C1MarginPositive :
  PositiveNat (numerator su3C1MarginAtEpsilonOneTenthEpsilonMax)
su3C1MarginPositive =
  positive-suc

------------------------------------------------------------------------
-- Row-level package.

record YMALocalArithmeticRow : Set where
  field
    gaugeGroup :
      GaugeGroup

    nValue :
      Nat

    gammaLowerBound :
      RationalNat

    casimirAdjointValue :
      Nat

    bochnerConstantValue :
      Nat

    c1MarginAtEpsilonOneTenthEpsilonMax :
      RationalNat

    nValueRecorded :
      groupN gaugeGroup ≡ nValue

    kingLowerBoundCleared :
      KingGammaLowerBoundCleared nValue gammaLowerBound

    casimirAdjointRecorded :
      casimirAdjoint gaugeGroup ≡ casimirAdjointValue

    bochnerConstantRecorded :
      bochnerConstant gaugeGroup ≡ bochnerConstantValue

    c1MarginRecorded :
      c1MarginAtEpsilonOneTenthEpsilonMax ≡ scaleRat 9 20 gammaLowerBound

    c1MarginPositive :
      PositiveNat (numerator c1MarginAtEpsilonOneTenthEpsilonMax)

su2YMALocalArithmeticRow :
  YMALocalArithmeticRow
su2YMALocalArithmeticRow =
  record
    { gaugeGroup =
        SU2
    ; nValue =
        2
    ; gammaLowerBound =
        su2GammaLowerBound
    ; casimirAdjointValue =
        2
    ; bochnerConstantValue =
        2
    ; c1MarginAtEpsilonOneTenthEpsilonMax =
        su2C1MarginAtEpsilonOneTenthEpsilonMax
    ; nValueRecorded =
        refl
    ; kingLowerBoundCleared =
        refl
    ; casimirAdjointRecorded =
        refl
    ; bochnerConstantRecorded =
        refl
    ; c1MarginRecorded =
        refl
    ; c1MarginPositive =
        positive-suc
    }

su3YMALocalArithmeticRow :
  YMALocalArithmeticRow
su3YMALocalArithmeticRow =
  record
    { gaugeGroup =
        SU3
    ; nValue =
        3
    ; gammaLowerBound =
        su3GammaLowerBound
    ; casimirAdjointValue =
        3
    ; bochnerConstantValue =
        3
    ; c1MarginAtEpsilonOneTenthEpsilonMax =
        su3C1MarginAtEpsilonOneTenthEpsilonMax
    ; nValueRecorded =
        refl
    ; kingLowerBoundCleared =
        refl
    ; casimirAdjointRecorded =
        refl
    ; bochnerConstantRecorded =
        refl
    ; c1MarginRecorded =
        refl
    ; c1MarginPositive =
        positive-suc
    }

------------------------------------------------------------------------
-- Fail-closed theorem flags.

arithmeticRecorded :
  Bool
arithmeticRecorded =
  true

arithmeticRecordedIsTrue :
  arithmeticRecorded ≡ true
arithmeticRecordedIsTrue =
  refl

kingAuthorityAcceptedAsArithmeticInput :
  Bool
kingAuthorityAcceptedAsArithmeticInput =
  true

kingAuthorityAcceptedAsArithmeticInputIsTrue :
  kingAuthorityAcceptedAsArithmeticInput ≡ true
kingAuthorityAcceptedAsArithmeticInputIsTrue =
  refl

domainClosureProved :
  Bool
domainClosureProved =
  false

boundaryFluxCancellationProved :
  Bool
boundaryFluxCancellationProved =
  false

selfAdjointQuotientHamiltonianProved :
  Bool
selfAdjointQuotientHamiltonianProved =
  false

clayYangMillsPromoted :
  Bool
clayYangMillsPromoted =
  false

domainClosureProvedIsFalse :
  domainClosureProved ≡ false
domainClosureProvedIsFalse =
  refl

boundaryFluxCancellationProvedIsFalse :
  boundaryFluxCancellationProved ≡ false
boundaryFluxCancellationProvedIsFalse =
  refl

selfAdjointQuotientHamiltonianProvedIsFalse :
  selfAdjointQuotientHamiltonianProved ≡ false
selfAdjointQuotientHamiltonianProvedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

------------------------------------------------------------------------
-- Control-card strings for audit visibility.

controlO :
  String
controlO =
  "O: local YM-A Killing arithmetic boundary for SU2/SU3 constants"

controlR :
  String
controlR =
  "R: Nat rational pairs, refl certificates, and fail-closed flags"

controlC :
  String
controlC =
  "C: pi^2=98696/10000, gamma rows 49348/10000 and 74022/10000"

controlS :
  String
controlS =
  "S: King gamma lower bound accepted only as arithmetic input"

controlL :
  String
controlL =
  "L: c1 margin at epsilon=0.1 epsilon_max is 9/20 gamma"

controlP :
  String
controlP =
  "P: domain, flux, quotient self-adjointness, and Clay promotion remain false"

controlG :
  String
controlG =
  "G: Agda --no-libraries local arithmetic row typechecks"

controlF :
  String
controlF =
  "F: no analytic theorem or Clay Yang-Mills promotion is proved here"
