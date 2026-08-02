module DASHI.Foundations.UBP.ExactnessAndLatticeBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.CarrierPromotionBoundaryCore as CarrierBoundary

------------------------------------------------------------------------
-- Exact irrational target versus exact rational execution.
--
-- The operational UBP constant obtained from a finite continued-fraction
-- convergent is an exact rational model constant.  It is not thereby an
-- exact representation of the irrational real target 1/(pi + 2/pi).

Not :
  Set →
  Set
Not A =
  A → ⊥

record IrrationalObserverConstantBoundary : Set₁ where
  field
    RealCarrier :
      Set

    embedRational :
      ℚ →
      RealCarrier

    exactObserverConstant :
      RealCarrier

    IsRational :
      RealCarrier →
      Set

    embeddedRationalsAreRational :
      (q : ℚ) →
      IsRational (embedRational q)

    exactObserverConstantIsIrrational :
      IsRational exactObserverConstant →
      ⊥

open IrrationalObserverConstantBoundary public

rationalFractionCannotEqualExactObserverConstant :
  (boundary : IrrationalObserverConstantBoundary) →
  (q : ℚ) →
  embedRational boundary q ≡ exactObserverConstant boundary →
  ⊥
rationalFractionCannotEqualExactObserverConstant boundary q equality =
  exactObserverConstantIsIrrational boundary
    (subst
      (IsRational boundary)
      equality
      (embeddedRationalsAreRational boundary q))

data ObserverConstantRole : Set where
  exactIrrationalTargetRole :
    ObserverConstantRole

  finiteContinuedFractionApproximationRole :
    ObserverConstantRole

  rationalIntervalLowerBoundRole :
    ObserverConstantRole

  rationalIntervalUpperBoundRole :
    ObserverConstantRole

record ObserverConstantStatus : Set where
  constructor observerConstantStatus
  field
    statusLabel :
      String

    exactTargetFormula :
      String

    implementedConstantReading :
      String

    implementedRole :
      ObserverConstantRole

    exactRationalExecution :
      Bool

    exactRationalExecutionIsTrue :
      exactRationalExecution ≡ true

    exactIrrationalTargetRepresentedByFraction :
      Bool

    exactIrrationalTargetRepresentedByFractionIsFalse :
      exactIrrationalTargetRepresentedByFraction ≡ false

    intervalCertificationRequiredForTargetClaim :
      Bool

    intervalCertificationRequiredForTargetClaimIsTrue :
      intervalCertificationRequiredForTargetClaim ≡ true

    zeroBinaryFloatDriftImpliesExactTarget :
      Bool

    zeroBinaryFloatDriftImpliesExactTargetIsFalse :
      zeroBinaryFloatDriftImpliesExactTarget ≡ false

open ObserverConstantStatus public

canonicalObserverConstantStatus :
  ObserverConstantStatus
canonicalObserverConstantStatus =
  observerConstantStatus
    "UBP observer constant exactness boundary"
    "Y = 1 / (pi + 2 / pi) on an exact real carrier"
    "Y_50 = 1 / (pi_50 + 2 / pi_50) on the rational carrier selected by the finite continued-fraction implementation"
    finiteContinuedFractionApproximationRole
    true
    refl
    false
    refl
    true
    refl
    false
    refl

record RationalIntervalCertificate
    (boundary : IrrationalObserverConstantBoundary) : Set₁ where
  field
    lower :
      ℚ

    upper :
      ℚ

    StrictOrder :
      RealCarrier boundary →
      RealCarrier boundary →
      Set

    lowerBelowExact :
      StrictOrder
        (embedRational boundary lower)
        (exactObserverConstant boundary)

    exactBelowUpper :
      StrictOrder
        (exactObserverConstant boundary)
        (embedRational boundary upper)

    intervalReading :
      String

open RationalIntervalCertificate public

------------------------------------------------------------------------
-- Ambient coordinate probes versus Leech-lattice members.
--
-- In the integer normalisation used by the supplied checkpoint, a single
-- 4e_i probe has squared norm 16.  A rootless Leech lattice has no member at
-- that norm.  Closure therefore cannot be invoked until membership of both
-- summands has already been supplied.

Coordinate24 :
  Set
Coordinate24 =
  Fin 24

record AmbientLeechAddressBoundary : Set₁ where
  field
    Ambient24 :
      Set

    InLeech :
      Ambient24 →
      Set

    integerNormSquared :
      Ambient24 →
      Nat

    bitAddress :
      Coordinate24 →
      Ambient24

    bitAddressNormSquaredIs16 :
      (coordinate : Coordinate24) →
      integerNormSquared (bitAddress coordinate) ≡ 16

    leechHasNoIntegerNormSquared16 :
      (point : Ambient24) →
      InLeech point →
      integerNormSquared point ≡ 16 →
      ⊥

open AmbientLeechAddressBoundary public

bitAddressIsNotLeechMember :
  (boundary : AmbientLeechAddressBoundary) →
  (coordinate : Coordinate24) →
  InLeech boundary (bitAddress boundary coordinate) →
  ⊥
bitAddressIsNotLeechMember boundary coordinate membership =
  leechHasNoIntegerNormSquared16 boundary
    (bitAddress boundary coordinate)
    membership
    (bitAddressNormSquaredIs16 boundary coordinate)

record LeechMembershipCertificate
    (boundary : AmbientLeechAddressBoundary)
    (point : Ambient24 boundary) : Set₁ where
  field
    GolayCosetWitness :
      Set

    ParityWitness :
      Set

    GlueWitness :
      Set

    golayCosetWitness :
      GolayCosetWitness

    parityWitness :
      ParityWitness

    glueWitness :
      GlueWitness

    certifiedMembership :
      InLeech boundary point

open LeechMembershipCertificate public

record LatticeClosureBoundary
    (boundary : AmbientLeechAddressBoundary) : Set₁ where
  field
    addAmbient :
      Ambient24 boundary →
      Ambient24 boundary →
      Ambient24 boundary

    closedUnderAddition :
      {left right : Ambient24 boundary} →
      InLeech boundary left →
      InLeech boundary right →
      InLeech boundary (addAmbient left right)

open LatticeClosureBoundary public

data AddressRole : Set where
  ambientCoordinateProbe :
    AddressRole

  certifiedLeechMember :
    AddressRole

record AmbientAddressStatus : Set where
  constructor ambientAddressStatus
  field
    addressRole :
      AddressRole

    individualAddressMembershipClaim :
      Bool

    individualAddressMembershipClaimIsFalse :
      individualAddressMembershipClaim ≡ false

    closureCanBeAppliedWithoutMembershipPremises :
      Bool

    closureCanBeAppliedWithoutMembershipPremisesIsFalse :
      closureCanBeAppliedWithoutMembershipPremises ≡ false

    fullGolayParityGlueCertificateRequired :
      Bool

    fullGolayParityGlueCertificateRequiredIsTrue :
      fullGolayParityGlueCertificateRequired ≡ true

    statusReading :
      String

open AmbientAddressStatus public

canonicalAmbientAddressStatus :
  AmbientAddressStatus
canonicalAmbientAddressStatus =
  ambientAddressStatus
    ambientCoordinateProbe
    false
    refl
    false
    refl
    true
    refl
    "4e_i is an ambient R^24 coordinate probe in the supplied normalisation; Leech membership requires an independent Golay/parity/glue certificate"

------------------------------------------------------------------------
-- Existing DASHI fail-closed integration.

ubpExactnessAuthorityBundle :
  Authority.AuthorityNonPromotionBundle
ubpExactnessAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "UBP exactness and Leech-address authority boundary"

ubpExactnessCarrierBoundary :
  CarrierBoundary.CarrierPromotionReceipt
ubpExactnessCarrierBoundary =
  CarrierBoundary.canonicalQQCarrierPromotionReceipt

ubpExactnessAndLatticeReceipt :
  GenericReceipt.GenericReceipt
ubpExactnessAndLatticeReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP exactness and Leech-address boundary"
    "DASHI.Foundations.UBP.ExactnessAndLatticeBoundary"
    "canonicalObserverConstantStatus and canonicalAmbientAddressStatus"
    "proves generically that a rational embedding cannot equal an irrational observer constant and that a norm-16 ambient bit address cannot be a member of a rootless integer-normalised Leech lattice"
    "a concrete exact-real backend, irrationality witness, interval certificate, and full Golay/parity/glue membership certificates remain explicit inputs"
    "agda -i . DASHI/Foundations/UBP/ExactnessAndLatticeBoundary.agda"

ubpExactnessAndLatticeReceiptNonPromoting :
  GenericReceipt.promotesClaim ubpExactnessAndLatticeReceipt ≡ false
ubpExactnessAndLatticeReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse ubpExactnessAndLatticeReceipt
