module DASHI.Physics.Closure.NSCompactGammaCanonicalParameterBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Sigma using (_,_)
import Agda.Builtin.Nat as Nat

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic
import DASHI.Physics.Closure.NSCompactGammaParameterCoverageCompletion as Parameters

------------------------------------------------------------------------
-- Semantic interpretation of the exact dyadic certificate.
--
-- The finite arithmetic is not itself a real/Fourier estimate.  This bridge
-- requires explicit interpretation functions for each certified comparison and
-- constructs the repository's `CanonicalParameterInequalities` record.  The
-- simultaneous witness is derived from the five component witnesses rather than
-- accepted as an unrelated field.
------------------------------------------------------------------------

onePositiveCode :
  Dyadic._≤ᴺ_ (suc zero) Dyadic.oneᴰ
onePositiveCode = Dyadic.s≤s Dyadic.z≤n

twoPositiveCode :
  Dyadic._≤ᴺ_ (suc zero) Dyadic.twoᴰ
twoPositiveCode = Dyadic.s≤s Dyadic.z≤n

record CanonicalParameterSemanticBridge
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (N : Parameters.CanonicalParameterNumerals {i} A) : Set (lsuc i) where
  field
    Positive StrictlyBelow : Scalar A → Set i
    LessThan : Scalar A → Scalar A → Set i

    radiusLargeEnoughForTail : Set i

    gammaFloorFromQuarter :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.quarterᴰ →
      Positive (Parameters.quarter N)

    energyFloorFromQuarter :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.quarterᴰ →
      Positive (Parameters.quarter N)

    offPacketCeilingFromHalf :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.halfᴰ →
      Positive (Parameters.half N)

    offPacketCeilingStrictFromHalf :
      Dyadic._≤ᴺ_ (suc Dyadic.halfᴰ) Dyadic.oneᴰ →
      LessThan (Parameters.half N) (Parameters.one N)

    alphaEnergyFromTwo :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.twoᴰ →
      Positive (Parameters.two N)

    alphaGammaFromTwo :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.twoᴰ →
      Positive (Parameters.two N)

    alphaOffPacketFromOne :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.oneᴰ →
      Positive (Parameters.one N)

    PacketWeightAbsorbs GammaWeightAbsorbs OffPacketWeightAbsorbs :
      Index → Set i

    packetWeightFromCertificate :
      Dyadic._≤ᴺ_
        Dyadic.packetLoss
        (Nat._*_ Dyadic.twoᴺ Dyadic.packetGain) →
      ∀ q → PacketWeightAbsorbs q

    gammaWeightFromCertificate :
      Dyadic._≤ᴺ_
        Dyadic.gammaLoss
        (Nat._*_ Dyadic.twoᴺ Dyadic.gammaGain) →
      ∀ q → GammaWeightAbsorbs q

    offPacketWeightFromCertificate :
      Dyadic._≤ᴺ_ Dyadic.offPacketLoss Dyadic.offPacketGain →
      ∀ q → OffPacketWeightAbsorbs q

    TailAbsorption GammaInward PacketEnergyPositive OffPacketInward :
      Index → Set i
    TotalCoercive : Index → Set i

    tailAbsorptionFromRadiusEight :
      Dyadic.RadiusEightAnalyticBounds →
      ∀ q → TailAbsorption q

    gammaInwardAtCanonicalTuple : ∀ q → GammaInward q
    packetEnergyPositiveAtCanonicalTuple : ∀ q → PacketEnergyPositive q
    offPacketInwardAtCanonicalTuple : ∀ q → OffPacketInward q

    totalCoerciveFromCertificate :
      Dyadic._≤ᴺ_ (suc zero) Dyadic.canonicalCoerciveRemainder →
      ∀ q → TotalCoercive q

open CanonicalParameterSemanticBridge public

canonicalParameterInequalitiesFromBridge :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {N : Parameters.CanonicalParameterNumerals {i} A} →
  (B : CanonicalParameterSemanticBridge A Index N) →
  Dyadic.RadiusEightAnalyticBounds →
  Parameters.CanonicalParameterInequalities A Index N
canonicalParameterInequalitiesFromBridge B R8 = record
  { Positive = Positive B
  ; StrictlyBelow = StrictlyBelow B
  ; LessThan = LessThan B
  ; radiusLargeEnoughForTail = radiusLargeEnoughForTail B
  ; gammaFloorCompatible = gammaFloorFromQuarter B Dyadic.quarterPositiveᴰ
  ; energyFloorCompatible = energyFloorFromQuarter B Dyadic.quarterPositiveᴰ
  ; offPacketCeilingPositive = offPacketCeilingFromHalf B Dyadic.halfPositiveᴰ
  ; offPacketCeilingStrict =
      offPacketCeilingStrictFromHalf B Dyadic.halfStrictBarrierᴰ
  ; alphaEnergyPositive = alphaEnergyFromTwo B twoPositiveCode
  ; alphaGammaPositive = alphaGammaFromTwo B twoPositiveCode
  ; alphaOffPacketPositive = alphaOffPacketFromOne B onePositiveCode
  ; packetWeightAbsorbsError =
      packetWeightFromCertificate B Dyadic.packetWeightTwoAbsorbsᴰ
  ; gammaWeightAbsorbsError =
      gammaWeightFromCertificate B Dyadic.gammaWeightTwoAbsorbsᴰ
  ; offPacketWeightAbsorbsError =
      offPacketWeightFromCertificate B Dyadic.offPacketWeightOneAbsorbsᴰ
  ; tailAbsorptionAtCanonicalTuple = tailAbsorptionFromRadiusEight B R8
  ; gammaInwardAtCanonicalTuple = gammaInwardAtCanonicalTuple B
  ; packetEnergyPositiveAtCanonicalTuple =
      packetEnergyPositiveAtCanonicalTuple B
  ; offPacketInwardAtCanonicalTuple = offPacketInwardAtCanonicalTuple B
  ; totalCoerciveCoefficientPositive =
      totalCoerciveFromCertificate B
        Dyadic.canonicalTotalCoerciveCoefficientPositiveᴰ
  ; allCanonicalConditionsHold = λ q →
      tailAbsorptionFromRadiusEight B R8 q ,
      (gammaInwardAtCanonicalTuple B q ,
      (packetEnergyPositiveAtCanonicalTuple B q ,
      (offPacketInwardAtCanonicalTuple B q ,
       totalCoerciveFromCertificate B
         Dyadic.canonicalTotalCoerciveCoefficientPositiveᴰ q)))
  }
