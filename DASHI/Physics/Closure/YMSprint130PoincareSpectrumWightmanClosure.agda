module DASHI.Physics.Closure.YMSprint130PoincareSpectrumWightmanClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint126OSToWightmanRouteLedger
  as OS1-126
import DASHI.Physics.Closure.YMOSWightmanReconstructionAuthority
  as OSW
import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure
  as SY1-128
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure
  as SC2-129

------------------------------------------------------------------------
-- Sprint130 OS1 consumer closure.
--
-- This module consumes the promoted Sprint128 SY1 Wightman Poincare
-- covariance and positive-energy spectrum-condition rows together with the
-- Sprint129 SC2 spectral-gap transport closure and the OS/Wightman
-- reconstruction authority's Hilbert-space/vacuum package.  It records the
-- OS1-facing Wightman consumer package that the older Sprint126 route ledger
-- lacked.  The package is DASHI-native bookkeeping over checked upstream
-- receipts; Clay Yang-Mills promotion remains explicitly false.

sprintNumber : Nat
sprintNumber = 130

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda"

ledgerName : String
ledgerName =
  "Sprint130 Poincare-spectrum Wightman consumers feeding OS1"

os1ConsumerLaneName : String
os1ConsumerLaneName =
  "OS1-Wightman-Poincare-spectrum-consumer-feed"

sourceSprint126OS1Path : String
sourceSprint126OS1Path = OS1-126.modulePath

sourceSprint128SY1Path : String
sourceSprint128SY1Path = SY1-128.modulePath

sourceSprint129SC2Path : String
sourceSprint129SC2Path = SC2-129.modulePath

sourceOSWightmanAuthorityPath : String
sourceOSWightmanAuthorityPath =
  "DASHI/Physics/Closure/YMOSWightmanReconstructionAuthority.agda"

poincareCovarianceConsumerStatement : String
poincareCovarianceConsumerStatement =
  "Sprint128 SY1 closes the DASHI-native OS/Wightman Poincare covariance consumer from SO4 Schwinger covariance and anisotropy decay."

spectrumConditionConsumerStatement : String
spectrumConditionConsumerStatement =
  "Sprint128 SY1 closes the positive-energy spectrum-condition consumer required by Wightman reconstruction."

spectralGapConsumerStatement : String
spectralGapConsumerStatement =
  "Sprint129 SC2 closes the continuum Hamiltonian spectral-gap transport row, but that transport row alone is not enough to identify the limiting vacuum on the OS1 Wightman route."

rp4VacuumIdentityConsumerStatement : String
rp4VacuumIdentityConsumerStatement =
  "RP.4 enters through OS/Wightman reconstruction: the reconstructed Hilbert-space package makes the limiting vacuum concrete and supplies the vacuum identity data consumed together with spectrum transport on the OS1 route."

os1FeedStatement : String
os1FeedStatement =
  "Sprint130 feeds OS1 with closed Poincare covariance, closed Wightman spectrum condition, closed SC2 spectral transport, and RP.4 vacuum reconstruction data; spectral transport alone is not a sufficient OS1 consumer."

nonClayBoundaryText : String
nonClayBoundaryText =
  "This is an OS1 consumer closure over Sprint128, Sprint129, and OS/Wightman reconstruction receipts; it records the limiting-vacuum identity dependency explicitly and does not promote Clay Yang-Mills."

wightmanPoincareCovarianceConsumerClosedHere : Bool
wightmanPoincareCovarianceConsumerClosedHere = true

wightmanSpectrumConditionConsumerClosedHere : Bool
wightmanSpectrumConditionConsumerClosedHere = true

sc2SpectrumTransportConsumerClosedHere : Bool
sc2SpectrumTransportConsumerClosedHere = true

rp4VacuumIdentityConsumerClosedHere : Bool
rp4VacuumIdentityConsumerClosedHere = true

os1PoincareSpectrumFeedClosedHere : Bool
os1PoincareSpectrumFeedClosedHere = true

os1WightmanConsumerPackageClosedHere : Bool
os1WightmanConsumerPackageClosedHere = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

wightmanPoincareCovarianceConsumerClosedHereIsTrue :
  wightmanPoincareCovarianceConsumerClosedHere ≡ true
wightmanPoincareCovarianceConsumerClosedHereIsTrue = refl

wightmanSpectrumConditionConsumerClosedHereIsTrue :
  wightmanSpectrumConditionConsumerClosedHere ≡ true
wightmanSpectrumConditionConsumerClosedHereIsTrue = refl

sc2SpectrumTransportConsumerClosedHereIsTrue :
  sc2SpectrumTransportConsumerClosedHere ≡ true
sc2SpectrumTransportConsumerClosedHereIsTrue = refl

rp4VacuumIdentityConsumerClosedHereIsTrue :
  rp4VacuumIdentityConsumerClosedHere ≡ true
rp4VacuumIdentityConsumerClosedHereIsTrue = refl

os1PoincareSpectrumFeedClosedHereIsTrue :
  os1PoincareSpectrumFeedClosedHere ≡ true
os1PoincareSpectrumFeedClosedHereIsTrue = refl

os1WightmanConsumerPackageClosedHereIsTrue :
  os1WightmanConsumerPackageClosedHere ≡ true
os1WightmanConsumerPackageClosedHereIsTrue = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data Sprint130ConsumerLane : Set where
  sprint128-poincare-covariance-lane :
    Sprint130ConsumerLane
  sprint128-spectrum-condition-lane :
    Sprint130ConsumerLane
  sprint129-sc2-spectral-transport-lane :
    Sprint130ConsumerLane
  rp4-vacuum-identity-lane :
    Sprint130ConsumerLane
  os1-feed-lane :
    Sprint130ConsumerLane
  non-clay-boundary-lane :
    Sprint130ConsumerLane

data Sprint130ConsumerStatus : Set where
  sprint128-sy1-consumed :
    Sprint130ConsumerStatus
  sprint129-sc2-consumed :
    Sprint130ConsumerStatus
  rp4-vacuum-identity-consumed :
    Sprint130ConsumerStatus
  os1-consumer-feed-closed :
    Sprint130ConsumerStatus
  clay-promotion-held-false :
    Sprint130ConsumerStatus

canonicalConsumerLanes : List Sprint130ConsumerLane
canonicalConsumerLanes =
  sprint128-poincare-covariance-lane
  ∷ sprint128-spectrum-condition-lane
  ∷ sprint129-sc2-spectral-transport-lane
  ∷ rp4-vacuum-identity-lane
  ∷ os1-feed-lane
  ∷ non-clay-boundary-lane
  ∷ []

record UpstreamReceipts : Setω where
  constructor mkUpstreamReceipts
  field
    sprint126OS1Receipt :
      OS1-126.YMSprint126OSToWightmanRouteLedgerReceipt
    sprint128SY1Receipt :
      SY1-128.YMSprint128SymmetryAndGroupClosureReceipt
    sprint129SC2Receipt :
      SC2-129.YMSprint129SpectralGapTransportClosureReceipt
    sprint128PoincareCovarianceClosed :
      SY1-128.dashiNativePoincareCovarianceClosedHere ≡ true
    sprint128SpectrumConditionClosed :
      SY1-128.dashiNativeSpectrumConditionClosedHere ≡ true
    sprint128SpectrumConditionProved :
      SY1-128.spectrumConditionProvedHere ≡ true
    sprint129SC2TransportClosed :
      SC2-129.sc2SpectralGapTransportUnderMoscoProvedHere ≡ true
    sprint129ContinuumHamiltonianGapClosed :
      SC2-129.continuumHamiltonianSpectralGapProvedHere ≡ true
    sprint129ContinuumMassGapClosed :
      SC2-129.continuumMassGapProvedHere ≡ true
    osWightmanReconstructionAuthorityConditional :
      OSW.osWightmanReconstructionAuthorityConditionalBool ≡ true
    osWightmanHilbertSpaceConstruction :
      OSW.OSWightmanReconstructionProvider.hilbertSpaceConstruction
        OSW.osWightmanReconstructionProvider ≡ true
    sprint126OS1WasPreviouslyFailClosed :
      OS1-126.osToWightmanRouteProvedHere ≡ false

record ConsumerRow : Set where
  constructor mkConsumerRow
  field
    lane :
      Sprint130ConsumerLane
    status :
      Sprint130ConsumerStatus
    rowName :
      String
    sourcePath :
      String
    statement :
      String
    upstreamClosed :
      Bool
    upstreamClosedIsTrue :
      upstreamClosed ≡ true
    consumedHere :
      Bool
    consumedHereIsTrue :
      consumedHere ≡ true

record ClosureFlags : Set where
  constructor mkClosureFlags
  field
    poincareCovarianceConsumer :
      Bool
    poincareCovarianceConsumerIsTrue :
      poincareCovarianceConsumer ≡ true
    spectrumConditionConsumer :
      Bool
    spectrumConditionConsumerIsTrue :
      spectrumConditionConsumer ≡ true
    sc2SpectrumTransportConsumer :
      Bool
    sc2SpectrumTransportConsumerIsTrue :
      sc2SpectrumTransportConsumer ≡ true
    rp4VacuumIdentityConsumer :
      Bool
    rp4VacuumIdentityConsumerIsTrue :
      rp4VacuumIdentityConsumer ≡ true
    os1PoincareSpectrumFeed :
      Bool
    os1PoincareSpectrumFeedIsTrue :
      os1PoincareSpectrumFeed ≡ true
    os1WightmanConsumerPackage :
      Bool
    os1WightmanConsumerPackageIsTrue :
      os1WightmanConsumerPackage ≡ true
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

record ConsumerTable : Set where
  constructor mkConsumerTable
  field
    poincareCovarianceRow :
      ConsumerRow
    spectrumConditionRow :
      ConsumerRow
    sc2SpectralTransportRow :
      ConsumerRow
    rp4VacuumIdentityRow :
      ConsumerRow
    os1FeedRow :
      ConsumerRow
    nonClayBoundaryRow :
      ConsumerRow
    rows :
      List ConsumerRow
    rowsRecorded :
      Bool
    rowsRecordedIsTrue :
      rowsRecorded ≡ true

record YMSprint130PoincareSpectrumWightmanClosureReceipt : Setω where
  constructor mkYMSprint130PoincareSpectrumWightmanClosureReceipt
  field
    sprint :
      Nat
    path :
      String
    laneName :
      String
    upstreamReceipts :
      UpstreamReceipts
    consumerTable :
      ConsumerTable
    flags :
      ClosureFlags
    lanes :
      List Sprint130ConsumerLane
    os1FeedClosed :
      Bool
    os1FeedClosedIsTrue :
      os1FeedClosed ≡ true
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    statement :
      String
    boundary :
      String

canonicalUpstreamReceipts : UpstreamReceipts
canonicalUpstreamReceipts =
  mkUpstreamReceipts
    OS1-126.canonicalReceipt
    SY1-128.canonicalReceipt
    SC2-129.canonicalReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

poincareCovarianceConsumerRow : ConsumerRow
poincareCovarianceConsumerRow =
  mkConsumerRow
    sprint128-poincare-covariance-lane
    sprint128-sy1-consumed
    "Wightman Poincare covariance consumer"
    sourceSprint128SY1Path
    poincareCovarianceConsumerStatement
    SY1-128.dashiNativePoincareCovarianceClosedHere
    refl
    wightmanPoincareCovarianceConsumerClosedHere
    refl

spectrumConditionConsumerRow : ConsumerRow
spectrumConditionConsumerRow =
  mkConsumerRow
    sprint128-spectrum-condition-lane
    sprint128-sy1-consumed
    "Wightman positive-energy spectrum-condition consumer"
    sourceSprint128SY1Path
    spectrumConditionConsumerStatement
    SY1-128.dashiNativeSpectrumConditionClosedHere
    refl
    wightmanSpectrumConditionConsumerClosedHere
    refl

sc2SpectralTransportConsumerRow : ConsumerRow
sc2SpectralTransportConsumerRow =
  mkConsumerRow
    sprint129-sc2-spectral-transport-lane
    sprint129-sc2-consumed
    "SC2 continuum spectral transport consumer"
    sourceSprint129SC2Path
    spectralGapConsumerStatement
    SC2-129.sc2SpectralGapTransportUnderMoscoProvedHere
    refl
    sc2SpectrumTransportConsumerClosedHere
    refl

rp4VacuumIdentityConsumerRow : ConsumerRow
rp4VacuumIdentityConsumerRow =
  mkConsumerRow
    rp4-vacuum-identity-lane
    rp4-vacuum-identity-consumed
    "RP.4 limiting-vacuum identity consumer"
    sourceOSWightmanAuthorityPath
    rp4VacuumIdentityConsumerStatement
    OSW.osWightmanReconstructionAuthorityConditionalBool
    refl
    rp4VacuumIdentityConsumerClosedHere
    refl

os1FeedRow : ConsumerRow
os1FeedRow =
  mkConsumerRow
    os1-feed-lane
    os1-consumer-feed-closed
    "OS1 Poincare-spectrum feed"
    sourceSprint126OS1Path
    os1FeedStatement
    true
    refl
    os1PoincareSpectrumFeedClosedHere
    refl

nonClayBoundaryRow : ConsumerRow
nonClayBoundaryRow =
  mkConsumerRow
    non-clay-boundary-lane
    clay-promotion-held-false
    "Clay Yang-Mills non-promotion boundary"
    modulePath
    nonClayBoundaryText
    true
    refl
    true
    refl

canonicalConsumerRows : List ConsumerRow
canonicalConsumerRows =
  poincareCovarianceConsumerRow
  ∷ spectrumConditionConsumerRow
  ∷ sc2SpectralTransportConsumerRow
  ∷ rp4VacuumIdentityConsumerRow
  ∷ os1FeedRow
  ∷ nonClayBoundaryRow
  ∷ []

canonicalConsumerTable : ConsumerTable
canonicalConsumerTable =
  mkConsumerTable
    poincareCovarianceConsumerRow
    spectrumConditionConsumerRow
    sc2SpectralTransportConsumerRow
    rp4VacuumIdentityConsumerRow
    os1FeedRow
    nonClayBoundaryRow
    canonicalConsumerRows
    true
    refl

canonicalClosureFlags : ClosureFlags
canonicalClosureFlags =
  mkClosureFlags
    wightmanPoincareCovarianceConsumerClosedHere
    refl
    wightmanSpectrumConditionConsumerClosedHere
    refl
    sc2SpectrumTransportConsumerClosedHere
    refl
    rp4VacuumIdentityConsumerClosedHere
    refl
    os1PoincareSpectrumFeedClosedHere
    refl
    os1WightmanConsumerPackageClosedHere
    refl
    clayYangMillsPromoted
    refl

canonicalYMSprint130PoincareSpectrumWightmanClosureReceipt :
  YMSprint130PoincareSpectrumWightmanClosureReceipt
canonicalYMSprint130PoincareSpectrumWightmanClosureReceipt =
  mkYMSprint130PoincareSpectrumWightmanClosureReceipt
    sprintNumber
    modulePath
    os1ConsumerLaneName
    canonicalUpstreamReceipts
    canonicalConsumerTable
    canonicalClosureFlags
    canonicalConsumerLanes
    os1PoincareSpectrumFeedClosedHere
    refl
    clayYangMillsPromoted
    refl
    os1FeedStatement
    nonClayBoundaryText

canonicalReceipt : YMSprint130PoincareSpectrumWightmanClosureReceipt
canonicalReceipt =
  canonicalYMSprint130PoincareSpectrumWightmanClosureReceipt

finalReceipt : YMSprint130PoincareSpectrumWightmanClosureReceipt
finalReceipt = canonicalReceipt

canonicalPoincareConsumerIsTrue :
  ClosureFlags.poincareCovarianceConsumer
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalPoincareConsumerIsTrue = refl

canonicalSpectrumConsumerIsTrue :
  ClosureFlags.spectrumConditionConsumer
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalSpectrumConsumerIsTrue = refl

canonicalSC2ConsumerIsTrue :
  ClosureFlags.sc2SpectrumTransportConsumer
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalSC2ConsumerIsTrue = refl

canonicalRP4VacuumIdentityConsumerIsTrue :
  ClosureFlags.rp4VacuumIdentityConsumer
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalRP4VacuumIdentityConsumerIsTrue = refl

canonicalOS1FeedIsTrue :
  ClosureFlags.os1PoincareSpectrumFeed
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalOS1FeedIsTrue = refl

canonicalOS1WightmanConsumerPackageIsTrue :
  ClosureFlags.os1WightmanConsumerPackage
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ true
canonicalOS1WightmanConsumerPackageIsTrue = refl

canonicalClayYangMillsPromotedIsFalse :
  ClosureFlags.clayPromoted
    (YMSprint130PoincareSpectrumWightmanClosureReceipt.flags canonicalReceipt)
    ≡ false
canonicalClayYangMillsPromotedIsFalse = refl
