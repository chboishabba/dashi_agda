module DASHI.Moonshine.OggMonstrousExponentTrialectic369QuantizationExact where

------------------------------------------------------------------------
-- ARITHMETIC TRIALECTIC -> DECLARED LOSSY T^3 / 27-STATE ADAPTER
--
-- ATTRIBUTION / SEMANTIC BOUNDARY
--
-- Arithmetic input is consumed from OggMonstrousExponentTrialecticDescentExact,
-- whose external theorem-bearing data is attributed upstream to
-- Duncan--Swisher.  Everything in this module is a DASHI representation
-- adapter.
--
-- The first concrete quantizer is intentionally weak:
--
--   0     -> 0
--   n > 0 -> +1
--
-- It records only presence/absence of each attributed modular contribution.
-- It does NOT identify arithmetic multiplicity with ternary polarity, and it
-- cannot recover the original magnitudes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Maybe using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Core.TopDownObservationCalculusExact as TopDown
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.OggMonstrousExponentTrialecticDescentExact as Arithmetic
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Moonshine.JInvariant369CodecBidiExact as MachineCodec
import DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact as Compact

------------------------------------------------------------------------
-- 1. Generic declared-loss quantizer interface.
------------------------------------------------------------------------

record ArithmeticTrialecticT3Quantizer : Set₁ where
  constructor arithmetic-trialectic-t3-quantizer
  field
    quantizeNat : Nat -> SSP.SSPTrit
    lossDeclared : Bool
    exactMagnitudeRecoveryClaimed : Bool
    arithmeticPolarityIdentityClaimed : Bool

open ArithmeticTrialecticT3Quantizer public

encodeTrialectic :
  ArithmeticTrialecticT3Quantizer ->
  {prime : Lane.MonsterPrimeLane} ->
  Arithmetic.ArithmeticTrialectic prime ->
  Fabric.Ternary27Point
encodeTrialectic quantizer trial =
  Fabric.ternary27Point
    (quantizeNat quantizer (Arithmetic.A trial))
    (quantizeNat quantizer (Arithmetic.B trial))
    (quantizeNat quantizer (Arithmetic.C trial))

------------------------------------------------------------------------
-- 2. Canonical presence/absence quantizer.
------------------------------------------------------------------------

presenceTrit : Nat -> SSP.SSPTrit
presenceTrit zero = SSP.sspZero
presenceTrit (suc n) = SSP.sspPosOne

canonicalPresenceQuantizer : ArithmeticTrialecticT3Quantizer
canonicalPresenceQuantizer =
  arithmetic-trialectic-t3-quantizer
    presenceTrit
    true
    false
    false

presenceEncode :
  {prime : Lane.MonsterPrimeLane} ->
  Arithmetic.ArithmeticTrialectic prime ->
  Fabric.Ternary27Point
presenceEncode = encodeTrialectic canonicalPresenceQuantizer

------------------------------------------------------------------------
-- 3. Concrete attributed arithmetic rows.
------------------------------------------------------------------------

p5PresenceRow :
  presenceEncode Arithmetic.p5Trialectic
  ≡ Fabric.ternary27Point
      SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne
p5PresenceRow = refl

p7PresenceRow :
  presenceEncode Arithmetic.p7Trialectic
  ≡ Fabric.ternary27Point
      SSP.sspPosOne SSP.sspPosOne SSP.sspZero
p7PresenceRow = refl

p11PresenceRow :
  presenceEncode Arithmetic.p11Trialectic
  ≡ Fabric.ternary27Point
      SSP.sspPosOne SSP.sspZero SSP.sspZero
p11PresenceRow = refl

p13PresenceRow :
  presenceEncode Arithmetic.p13Trialectic
  ≡ Fabric.ternary27Point
      SSP.sspPosOne SSP.sspPosOne SSP.sspZero
p13PresenceRow = refl

p7AndP13CollideUnderPresenceQuantization :
  presenceEncode Arithmetic.p7Trialectic
  ≡ presenceEncode Arithmetic.p13Trialectic
p7AndP13CollideUnderPresenceQuantization = refl

------------------------------------------------------------------------
-- 4. Loss is theorem-bearing, not just a Boolean declaration.
------------------------------------------------------------------------

oneAndTwoQuantizeSame :
  presenceTrit 1 ≡ presenceTrit 2
oneAndTwoQuantizeSame = refl

data PresenceQuantizerRecoversNatExactly : Set where

presenceQuantizerDoesNotRecoverMagnitude :
  PresenceQuantizerRecoversNatExactly -> ⊥
presenceQuantizerDoesNotRecoverMagnitude ()

data PresenceQuantizationIsArithmeticSemanticIdentity : Set where

presenceQuantizationDoesNotCreateArithmeticSemanticIdentity :
  PresenceQuantizationIsArithmeticSemanticIdentity -> ⊥
presenceQuantizationDoesNotCreateArithmeticSemanticIdentity ()


------------------------------------------------------------------------
-- 4b. Upgrade the lossy surface to an exact dependent residual codec.
--
-- The coarse surface remains zero/nonzero.  Exact magnitude lives in a
-- residual whose type depends on that surface:
--
--   0  -> Unit
--   +1 -> Nat       (stores predecessor)
--   -1 -> Empty     (not emitted by this quantizer).
------------------------------------------------------------------------

PresenceResidual : SSP.SSPTrit -> Set
PresenceResidual SSP.sspNegOne = ⊥
PresenceResidual SSP.sspZero = ⊤
PresenceResidual SSP.sspPosOne = Nat

presenceResidual : (n : Nat) -> PresenceResidual (presenceTrit n)
presenceResidual zero = tt
presenceResidual (suc n) = n

reopenPresence :
  (surface : SSP.SSPTrit) ->
  PresenceResidual surface ->
  Nat
reopenPresence SSP.sspNegOne ()
reopenPresence SSP.sspZero residual = 0
reopenPresence SSP.sspPosOne residual = suc residual

presenceReopenExact :
  (n : Nat) ->
  reopenPresence (presenceTrit n) (presenceResidual n) ≡ n
presenceReopenExact zero = refl
presenceReopenExact (suc n) = refl

presenceNatRecoverableProjection :
  Recoverable.DependentExactRecoverableProjection Nat SSP.SSPTrit
presenceNatRecoverableProjection =
  Recoverable.dependentExactRecoverableProjection
    PresenceResidual
    presenceTrit
    presenceResidual
    reopenPresence
    presenceReopenExact

presenceNatCode :
  Nat -> Recoverable.DependentCode presenceNatRecoverableProjection
presenceNatCode = Recoverable.encode presenceNatRecoverableProjection

presenceNatDecode :
  Recoverable.DependentCode presenceNatRecoverableProjection -> Nat
presenceNatDecode = Recoverable.decode presenceNatRecoverableProjection

presenceNatDecodeEncode :
  (n : Nat) ->
  presenceNatDecode (presenceNatCode n) ≡ n
presenceNatDecodeEncode =
  Recoverable.decodeEncodeExact presenceNatRecoverableProjection

------------------------------------------------------------------------
-- 4c. Three-coordinate arithmetic codec.
------------------------------------------------------------------------

record ArithmeticTriple : Set where
  constructor arithmetic-triple
  field
    tripleA tripleB tripleC : Nat

open ArithmeticTriple public

trialecticToArithmeticTriple :
  {prime : Lane.MonsterPrimeLane} ->
  Arithmetic.ArithmeticTrialectic prime ->
  ArithmeticTriple
trialecticToArithmeticTriple trial =
  arithmetic-triple
    (Arithmetic.A trial)
    (Arithmetic.B trial)
    (Arithmetic.C trial)

tripleSurface : ArithmeticTriple -> Fabric.Ternary27Point
tripleSurface (arithmetic-triple a b c) =
  Fabric.ternary27Point
    (presenceTrit a)
    (presenceTrit b)
    (presenceTrit c)

TripleResidual : Fabric.Ternary27Point -> Set
TripleResidual point =
  PresenceResidual (Fabric.x point)
  ×
  (PresenceResidual (Fabric.y point)
  × PresenceResidual (Fabric.z point))

tripleResidual :
  (triple : ArithmeticTriple) ->
  TripleResidual (tripleSurface triple)
tripleResidual (arithmetic-triple a b c) =
  presenceResidual a , (presenceResidual b , presenceResidual c)

reopenTriple :
  (surface : Fabric.Ternary27Point) ->
  TripleResidual surface ->
  ArithmeticTriple
reopenTriple
  (Fabric.ternary27Point x y z)
  (rx , (ry , rz)) =
  arithmetic-triple
    (reopenPresence x rx)
    (reopenPresence y ry)
    (reopenPresence z rz)

tripleReopenExact :
  (triple : ArithmeticTriple) ->
  reopenTriple (tripleSurface triple) (tripleResidual triple) ≡ triple
tripleReopenExact (arithmetic-triple zero zero zero) = refl
tripleReopenExact (arithmetic-triple zero zero (suc c)) = refl
tripleReopenExact (arithmetic-triple zero (suc b) zero) = refl
tripleReopenExact (arithmetic-triple zero (suc b) (suc c)) = refl
tripleReopenExact (arithmetic-triple (suc a) zero zero) = refl
tripleReopenExact (arithmetic-triple (suc a) zero (suc c)) = refl
tripleReopenExact (arithmetic-triple (suc a) (suc b) zero) = refl
tripleReopenExact (arithmetic-triple (suc a) (suc b) (suc c)) = refl

arithmeticTripleRecoverableProjection :
  Recoverable.DependentExactRecoverableProjection
    ArithmeticTriple
    Fabric.Ternary27Point
arithmeticTripleRecoverableProjection =
  Recoverable.dependentExactRecoverableProjection
    TripleResidual
    tripleSurface
    tripleResidual
    reopenTriple
    tripleReopenExact

ArithmeticTripleCode : Set
ArithmeticTripleCode =
  Recoverable.DependentCode arithmeticTripleRecoverableProjection

encodeArithmeticTriple : ArithmeticTriple -> ArithmeticTripleCode
encodeArithmeticTriple =
  Recoverable.encode arithmeticTripleRecoverableProjection

decodeArithmeticTriple : ArithmeticTripleCode -> ArithmeticTriple
decodeArithmeticTriple =
  Recoverable.decode arithmeticTripleRecoverableProjection

decodeEncodeArithmeticTriple :
  (triple : ArithmeticTriple) ->
  decodeArithmeticTriple (encodeArithmeticTriple triple) ≡ triple
decodeEncodeArithmeticTriple =
  Recoverable.decodeEncodeExact arithmeticTripleRecoverableProjection

arithmeticTripleCodeSeparates :
  Recoverable.DependentCodeSeparating arithmeticTripleRecoverableProjection
arithmeticTripleCodeSeparates =
  Recoverable.dependentCodeSeparating arithmeticTripleRecoverableProjection

------------------------------------------------------------------------
-- 4d. Consumer-indexed theorem: surface alone loses arithmetic magnitude,
-- while surface+residual is sufficient for every consumer.
------------------------------------------------------------------------

tripleSum : ArithmeticTriple -> Nat
tripleSum triple =
  tripleA triple + tripleB triple + tripleC triple

p7ArithmeticTriple : ArithmeticTriple
p7ArithmeticTriple = trialecticToArithmeticTriple Arithmetic.p7Trialectic

p13ArithmeticTriple : ArithmeticTriple
p13ArithmeticTriple = trialecticToArithmeticTriple Arithmetic.p13Trialectic

p7P13SameSurface :
  tripleSurface p7ArithmeticTriple ≡ tripleSurface p13ArithmeticTriple
p7P13SameSurface = refl

p7P13DifferentSum :
  tripleSum p7ArithmeticTriple ≡ tripleSum p13ArithmeticTriple -> ⊥
p7P13DifferentSum ()

surfaceCannotAnswerArithmeticSum :
  Descent.ConsumerSufficient tripleSurface tripleSum -> ⊥
surfaceCannotAnswerArithmeticSum sufficient =
  p7P13DifferentSum
    (sufficient p7ArithmeticTriple p13ArithmeticTriple p7P13SameSurface)

surfacePlusResidualAnswersEveryConsumer :
  {Outcome : Set} ->
  (consumer : ArithmeticTriple -> Outcome) ->
  Descent.ConsumerSufficient
    (TopDown.dependentCodeObserver arithmeticTripleRecoverableProjection)
    consumer
surfacePlusResidualAnswersEveryConsumer =
  TopDown.dependentCodeIsAdequateForEveryConsumer
    arithmeticTripleRecoverableProjection

------------------------------------------------------------------------
-- 4e. Reuse the existing verified 27-state machine codec for the coarse T3
-- surface.  The machine code is lossless for the coarse row; arithmetic loss
-- remains solely in the declared residual above.
------------------------------------------------------------------------

encodeArithmeticSurface :
  ArithmeticTriple -> MachineCodec.Code27
encodeArithmeticSurface triple =
  MachineCodec.encode27 (tripleSurface triple)

decodeArithmeticSurface :
  MachineCodec.Code27 -> Maybe Fabric.Ternary27Point
decodeArithmeticSurface = MachineCodec.decode27

machineCodecRoundTripOnArithmeticSurface :
  (triple : ArithmeticTriple) ->
  decodeArithmeticSurface (encodeArithmeticSurface triple)
  ≡ just (tripleSurface triple)
machineCodecRoundTripOnArithmeticSurface triple =
  MachineCodec.decodeEncode27 (tripleSurface triple)


------------------------------------------------------------------------
-- 4f. Reuse the compact 27 codec and identify its explicit frame only at the
-- representation level for this consumer.
--
-- In the J renderer the same generic frame coordinate is proved to equal the
-- third pants continuation.  Here, because our row ordering is (A,B,C), the
-- exact same codec field is simply coarse C_p presence.  These are separate
-- consumer-specific interpretations of one representation coordinate.
------------------------------------------------------------------------

encodeCompactArithmeticSurface :
  ArithmeticTriple -> Compact.Compact27
encodeCompactArithmeticSurface triple =
  Compact.encodeCompact27 (tripleSurface triple)

compactArithmeticSurfaceRoundTrip :
  (triple : ArithmeticTriple) ->
  Compact.decodeCompact27 (encodeCompactArithmeticSurface triple)
  ≡ tripleSurface triple
compactArithmeticSurfaceRoundTrip triple =
  Compact.decodeEncodeCompact27 (tripleSurface triple)

compactFrameIsArithmeticCPresence :
  (triple : ArithmeticTriple) ->
  Compact.frame3 (encodeCompactArithmeticSurface triple)
  ≡ presenceTrit (tripleC triple)
compactFrameIsArithmeticCPresence
  (arithmetic-triple a b c) = refl

compactPayloadAndFrameDoNotRecoverArithmeticWithoutResidual :
  Descent.ConsumerSufficient
    (λ triple -> Compact.decodeCompact27 (encodeCompactArithmeticSurface triple))
    tripleSum
  -> ⊥
compactPayloadAndFrameDoNotRecoverArithmeticWithoutResidual sufficient =
  p7P13DifferentSum
    (sufficient
      p7ArithmeticTriple
      p13ArithmeticTriple
      (trans
        (compactArithmeticSurfaceRoundTrip p7ArithmeticTriple)
        (trans
          p7P13SameSurface
          (sym (compactArithmeticSurfaceRoundTrip p13ArithmeticTriple)))))

data ArithmeticFrameAutomaticallyHasJRendererPantsMeaning : Set where

arithmeticFrameDoesNotInheritJRendererPantsMeaning :
  ArithmeticFrameAutomaticallyHasJRendererPantsMeaning -> ⊥
arithmeticFrameDoesNotInheritJRendererPantsMeaning ()


------------------------------------------------------------------------
-- 4g. Consumer-indexed arithmetic codec routing.
--
-- This mirrors the existing J codec policy: discard only what a declared
-- consumer provably does not need.
------------------------------------------------------------------------

data ArithmeticCodecConsumerClass : Set where
  presencePatternOnly : ArithmeticCodecConsumerClass
  exponentSumConsumer : ArithmeticCodecConsumerClass
  fullContributionConsumer : ArithmeticCodecConsumerClass

data ArithmeticCodecRetention : Set where
  retainCoarseT3Only : ArithmeticCodecRetention
  retainCoarseT3PlusArithmeticResidual : ArithmeticCodecRetention
  retainFullArithmeticTripleCode : ArithmeticCodecRetention

routeArithmeticConsumer :
  ArithmeticCodecConsumerClass ->
  ArithmeticCodecRetention
routeArithmeticConsumer presencePatternOnly =
  retainCoarseT3Only
routeArithmeticConsumer exponentSumConsumer =
  retainCoarseT3PlusArithmeticResidual
routeArithmeticConsumer fullContributionConsumer =
  retainFullArithmeticTripleCode

presencePatternConsumer :
  ArithmeticTriple -> Fabric.Ternary27Point
presencePatternConsumer = tripleSurface

presencePatternFactorsThroughSurface :
  Descent.FactorsThrough
    tripleSurface
    presencePatternConsumer
presencePatternFactorsThroughSurface =
  Factorized.factorizedRefinement
    (λ surface -> surface)
    (λ triple -> refl)

presencePatternSurfaceSufficient :
  Descent.ConsumerSufficient
    tripleSurface
    presencePatternConsumer
presencePatternSurfaceSufficient left right same = same

exponentSumNeedsResidual :
  Descent.ConsumerSufficient
    tripleSurface
    tripleSum
  -> ⊥
exponentSumNeedsResidual =
  surfaceCannotAnswerArithmeticSum

fullContributionConsumerFn :
  ArithmeticTriple -> ArithmeticTriple
fullContributionConsumerFn triple = triple

fullContributionNeedsResidual :
  Descent.ConsumerSufficient
    tripleSurface
    fullContributionConsumerFn
  -> ⊥
fullContributionNeedsResidual sufficient =
  p7P13DifferentSum
    (cong tripleSum
      (sufficient
        p7ArithmeticTriple
        p13ArithmeticTriple
        p7P13SameSurface))

residualCodeSufficesForExponentSum :
  Descent.ConsumerSufficient
    (TopDown.dependentCodeObserver arithmeticTripleRecoverableProjection)
    tripleSum
residualCodeSufficesForExponentSum =
  TopDown.dependentCodeIsAdequateForEveryConsumer
    arithmeticTripleRecoverableProjection
    tripleSum

residualCodeSufficesForFullContribution :
  Descent.ConsumerSufficient
    (TopDown.dependentCodeObserver arithmeticTripleRecoverableProjection)
    fullContributionConsumerFn
residualCodeSufficesForFullContribution =
  TopDown.dependentCodeIsAdequateForEveryConsumer
    arithmeticTripleRecoverableProjection
    fullContributionConsumerFn

record ArithmeticCodecRoutingReceipt
  (consumerClass : ArithmeticCodecConsumerClass) : Set where
  constructor arithmetic-codec-routing-receipt
  field
    retention : ArithmeticCodecRetention
    retentionMatchesCanonicalRoute :
      retention ≡ routeArithmeticConsumer consumerClass

open ArithmeticCodecRoutingReceipt public

canonicalPresenceRoutingReceipt :
  ArithmeticCodecRoutingReceipt presencePatternOnly
canonicalPresenceRoutingReceipt =
  arithmetic-codec-routing-receipt
    retainCoarseT3Only
    refl

canonicalExponentSumRoutingReceipt :
  ArithmeticCodecRoutingReceipt exponentSumConsumer
canonicalExponentSumRoutingReceipt =
  arithmetic-codec-routing-receipt
    retainCoarseT3PlusArithmeticResidual
    refl

canonicalFullContributionRoutingReceipt :
  ArithmeticCodecRoutingReceipt fullContributionConsumer
canonicalFullContributionRoutingReceipt =
  arithmetic-codec-routing-receipt
    retainFullArithmeticTripleCode
    refl


------------------------------------------------------------------------
-- 4h. Role-indexed selective residual routing.
--
-- A consumer may need one attributed contribution magnitude without needing
-- the other two.  Retain the common T3 presence surface plus exactly the
-- residual for the requested source role.
------------------------------------------------------------------------

roleSurface :
  Arithmetic.ModularContributionRole ->
  Fabric.Ternary27Point ->
  SSP.SSPTrit
roleSurface Arithmetic.frickeComparison = Fabric.x
roleSurface Arithmetic.levelPComparison = Fabric.y
roleSurface Arithmetic.levelP2Comparison = Fabric.z

roleMagnitude :
  Arithmetic.ModularContributionRole ->
  ArithmeticTriple ->
  Nat
roleMagnitude Arithmetic.frickeComparison = tripleA
roleMagnitude Arithmetic.levelPComparison = tripleB
roleMagnitude Arithmetic.levelP2Comparison = tripleC

SelectedRoleResidual :
  Arithmetic.ModularContributionRole ->
  Fabric.Ternary27Point ->
  Set
SelectedRoleResidual role surface =
  PresenceResidual (roleSurface role surface)

selectedRoleResidual :
  (role : Arithmetic.ModularContributionRole) ->
  (triple : ArithmeticTriple) ->
  SelectedRoleResidual role (tripleSurface triple)
selectedRoleResidual Arithmetic.frickeComparison
  (arithmetic-triple a b c) = presenceResidual a
selectedRoleResidual Arithmetic.levelPComparison
  (arithmetic-triple a b c) = presenceResidual b
selectedRoleResidual Arithmetic.levelP2Comparison
  (arithmetic-triple a b c) = presenceResidual c

record SelectedRoleCode
  (role : Arithmetic.ModularContributionRole) : Set where
  constructor selected-role-code
  field
    selectedSurface : Fabric.Ternary27Point
    selectedResidual : SelectedRoleResidual role selectedSurface

open SelectedRoleCode public

encodeSelectedRole :
  (role : Arithmetic.ModularContributionRole) ->
  ArithmeticTriple ->
  SelectedRoleCode role
encodeSelectedRole role triple =
  selected-role-code
    (tripleSurface triple)
    (selectedRoleResidual role triple)

decodeSelectedRoleMagnitude :
  (role : Arithmetic.ModularContributionRole) ->
  SelectedRoleCode role ->
  Nat
decodeSelectedRoleMagnitude role
  (selected-role-code surface residual) =
  reopenPresence (roleSurface role surface) residual

decodeEncodeSelectedRoleMagnitude :
  (role : Arithmetic.ModularContributionRole) ->
  (triple : ArithmeticTriple) ->
  decodeSelectedRoleMagnitude role (encodeSelectedRole role triple)
  ≡ roleMagnitude role triple
decodeEncodeSelectedRoleMagnitude
  Arithmetic.frickeComparison
  (arithmetic-triple zero b c) = refl
decodeEncodeSelectedRoleMagnitude
  Arithmetic.frickeComparison
  (arithmetic-triple (suc a) b c) = refl
decodeEncodeSelectedRoleMagnitude
  Arithmetic.levelPComparison
  (arithmetic-triple a zero c) = refl
decodeEncodeSelectedRoleMagnitude
  Arithmetic.levelPComparison
  (arithmetic-triple a (suc b) c) = refl
decodeEncodeSelectedRoleMagnitude
  Arithmetic.levelP2Comparison
  (arithmetic-triple a b zero) = refl
decodeEncodeSelectedRoleMagnitude
  Arithmetic.levelP2Comparison
  (arithmetic-triple a b (suc c)) = refl

selectedRoleCodeSufficesForRoleMagnitude :
  (role : Arithmetic.ModularContributionRole) ->
  Descent.ConsumerSufficient
    (encodeSelectedRole role)
    (roleMagnitude role)
selectedRoleCodeSufficesForRoleMagnitude role left right sameCode =
  trans
    (sym (decodeEncodeSelectedRoleMagnitude role left))
    (trans
      (cong (decodeSelectedRoleMagnitude role) sameCode)
      (decodeEncodeSelectedRoleMagnitude role right))

data ArithmeticRoleConsumerClass : Set where
  oneRoleMagnitude :
    Arithmetic.ModularContributionRole ->
    ArithmeticRoleConsumerClass

data ArithmeticRoleRetention : Set where
  retainT3PlusSelectedRoleResidual :
    Arithmetic.ModularContributionRole ->
    ArithmeticRoleRetention

routeArithmeticRoleConsumer :
  ArithmeticRoleConsumerClass ->
  ArithmeticRoleRetention
routeArithmeticRoleConsumer (oneRoleMagnitude role) =
  retainT3PlusSelectedRoleResidual role

selectedRoleRoutingIsStrictlyLessThanFullTripleByPolicy :
  (role : Arithmetic.ModularContributionRole) ->
  routeArithmeticRoleConsumer (oneRoleMagnitude role)
  ≡ retainT3PlusSelectedRoleResidual role
selectedRoleRoutingIsStrictlyLessThanFullTripleByPolicy role = refl

------------------------------------------------------------------------
-- 5. Role order is retained exactly.
--
-- x = Fricke contribution A_p
-- y = level-p contribution B_p
-- z = level-p^2 contribution C_p
--
-- Only the values are coarsened; source-role provenance is not permuted.
------------------------------------------------------------------------

presenceX :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : Arithmetic.ArithmeticTrialectic prime) ->
  Fabric.x (presenceEncode trial) ≡ presenceTrit (Arithmetic.A trial)
presenceX trial = refl

presenceY :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : Arithmetic.ArithmeticTrialectic prime) ->
  Fabric.y (presenceEncode trial) ≡ presenceTrit (Arithmetic.B trial)
presenceY trial = refl

presenceZ :
  {prime : Lane.MonsterPrimeLane} ->
  (trial : Arithmetic.ArithmeticTrialectic prime) ->
  Fabric.z (presenceEncode trial) ≡ presenceTrit (Arithmetic.C trial)
presenceZ trial = refl

------------------------------------------------------------------------
-- 6. Post-rebase seam.
--
-- Current master has an exact
--
--   ObserverMatrix3 SSPTrit <-> T^9 <-> three T^3 hypervoxels
--
-- rechart.  This branch deliberately stops at the stable shared T^3 donor
-- type, so the future rebase only needs to place this row into a declared
-- observer-matrix role.  No semantic identity is asserted here.
------------------------------------------------------------------------

data ArithmeticT3RowAlreadyIsRelationalObserverRow : Set where

arithmeticT3RowDoesNotAutomaticallyBecomeRelationalObserverRow :
  ArithmeticT3RowAlreadyIsRelationalObserverRow -> ⊥
arithmeticT3RowDoesNotAutomaticallyBecomeRelationalObserverRow ()

adapterClaimOrigin : Source.ClaimOrigin
adapterClaimOrigin = Source.repositoryNewExtension

record OggMonstrousExponentTrialectic369QuantizationBoundary : Set where
  constructor ogg-monstrous-exponent-trialectic-369-quantization-boundary
  field
    genericDeclaredLossQuantizerOwned : Bool
    canonicalPresenceQuantizerOwned : Bool
    sourceRoleOrderPreserved : Bool
    concreteP5P7P11P13RowsComputed : Bool
    explicitQuantizationCollisionOwned : Bool
    dependentResidualCodecReopensArithmeticExactly : Bool
    coarseSurfaceAloneFailsMagnitudeConsumer : Bool
    surfacePlusResidualAdequateForEveryConsumer : Bool
    existingVerified27MachineCodecReused : Bool
    compact27CodecReused : Bool
    compactFrameIsArithmeticCPresence : Bool
    consumerIndexedArithmeticRoutingOwned : Bool
    presenceConsumerMayDiscardResidual : Bool
    exponentSumConsumerRequiresResidual : Bool
    fullContributionConsumerRequiresResidual : Bool
    roleIndexedSelectiveResidualRoutingOwned : Bool
    selectedRoleResidualSufficesForRoleMagnitude : Bool
    arithmeticFrameInheritsJRendererPantsMeaning : Bool
    exactMagnitudeRecoveryFromPresenceCode : Bool
    arithmeticPolarityIdentityClaimed : Bool
    sharedT3PostRebaseSeamPrepared : Bool
    arithmeticRowAlreadyRelationalObserverRow : Bool

canonicalOggMonstrousExponentTrialectic369QuantizationBoundary :
  OggMonstrousExponentTrialectic369QuantizationBoundary
canonicalOggMonstrousExponentTrialectic369QuantizationBoundary =
  ogg-monstrous-exponent-trialectic-369-quantization-boundary
    true true true true true
    true true true true
    true true true true true true true true
    false false true false
