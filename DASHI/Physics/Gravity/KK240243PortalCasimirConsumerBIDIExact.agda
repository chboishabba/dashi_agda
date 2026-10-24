module DASHI.Physics.Gravity.KK240243PortalCasimirConsumerBIDIExact where

------------------------------------------------------------------------
-- TOE x 240/243 x QED-QCD-Casimir x Higgs-portal BIDI
--
-- The same numeral 240 occurs in:
--   (a) classical E8 norm-two root cardinality,
--   (b) ideal conducting-plate pressure denominator,
--   (c) selected KK QCD stationary-source defect (approximate).
-- All three have DIFFERENT quantities, operators, boundary regimes.
-- This finite module proves the number alone cannot answer which
-- consumer is intended. It does not prove any 5D QFT theorem.
--
-- Prior owners: PR #1094 T5E8RelativeComplementCandidateExact
--              (243=3+240; NO E8 recognition);
--              CasimirCoefficient720To240CompilerExact
--              (plate arithmetic, NOT 5D circle stress);
--              DarkSector.GaugeSingletPortal (permitted interaction);
--              canonical ClaimTransport/ConsumerDescent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_∸_)

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Physics.QuantumVacuum.CasimirCoefficient720To240CompilerExact as Plate
import DASHI.Physics.DarkSector.GaugeSingletPortal as Portal

data TwoFortyRole : Set where
  classicalE8RootCount : TwoFortyRole
  idealPlatePressureDenominator : TwoFortyRole
  selectedKKStationarityMagnitude : TwoFortyRole

-- The physical values of the KK defect vary continuously with quark mass:
-- only the selected massless-limit integer coefficient is represented here.
numeralOnly : TwoFortyRole → Nat
numeralOnly classicalE8RootCount = 240
numeralOnly idealPlatePressureDenominator = 240
numeralOnly selectedKKStationarityMagnitude = 240

physicalRoleConsumer : TwoFortyRole → TwoFortyRole
physicalRoleConsumer role = role

e8RoleNotPlateRole :
  classicalE8RootCount ≡ idealPlatePressureDenominator → ⊥
e8RoleNotPlateRole ()

plateRoleNotKKRole :
  idealPlatePressureDenominator ≡ selectedKKStationarityMagnitude → ⊥
plateRoleNotKKRole ()

sameNumberDoesNotRecoverPhysicalRole :
  Transport.ClaimNonTransportWitness numeralOnly physicalRoleConsumer
sameNumberDoesNotRecoverPhysicalRole =
  Descent.consumerNonDescentWitness
    classicalE8RootCount idealPlatePressureDenominator
    refl e8RoleNotPlateRole

noBIDIClaimFromBare240 :
  Transport.ClaimTransport numeralOnly physicalRoleConsumer → ⊥
noBIDIClaimFromBare240 =
  Transport.claimNonTransportWitnessBlocksTransport
    sameNumberDoesNotRecoverPhysicalRole

threeDiagonalPlusNonDiagonal : 3 + 240 ≡ 243
threeDiagonalPlusNonDiagonal = refl

fiveDimensionalCasimirCount : 5 * 48 ≡ 240
fiveDimensionalCasimirCount = refl

plateDerivativeArithmetic : 3 * 240 ≡ 720
plateDerivativeArithmetic = Plate.threeTimes240Is720

qcdGluonUnits : Nat
qcdGluonUnits = 8 * 3

qcdDiracQuarkUnits : Nat
qcdDiracQuarkUnits = 6 * 3 * 4

selectedQCDNetUnits : Nat
selectedQCDNetUnits = qcdDiracQuarkUnits ∸ qcdGluonUnits

qcdNetExactlyFortyEight : selectedQCDNetUnits ≡ 48
qcdNetExactlyFortyEight = refl

singleRealScalarBoundArithmetic : 1 * 5 ≡ 5
singleRealScalarBoundArithmetic = refl

oneComplexScalarCountArithmetic : 2 * 5 ≡ 10
oneComplexScalarCountArithmetic = refl

fortySevenInsufficientUnits : 47 * 5 ≡ 235
fortySevenInsufficientUnits = refl

fortyEightMaximumUnits : 48 * 5 ≡ 240
fortyEightMaximumUnits = refl

-- 'Portal allowed' is NOT 'portal coupling, mass, KK determinant
-- and same-action 5D stress paid'. Analytic h(z)<=1 for a periodic
-- free massive real scalar is tested in the accompanying executable,
-- not formalised by these natural-number equations.
quadraticPortalPermitted :
  Portal.portalAllowed Portal.canonicalQuadraticHiggsPortal ≡ true
quadraticPortalPermitted = Portal.quadraticHiggsPortalIsAllowed

-- Supplying the missing physical role recovers it for the *finite*
-- question. No E8/KK/plate same-object equivalence is inferred.
roleTaggedObservation : TwoFortyRole → Nat × TwoFortyRole
roleTaggedObservation role = numeralOnly role , role

roleConsumerFactorsThroughTaggedObservation :
  Transport.ClaimTransport roleTaggedObservation physicalRoleConsumer
roleConsumerFactorsThroughTaggedObservation =
  Transport.claimTransport proj₂ (λ role → refl)

repairMustDistinguishE8AndPlate :
  (refine : TwoFortyRole → Bool) →
  Repair.RefinementRepairs numeralOnly refine physicalRoleConsumer →
  refine classicalE8RootCount ≡ refine idealPlatePressureDenominator → ⊥
repairMustDistinguishE8AndPlate refine adequate same =
  Repair.refinementRepairSeparatesWitness
    sameNumberDoesNotRecoverPhysicalRole adequate same
