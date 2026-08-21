module DASHI.Governance.HyperformalTernaryCarrierEquivalenceExact where

------------------------------------------------------------------------
-- HYPERFORMAL TERNARY CARRIER EQUIVALENCE
--
-- Thin composition of existing theorem owners:
--   EpistemicTrit^9 --(declared neutral-unresolved policy)--> SSPTrit^9
--   SSPTrit^9 <-> DialecticMotifKernel.State9
--   SSPTrit^9 <-> Base369 OneRoundInteractionState
-- while Monster/Ogg arithmetic maps into the same SSPTrit carrier only by the
-- existing lossy residue projection.  Shared carrier geometry is not semantic
-- identity or cross-domain authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Aggregate
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Governance.EpistemicTritBalancedTernarySeparationExact as Separation
import DASHI.Moonshine.MonsterOggNonarySSPTritBridgeExact as Monster
import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Reasoning.DialecticMotifKernel as Dialectic

balancedDigitToSSP : BT.BalancedDigit → SSP.SSPTrit
balancedDigitToSSP BT.neg = SSP.sspNegOne
balancedDigitToSSP BT.zeroDigit = SSP.sspZero
balancedDigitToSSP BT.pos = SSP.sspPosOne

sspToBalancedDigit : SSP.SSPTrit → BT.BalancedDigit
sspToBalancedDigit SSP.sspNegOne = BT.neg
sspToBalancedDigit SSP.sspZero = BT.zeroDigit
sspToBalancedDigit SSP.sspPosOne = BT.pos

balancedSSPRoundTrip :
  (digit : BT.BalancedDigit) →
  sspToBalancedDigit (balancedDigitToSSP digit) ≡ digit
balancedSSPRoundTrip BT.neg = refl
balancedSSPRoundTrip BT.zeroDigit = refl
balancedSSPRoundTrip BT.pos = refl

sspBalancedRoundTrip :
  (trit : SSP.SSPTrit) →
  balancedDigitToSSP (sspToBalancedDigit trit) ≡ trit
sspBalancedRoundTrip SSP.sspNegOne = refl
sspBalancedRoundTrip SSP.sspZero = refl
sspBalancedRoundTrip SSP.sspPosOne = refl

epistemicToSSP : Epistemic.EpistemicTrit → SSP.SSPTrit
epistemicToSSP state =
  balancedDigitToSSP
    (Separation.encodeWithPolicy Separation.neutralUnresolvedPolicy state)

sspToEpistemic : SSP.SSPTrit → Epistemic.EpistemicTrit
sspToEpistemic SSP.sspNegOne = Epistemic.contradicted
sspToEpistemic SSP.sspZero = Epistemic.unresolved
sspToEpistemic SSP.sspPosOne = Epistemic.supported

epistemicSSPRoundTrip :
  (state : Epistemic.EpistemicTrit) →
  sspToEpistemic (epistemicToSSP state) ≡ state
epistemicSSPRoundTrip Epistemic.contradicted = refl
epistemicSSPRoundTrip Epistemic.unresolved = refl
epistemicSSPRoundTrip Epistemic.supported = refl

sspEpistemicRoundTrip :
  (trit : SSP.SSPTrit) →
  epistemicToSSP (sspToEpistemic trit) ≡ trit
sspEpistemicRoundTrip SSP.sspNegOne = refl
sspEpistemicRoundTrip SSP.sspZero = refl
sspEpistemicRoundTrip SSP.sspPosOne = refl

record Epistemic9 : Set where
  constructor epistemic9
  field
    e1 e2 e3 e4 e5 e6 e7 e8 e9 : Epistemic.EpistemicTrit

open Epistemic9 public

epistemic9ToNineTrits : Epistemic9 → Aggregate.NineTrits
epistemic9ToNineTrits (epistemic9 a b c d e f g h i) =
  Aggregate.nineTrits
    (epistemicToSSP a) (epistemicToSSP b) (epistemicToSSP c)
    (epistemicToSSP d) (epistemicToSSP e) (epistemicToSSP f)
    (epistemicToSSP g) (epistemicToSSP h) (epistemicToSSP i)

nineTritsToEpistemic9 : Aggregate.NineTrits → Epistemic9
nineTritsToEpistemic9
  (Aggregate.nineTrits a b c d e f g h i) =
  epistemic9
    (sspToEpistemic a) (sspToEpistemic b) (sspToEpistemic c)
    (sspToEpistemic d) (sspToEpistemic e) (sspToEpistemic f)
    (sspToEpistemic g) (sspToEpistemic h) (sspToEpistemic i)

epistemic9RoundTrip :
  (state : Epistemic9) →
  nineTritsToEpistemic9 (epistemic9ToNineTrits state) ≡ state
epistemic9RoundTrip (epistemic9 a b c d e f g h i)
  rewrite epistemicSSPRoundTrip a
        | epistemicSSPRoundTrip b
        | epistemicSSPRoundTrip c
        | epistemicSSPRoundTrip d
        | epistemicSSPRoundTrip e
        | epistemicSSPRoundTrip f
        | epistemicSSPRoundTrip g
        | epistemicSSPRoundTrip h
        | epistemicSSPRoundTrip i = refl

nineTritsEpistemic9RoundTrip :
  (state : Aggregate.NineTrits) →
  epistemic9ToNineTrits (nineTritsToEpistemic9 state) ≡ state
nineTritsEpistemic9RoundTrip
  (Aggregate.nineTrits a b c d e f g h i)
  rewrite sspEpistemicRoundTrip a
        | sspEpistemicRoundTrip b
        | sspEpistemicRoundTrip c
        | sspEpistemicRoundTrip d
        | sspEpistemicRoundTrip e
        | sspEpistemicRoundTrip f
        | sspEpistemicRoundTrip g
        | sspEpistemicRoundTrip h
        | sspEpistemicRoundTrip i = refl

dialecticToNineTrits : Dialectic.State9 → Aggregate.NineTrits
dialecticToNineTrits
  (Dialectic.state9 a b c d e f g h i) =
  Aggregate.nineTrits
    (SSP.fromTrit a) (SSP.fromTrit b) (SSP.fromTrit c)
    (SSP.fromTrit d) (SSP.fromTrit e) (SSP.fromTrit f)
    (SSP.fromTrit g) (SSP.fromTrit h) (SSP.fromTrit i)

nineTritsToDialectic : Aggregate.NineTrits → Dialectic.State9
nineTritsToDialectic
  (Aggregate.nineTrits a b c d e f g h i) =
  Dialectic.state9
    (SSP.toTrit a) (SSP.toTrit b) (SSP.toTrit c)
    (SSP.toTrit d) (SSP.toTrit e) (SSP.toTrit f)
    (SSP.toTrit g) (SSP.toTrit h) (SSP.toTrit i)

dialecticNineRoundTrip :
  (state : Dialectic.State9) →
  nineTritsToDialectic (dialecticToNineTrits state) ≡ state
dialecticNineRoundTrip
  (Dialectic.state9 a b c d e f g h i)
  rewrite SSP.toTrit-fromTrit a
        | SSP.toTrit-fromTrit b
        | SSP.toTrit-fromTrit c
        | SSP.toTrit-fromTrit d
        | SSP.toTrit-fromTrit e
        | SSP.toTrit-fromTrit f
        | SSP.toTrit-fromTrit g
        | SSP.toTrit-fromTrit h
        | SSP.toTrit-fromTrit i = refl

nineDialecticRoundTrip :
  (state : Aggregate.NineTrits) →
  dialecticToNineTrits (nineTritsToDialectic state) ≡ state
nineDialecticRoundTrip
  (Aggregate.nineTrits a b c d e f g h i)
  rewrite SSP.fromTrit-toTrit a
        | SSP.fromTrit-toTrit b
        | SSP.fromTrit-toTrit c
        | SSP.fromTrit-toTrit d
        | SSP.fromTrit-toTrit e
        | SSP.fromTrit-toTrit f
        | SSP.fromTrit-toTrit g
        | SSP.fromTrit-toTrit h
        | SSP.fromTrit-toTrit i = refl

base369ToDialectic : Cube.OneRoundInteractionState → Dialectic.State9
base369ToDialectic state =
  nineTritsToDialectic (Aggregate.flattenRound state)

dialecticToBase369 : Dialectic.State9 → Cube.OneRoundInteractionState
dialecticToBase369 state =
  Aggregate.rebuildRound (dialecticToNineTrits state)

base369DialecticRoundTrip :
  (state : Cube.OneRoundInteractionState) →
  dialecticToBase369 (base369ToDialectic state) ≡ state
base369DialecticRoundTrip state
  rewrite nineDialecticRoundTrip (Aggregate.flattenRound state)
        | Aggregate.rebuildFlattenRoundTrip state = refl

dialecticBase369RoundTrip :
  (state : Dialectic.State9) →
  base369ToDialectic (dialecticToBase369 state) ≡ state
dialecticBase369RoundTrip state
  rewrite Aggregate.flattenRebuildRoundTrip (dialecticToNineTrits state)
        | dialecticNineRoundTrip state = refl

epistemic9ToBase369 : Epistemic9 → Cube.OneRoundInteractionState
epistemic9ToBase369 state =
  Aggregate.rebuildRound (epistemic9ToNineTrits state)

base369ToEpistemic9 : Cube.OneRoundInteractionState → Epistemic9
base369ToEpistemic9 state =
  nineTritsToEpistemic9 (Aggregate.flattenRound state)

epistemic9Base369RoundTrip :
  (state : Epistemic9) →
  base369ToEpistemic9 (epistemic9ToBase369 state) ≡ state
epistemic9Base369RoundTrip state
  rewrite Aggregate.flattenRebuildRoundTrip (epistemic9ToNineTrits state)
        | epistemic9RoundTrip state = refl

base369Epistemic9RoundTrip :
  (state : Cube.OneRoundInteractionState) →
  epistemic9ToBase369 (base369ToEpistemic9 state) ≡ state
base369Epistemic9RoundTrip state
  rewrite nineTritsEpistemic9RoundTrip (Aggregate.flattenRound state)
        | Aggregate.rebuildFlattenRoundTrip state = refl

monsterOggToCommonTrit : Lane.MonsterPrimeLane → SSP.SSPTrit
monsterOggToCommonTrit = Monster.oggPrimeResidueTrit

monsterThreeMapsToCommonNeutral :
  monsterOggToCommonTrit Lane.p3 ≡ SSP.sspZero
monsterThreeMapsToCommonNeutral = Monster.threeResidueTritNeutral

record HyperformalTernaryCarrierBoundary : Set where
  constructor hyperformalTernaryCarrierBoundary
  field
    epistemicNineEquivalentUnderDeclaredPolicy : Bool
    dialecticStateNineEquivalentToSSPNine : Bool
    base369RoundEquivalentToSSPNine : Bool
    unresolvedDefinitionallyMeansBalancedZero : Bool
    monsterProjectionIsDeclaredCarrierEquivalence : Bool
    sharedCarrierCreatesSemanticIdentity : Bool
    sharedCarrierCreatesCrossDomainAuthority : Bool

canonicalHyperformalTernaryCarrierBoundary : HyperformalTernaryCarrierBoundary
canonicalHyperformalTernaryCarrierBoundary =
  hyperformalTernaryCarrierBoundary
    true true true false false false false
