module DASHI.Physics.Closure.NSTriadKNLuoClaimRouteCrosswalkRound24Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Map each claimed-solution mechanism to the first load-bearing lemma it must
-- actually supply on the canonical Clay path.  A source claim never maps
-- directly to the terminal theorem.  It first has to inhabit a physical lemma
-- with the required cutoff-uniformity, sign, scaling and quantifier order.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoClaimedSolutionCorpusRound24Exact as Corpus


data LadderNode : Set where
  L3_fullPeriodicFourierCarrier : LadderNode
  L7_uniformFiveSourceTax : LadderNode
  L8_periodicKernelAndCZ : LadderNode
  L9_incrementDiffusionCoercivity : LadderNode
  L10_farFieldPacking : LadderNode
  L11_commutatorSubgridBound : LadderNode
  L12_hystereticPositiveVariation : LadderNode
  L13_dissipationWavenumberAndLowReservoir : LadderNode
  L15_strictViscosityMargin : LadderNode
  L17_nonCircularGronwall : LadderNode
  L21_restartAndSmoothRecovery : LadderNode

firstLoadBearingNode : Corpus.ClaimFamily → LadderNode
firstLoadBearingNode Corpus.shellModifiedEnergy =
  L15_strictViscosityMargin
firstLoadBearingNode Corpus.finitePacketExhaustion =
  L7_uniformFiveSourceTax
firstLoadBearingNode Corpus.temporalResponseLift =
  L17_nonCircularGronwall
firstLoadBearingNode Corpus.geometricDepletion =
  L8_periodicKernelAndCZ
firstLoadBearingNode Corpus.helicalFluxQuasiTrapping =
  L10_farFieldPacking
firstLoadBearingNode Corpus.filteredVortexDefect =
  L11_commutatorSubgridBound
firstLoadBearingNode Corpus.firstThresholdPackets =
  L12_hystereticPositiveVariation
firstLoadBearingNode Corpus.sparseSupercriticalEnergy =
  L13_dissipationWavenumberAndLowReservoir
firstLoadBearingNode Corpus.highHighResidenceAbsorption =
  L12_hystereticPositiveVariation
firstLoadBearingNode Corpus.emergentVorticityDamping =
  L9_incrementDiffusionCoercivity
firstLoadBearingNode Corpus.strainProjectionCoercivity =
  L9_incrementDiffusionCoercivity
firstLoadBearingNode Corpus.topologicalContinuationExhaustion =
  L21_restartAndSmoothRecovery
firstLoadBearingNode Corpus.universalFrequencyEnvelope =
  L13_dissipationWavenumberAndLowReservoir
firstLoadBearingNode Corpus.finiteCascadeSpeed =
  L10_farFieldPacking
firstLoadBearingNode Corpus.arithmeticVortonCutoff =
  L13_dissipationWavenumberAndLowReservoir
firstLoadBearingNode Corpus.symmetryRestrictedThreshold =
  L3_fullPeriodicFourierCarrier

abuClaimEntersAtStrictMargin :
  firstLoadBearingNode (Corpus.family Corpus.abuGhuwaleh)
  ≡ L15_strictViscosityMargin
abuClaimEntersAtStrictMargin = refl

abuPacketClaimEntersAtUniformFiveSourceTax :
  firstLoadBearingNode (Corpus.family Corpus.abuShellBridge)
  ≡ L7_uniformFiveSourceTax
abuPacketClaimEntersAtUniformFiveSourceTax = refl

camlinClaimEntersAtNonCircularGronwall :
  firstLoadBearingNode (Corpus.family Corpus.camlin)
  ≡ L17_nonCircularGronwall
camlinClaimEntersAtNonCircularGronwall = refl

permanaClaimEntersAtPeriodicKernel :
  firstLoadBearingNode (Corpus.family Corpus.permanaLathifIbrahim)
  ≡ L8_periodicKernelAndCZ
permanaClaimEntersAtPeriodicKernel = refl

shahmurovClaimEntersAtPositiveVariation :
  firstLoadBearingNode (Corpus.family Corpus.shahmurovPartII)
  ≡ L12_hystereticPositiveVariation
shahmurovClaimEntersAtPositiveVariation = refl

riClaimEntersAtDissipationRange :
  firstLoadBearingNode (Corpus.family Corpus.ri)
  ≡ L13_dissipationWavenumberAndLowReservoir
riClaimEntersAtDissipationRange = refl

higginsClaimEntersAtFarFieldPacking :
  firstLoadBearingNode (Corpus.family Corpus.higgins)
  ≡ L10_farFieldPacking
higginsClaimEntersAtFarFieldPacking = refl

aksmanClaimEntersAtDissipationRange :
  firstLoadBearingNode (Corpus.family Corpus.aksman)
  ≡ L13_dissipationWavenumberAndLowReservoir
aksmanClaimEntersAtDissipationRange = refl

cavazziniRestrictedClaimEntersAtFullCarrier :
  firstLoadBearingNode (Corpus.family Corpus.cavazzini)
  ≡ L3_fullPeriodicFourierCarrier
cavazziniRestrictedClaimEntersAtFullCarrier = refl

claimedConclusionIsNeverTerminalEvidenceByItself : Bool
claimedConclusionIsNeverTerminalEvidenceByItself = true
