module DASHI.Biology.KitzerowBH4StrictEvidenceBindingExact where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.StrictEvidencePromotionBindingExact as Strict
import DASHI.Biology.KitzerowBH4TransportCarrierProbeExact as Transport
import DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeExact as RouteState

------------------------------------------------------------------------
-- BH4 STRICT EVIDENCE -> CLAIM -> ESTIMAND BINDING
--
-- This is the direct cross-pollination from the autism/vaccine strict-binding
-- lane. Shared subject matter or a shared word such as "BH4", "transport" or
-- "monoamine" cannot pay a new coordinate. Positive promotion requires an
-- exact evidence token plus an exact estimand witness.
------------------------------------------------------------------------

record BH4EvidenceToken : Set where
  constructor bh4-evidence-token
  field
    evidenceKey : String
    sourceOwner : Source.AttributedSource
    evidenceReading : String

open BH4EvidenceToken public

caco2009Evidence : BH4EvidenceToken
caco2009Evidence =
  bh4-evidence-token
    "ohashi-2009-caco-bh4-transcellular"
    Transport.ohashiEtAl2009CacoTransport
    "Quantitative apical-to-basolateral BH4 movement in polarized Caco-2 epithelium; not a neural donor-recipient measurement."

nagatsu1994THEvidence : BH4EvidenceToken
nagatsu1994THEvidence =
  bh4-evidence-token
    "nagatsu-1994-striatal-th-response"
    RouteState.nagatsuEtAl1994TH
    "Peripheral BH4 increases the DOPA-accumulation index of striatal TH activity in the reported mouse experiment."

tph1998Evidence : BH4EvidenceToken
tph1998Evidence =
  bh4-evidence-token
    "1998-striatal-tph-response"
    RouteState.bh4TryptophanHydroxylase1998
    "Peripheral BH4 increases 5-HTP accumulation as an in-vivo TPH-activity index in the reported rat contexts."

koshimura1994RouteEvidence : BH4EvidenceToken
koshimura1994RouteEvidence =
  bh4-evidence-token
    "koshimura-1994-intracellular-extracellular-route"
    RouteState.koshimuraMiwaWatanabe1994Sepiapterin
    "Intracellular BH4 elevation via sepiapterin and extracellular BH4 exposure have distinguishable dopamine-response mechanisms."

record BH4Claim : Set where
  constructor bh4-claim
  field claimKey : String

open BH4Claim public

cacoTranscellularRateClaim : BH4Claim
cacoTranscellularRateClaim = bh4-claim "context-specific non-neural transcellular BH4 rate is measured"

thInVivoResponseClaim : BH4Claim
thInVivoResponseClaim = bh4-claim "BH4 can increase striatal TH activity in the reported in-vivo context"

tphInVivoResponseClaim : BH4Claim
tphInVivoResponseClaim = bh4-claim "BH4 can increase striatal TPH activity in the reported in-vivo context"

routeStateDistinctionClaim : BH4Claim
routeStateDistinctionClaim = bh4-claim "intracellular and extracellular BH4 routes are mechanistically non-equivalent in the reported striatal context"

targetNeuralDonorRecipientFluxClaim : BH4Claim
targetNeuralDonorRecipientFluxClaim = bh4-claim "quantitative donor-derived BH4/BH2 flux into a target neural recipient is measured"

sameObjectSimultaneousAllocationClaim : BH4Claim
sameObjectSimultaneousAllocationClaim = bh4-claim "one target-neural experiment measures causal simultaneous TH/TPH/NOS/AGMO allocation mediated by donor-derived BH4/BH2 transfer"

record BH4Estimand : Set where
  constructor bh4-estimand
  field
    estimandScopeKey : String
    estimandReading : String

open BH4Estimand public

cacoTranscellularEstimand : BH4Estimand
cacoTranscellularEstimand =
  bh4-estimand
    "Caco-2 / apical-100uM-BH4 / basolateral-transfer / pmol-per-hour-per-well"
    "Ohashi-2009 polarized epithelial transcellular BH4 coordinate."

striatalTHEstimand : BH4Estimand
striatalTHEstimand =
  bh4-estimand
    "mouse-striatum / peripheral-6R-BH4 / AADC-inhibited / DOPA-accumulation TH-index"
    "Nagatsu-1994 in-vivo TH-response coordinate."

striatalTPHEstimand : BH4Estimand
striatalTPHEstimand =
  bh4-estimand
    "rat-striatum / peripheral-6R-BH4 / control-and-lesioned-transplant / 5-HTP TPH-index"
    "1998 in-vivo TPH-response coordinate."

striatalRouteStateEstimand : BH4Estimand
striatalRouteStateEstimand =
  bh4-estimand
    "rat-striatum / sepiapterin-intracellular-vs-6R-BH4-extracellular / DOPA-and-DA / TH-NOS-inhibitor-tests"
    "Koshimura-1994 route/state response coordinate."

targetNeuralTransferEstimand : BH4Estimand
targetNeuralTransferEstimand =
  bh4-estimand
    "target-neural donor-labelled BH4/BH2 / donor-to-recipient rate-direction / cell-region-compartment-time"
    "Still-open donor-resolved transfer estimand."

simultaneousAllocationEstimand : BH4Estimand
simultaneousAllocationEstimand =
  bh4-estimand
    "one target-neural system / donor-labelled BH4-BH2 plus NAD(P)H / simultaneous TH-TPH-NOS-AGMO activity-flux / mediation-time"
    "Still-open same-object simultaneous allocation estimand."

data EvidencePaysClaim : BH4EvidenceToken → BH4Claim → Set where
  cacoPaysCacoRate : EvidencePaysClaim caco2009Evidence cacoTranscellularRateClaim
  nagatsuPaysTHResponse : EvidencePaysClaim nagatsu1994THEvidence thInVivoResponseClaim
  tphStudyPaysTPHResponse : EvidencePaysClaim tph1998Evidence tphInVivoResponseClaim
  koshimuraPaysRouteState : EvidencePaysClaim koshimura1994RouteEvidence routeStateDistinctionClaim

data EvidenceMatchesEstimand : BH4EvidenceToken → BH4Estimand → Set where
  cacoMatchesCacoEstimand : EvidenceMatchesEstimand caco2009Evidence cacoTranscellularEstimand
  nagatsuMatchesTHEstimand : EvidenceMatchesEstimand nagatsu1994THEvidence striatalTHEstimand
  tphStudyMatchesTPHEstimand : EvidenceMatchesEstimand tph1998Evidence striatalTPHEstimand
  koshimuraMatchesRouteStateEstimand : EvidenceMatchesEstimand koshimura1994RouteEvidence striatalRouteStateEstimand

cacoStrictBinding :
  Strict.StrictPromotionBinding claimKey evidenceKey estimandScopeKey
    EvidencePaysClaim EvidenceMatchesEstimand
    cacoTranscellularRateClaim caco2009Evidence cacoTranscellularEstimand
cacoStrictBinding =
  Strict.strict-promotion-binding
    "context-specific non-neural transcellular BH4 rate is measured" refl
    "ohashi-2009-caco-bh4-transcellular" refl
    "Caco-2 / apical-100uM-BH4 / basolateral-transfer / pmol-per-hour-per-well" refl
    cacoPaysCacoRate cacoMatchesCacoEstimand
    "Exact quantitative payment remains Caco-2 epithelial; shared BH4 identity cannot transport this rate into a neural donor-recipient estimand."

thStrictBinding :
  Strict.StrictPromotionBinding claimKey evidenceKey estimandScopeKey
    EvidencePaysClaim EvidenceMatchesEstimand
    thInVivoResponseClaim nagatsu1994THEvidence striatalTHEstimand
thStrictBinding =
  Strict.strict-promotion-binding
    "BH4 can increase striatal TH activity in the reported in-vivo context" refl
    "nagatsu-1994-striatal-th-response" refl
    "mouse-striatum / peripheral-6R-BH4 / AADC-inhibited / DOPA-accumulation TH-index" refl
    nagatsuPaysTHResponse nagatsuMatchesTHEstimand
    "Pays the reported TH-response coordinate only; it is not simultaneous TPH/NOS/AGMO allocation evidence."

tphStrictBinding :
  Strict.StrictPromotionBinding claimKey evidenceKey estimandScopeKey
    EvidencePaysClaim EvidenceMatchesEstimand
    tphInVivoResponseClaim tph1998Evidence striatalTPHEstimand
tphStrictBinding =
  Strict.strict-promotion-binding
    "BH4 can increase striatal TPH activity in the reported in-vivo context" refl
    "1998-striatal-tph-response" refl
    "rat-striatum / peripheral-6R-BH4 / control-and-lesioned-transplant / 5-HTP TPH-index" refl
    tphStudyPaysTPHResponse tphStudyMatchesTPHEstimand
    "Pays the reported TPH-response coordinate only; it cannot be fused with the separate TH study into one same-object allocation experiment."

routeStateStrictBinding :
  Strict.StrictPromotionBinding claimKey evidenceKey estimandScopeKey
    EvidencePaysClaim EvidenceMatchesEstimand
    routeStateDistinctionClaim koshimura1994RouteEvidence striatalRouteStateEstimand
routeStateStrictBinding =
  Strict.strict-promotion-binding
    "intracellular and extracellular BH4 routes are mechanistically non-equivalent in the reported striatal context" refl
    "koshimura-1994-intracellular-extracellular-route" refl
    "rat-striatum / sepiapterin-intracellular-vs-6R-BH4-extracellular / DOPA-and-DA / TH-NOS-inhibitor-tests" refl
    koshimuraPaysRouteState koshimuraMatchesRouteStateEstimand
    "Pays route/state non-equivalence in the reported experiment without paying donor-labelled intercellular transfer or whole-network allocation."

-- There are deliberately no EvidencePaysClaim or EvidenceMatchesEstimand
-- constructors for targetNeuralDonorRecipientFluxClaim,
-- sameObjectSimultaneousAllocationClaim, targetNeuralTransferEstimand or
-- simultaneousAllocationEstimand.

data CacoPaysTargetNeuralFluxPermission : Set where
data SeparateBranchStudiesPaySimultaneousAllocationPermission : Set where
data SameClaimLabelErasesEstimandScopePermission : Set where

cacoCannotPayTargetNeuralFlux : CacoPaysTargetNeuralFluxPermission → ⊥
cacoCannotPayTargetNeuralFlux ()

separateBranchStudiesCannotPaySimultaneousAllocation :
  SeparateBranchStudiesPaySimultaneousAllocationPermission → ⊥
separateBranchStudiesCannotPaySimultaneousAllocation ()

sameClaimLabelCannotEraseEstimandScope : SameClaimLabelErasesEstimandScopePermission → ⊥
sameClaimLabelCannotEraseEstimandScope ()

record BH4StrictBindingBoundary : Set where
  constructor bh4-strict-binding-boundary
  field
    cacoRatePaysOnlyCacoEstimand : Bool
    cacoRatePaysOnlyCacoEstimandIsTrue : cacoRatePaysOnlyCacoEstimand ≡ true
    cacoRatePaysTargetNeuralDonorRecipientFlux : Bool
    cacoRatePaysTargetNeuralDonorRecipientFluxIsFalse : cacoRatePaysTargetNeuralDonorRecipientFlux ≡ false
    thResponsePaidInItsEstimand : Bool
    thResponsePaidInItsEstimandIsTrue : thResponsePaidInItsEstimand ≡ true
    tphResponsePaidInItsEstimand : Bool
    tphResponsePaidInItsEstimandIsTrue : tphResponsePaidInItsEstimand ≡ true
    separateBranchStudiesPaySameObjectSimultaneousAllocation : Bool
    separateBranchStudiesPaySameObjectSimultaneousAllocationIsFalse :
      separateBranchStudiesPaySameObjectSimultaneousAllocation ≡ false
    sameClaimLabelErasesEstimandScope : Bool
    sameClaimLabelErasesEstimandScopeIsFalse : sameClaimLabelErasesEstimandScope ≡ false
    strictBindingsCloseWholeAllocator : Bool
    strictBindingsCloseWholeAllocatorIsFalse : strictBindingsCloseWholeAllocator ≡ false

open BH4StrictBindingBoundary public

canonicalBH4StrictBindingBoundary : BH4StrictBindingBoundary
canonicalBH4StrictBindingBoundary =
  bh4-strict-binding-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
