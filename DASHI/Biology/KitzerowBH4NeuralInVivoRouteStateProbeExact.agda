module DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4TransportCarrierProbeExact as Transport

------------------------------------------------------------------------
-- IN-VIVO / EX-VIVO ROUTE-AND-STATE RESPONSE TEST
--
-- This owner tests the stronger claim suggested by the transport/topology pass:
-- increasing total or extracellular BH4 is not equivalent to increasing the
-- intracellular cofactor state of a particular branch. Route, intracellular
-- conversion, enzyme state and physiological context can change the response.
------------------------------------------------------------------------

nakaharaEtAl1988Microdialysis : Source.AttributedSource
nakaharaEtAl1988Microdialysis =
  Source.mkDOISource
    "D. Nakahara; N. Ozaki; N. Kaneda; K. Kiuchi; T. Okada; T. Ohta; T. Nagatsu"
    "Intracerebrally administered (6R)-L-erythro-tetrahydrobiopterin does not affect extracellular levels of dopamine and serotonin metabolites in rat striatum in vivo during measurement by brain micro-dialysis system"
    "Neurochemistry International 12(2):121-124"
    "1988"
    "10.1016/0197-0186(88)90118-0"
    "https://pubmed.ncbi.nlm.nih.gov/20501212/"
    Source.academicArticleSource
    "Primary rat-striatum in-vivo microdialysis study. Intracerebral 6R-BH4 caused very large increases in striatal total biopterin (reported approximately 23-fold in probe-implanted and 93-fold in unoperated striatum) without an apparent change in extracellular dopamine, DOPAC, HVA or 5-HIAA in the measured physiological context. This pays a counterexample to total-tissue-biopterin sufficiency, not a universal null effect of BH4."
    Source.publicAttribution

koshimuraMiwaWatanabe1994Sepiapterin : Source.AttributedSource
koshimuraMiwaWatanabe1994Sepiapterin =
  Source.mkDOISource
    "K. Koshimura; S. Miwa; Y. Watanabe"
    "Dopamine-releasing action of 6R-L-erythro-tetrahydrobiopterin: analysis of its action site using sepiapterin"
    "Journal of Neurochemistry 63(2):649-654"
    "1994"
    "10.1046/j.1471-4159.1994.63020649.x"
    "https://pubmed.ncbi.nlm.nih.gov/7518501/"
    Source.academicArticleSource
    "Primary rat-striatum in-vivo microdialysis study separating intracellular BH4 elevation via sepiapterin from extracellular BH4 exposure. Sepiapterin raised tissue reduced biopterin without raising extracellular reduced biopterin and increased DOPA/DA in a TH-dependent manner. Direct 6R-BH4 also increased DOPA/DA, but most DA-release enhancement persisted after TH inhibition and NOS inhibition, supporting a route-dependent extracellular action distinct from intracellular cofactor action."
    Source.publicAttribution

nagatsuEtAl1994TH : Source.AttributedSource
nagatsuEtAl1994TH =
  Source.mkDOISource
    "T. Nagatsu; D. Nakahara; K. Kobayashi; S. Morita; H. Sawada; T. Mizuguchi; K. Kiuchi"
    "Peripherally administered (6R)-tetrahydrobiopterin increases in vivo tyrosine hydroxylase activity in the striatum measured by microdialysis both in normal mice and in transgenic mice carrying human tyrosine hydroxylase"
    "Neuroscience Letters 182(1):44-46"
    "1994"
    "10.1016/0304-3940(94)90201-1"
    "https://pubmed.ncbi.nlm.nih.gov/7891884/"
    Source.academicArticleSource
    "Primary mouse in-vivo microdialysis study. Peripheral 6R-BH4 increased the DOPA-accumulation index of striatal TH activity by about four-fold in both normal and human-TH-transgenic mice under AADC inhibition. This pays context-specific in-vivo branch activation after peripheral BH4 delivery, not multi-branch allocator closure."
    Source.publicAttribution

bh4TryptophanHydroxylase1998 : Source.AttributedSource
bh4TryptophanHydroxylase1998 =
  Source.mkPubMedSource
    "Peripherally administered tetrahydrobiopterin increases in vivo tryptophan hydroxylase activity in the striatum after transplantation of fetal ventral mesencephalon in six hydroxydopamine lesioned rats"
    "1998"
    "https://pubmed.ncbi.nlm.nih.gov/9754801/"
    Source.academicArticleSource
    "Primary rat in-vivo microdialysis study. Peripheral 6R-BH4 increased 5-HTP accumulation, used as an index of in-vivo tryptophan-hydroxylase activity, in control and lesioned/transplanted striata. It pays a separate branch-response coordinate but is not the same experiment as the TH/NOS measurements and therefore cannot by itself pay simultaneous allocation."
    Source.publicAttribution

canonicalNeuralInVivoRouteStateSources : List Source.AttributedSource
canonicalNeuralInVivoRouteStateSources =
  nakaharaEtAl1988Microdialysis
  ∷ koshimuraMiwaWatanabe1994Sepiapterin
  ∷ nagatsuEtAl1994TH
  ∷ bh4TryptophanHydroxylase1998
  ∷ []

record NeuralRouteStateObservation : Set where
  constructor neuralRouteStateObservation
  field
    key : String
    routeState : String
    measuredOutput : String
    result : String
    sameExperimentMultiBranch : Bool

open NeuralRouteStateObservation public

largeTissueBiopterinNullMonoamineObservation : NeuralRouteStateObservation
largeTissueBiopterinNullMonoamineObservation =
  neuralRouteStateObservation
    "large tissue-biopterin increase without extracellular monoamine-metabolite response"
    "intracerebral 6R-BH4 in physiologically normal rat striatum"
    "dialysate DA/DOPAC/HVA/5-HIAA plus tissue total biopterin"
    "very large tissue biopterin increase with no apparent measured extracellular monoamine/metabolite change"
    false

intracellularCofactorTHObservation : NeuralRouteStateObservation
intracellularCofactorTHObservation =
  neuralRouteStateObservation
    "intracellular BH4 elevation engages TH-dependent DOPA/DA"
    "sepiapterin raises intracellular/tissue reduced biopterin without raising extracellular reduced biopterin"
    "DOPA and dopamine"
    "DOPA/DA increases abolished by TH inhibition, paying intracellular cofactor-dependent TH action"
    false

extracellularBH4NonCofactorDAObservation : NeuralRouteStateObservation
extracellularBH4NonCofactorDAObservation =
  neuralRouteStateObservation
    "extracellular BH4 can evoke DA release independently of TH/NOS cofactor action"
    "direct extracellular/dialytic 6R-BH4 exposure"
    "DOPA and dopamine with TH/NOS inhibitor tests"
    "DOPA response is TH-dependent while most DA-release enhancement persists after TH and NOS inhibition"
    false

peripheralTHActivationObservation : NeuralRouteStateObservation
peripheralTHActivationObservation =
  neuralRouteStateObservation
    "peripheral BH4 activates striatal TH in vivo"
    "systemic 6R-BH4 with AADC inhibition"
    "DOPA accumulation index of TH activity"
    "about four-fold increase in the reported mouse experiment"
    false

peripheralTPHActivationObservation : NeuralRouteStateObservation
peripheralTPHActivationObservation =
  neuralRouteStateObservation
    "peripheral BH4 activates striatal TPH in vivo"
    "systemic 6R-BH4 in control and lesioned/transplanted rats"
    "5-HTP accumulation index of TPH activity"
    "increased 5-HTP accumulation in the reported contexts"
    false

canonicalNeuralRouteStateObservations : List NeuralRouteStateObservation
canonicalNeuralRouteStateObservations =
  largeTissueBiopterinNullMonoamineObservation
  ∷ intracellularCofactorTHObservation
  ∷ extracellularBH4NonCofactorDAObservation
  ∷ peripheralTHActivationObservation
  ∷ peripheralTPHActivationObservation
  ∷ []

record NeuralRouteStateBoundary : Set where
  constructor neuralRouteStateBoundary
  field
    totalTissueBiopterinSufficesForMonoamineOutput : Bool
    totalTissueBiopterinSufficesForMonoamineOutputIsFalse : totalTissueBiopterinSufficesForMonoamineOutput ≡ false
    intracellularAndExtracellularBH4AreMechanisticallyEquivalent : Bool
    intracellularAndExtracellularBH4AreMechanisticallyEquivalentIsFalse :
      intracellularAndExtracellularBH4AreMechanisticallyEquivalent ≡ false
    peripheralBH4CanActivateTHInVivo : Bool
    peripheralBH4CanActivateTHInVivoIsTrue : peripheralBH4CanActivateTHInVivo ≡ true
    peripheralBH4CanActivateTPHInVivo : Bool
    peripheralBH4CanActivateTPHInVivoIsTrue : peripheralBH4CanActivateTPHInVivo ≡ true
    sameObjectSimultaneousMultiBranchAllocationPaid : Bool
    sameObjectSimultaneousMultiBranchAllocationPaidIsFalse : sameObjectSimultaneousMultiBranchAllocationPaid ≡ false
    routeStateEvidenceClosesWholeAllocator : Bool
    routeStateEvidenceClosesWholeAllocatorIsFalse : routeStateEvidenceClosesWholeAllocator ≡ false

open NeuralRouteStateBoundary public

canonicalNeuralRouteStateBoundary : NeuralRouteStateBoundary
canonicalNeuralRouteStateBoundary =
  neuralRouteStateBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl

record RouteStateBackprop : Set where
  constructor routeStateBackprop
  field
    transportUpgrade : Transport.TransportTopologyUpgrade
    eliminatedCoarseModel : String
    survivingAllocatorRequirement : String
    residualExperiment : String

open RouteStateBackprop public

canonicalRouteStateBackprop : RouteStateBackprop
canonicalRouteStateBackprop =
  routeStateBackprop
    Transport.canonicalTransportTopologyUpgrade
    "eliminate any model in which total tissue BH4 or generic extracellular BH4 exposure uniquely determines monoamine output independent of route, intracellular conversion, enzyme state and physiological context"
    "an adaptive allocator must predict branch response as a function of intracellular/extracellular route, redox form, transporter context, enzyme abundance/activity and regional/developmental state rather than total BH4 alone"
    "perform one donor-traceable target-neural perturbation with simultaneous BH4/BH2 transfer, NAD(P)H/redox, TH/TPH/NOS/AGMO branch flux/activity and enzyme-state readouts so route-state mediation can be distinguished from parallel extracellular/redox effects"
