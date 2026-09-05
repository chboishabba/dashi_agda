module DASHI.Biology.JasonThomasSignallingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.FiniteObservationClosureBidiExact as Closure

-- Koch et al. 2018 ACS Chem Biol DOI 10.1021/acschembio.7b01060;
-- Dowdle et al. 2014 Nature Cell Biology DOI 10.1038/ncb3053.

data SignallingReadout : Set where IRF3NuclearTranslocation NFkBNuclearTranslocation downstreamActivation : SignallingReadout

data Perturbation : Set where STINGAgonist candidateAntagonist PIKIII VPS34Loss : Perturbation

data AutophagyObject : Set where LC3 NCOA4 ferritin ironPool : AutophagyObject

record ThomasMechanismBoundary : Set where
  constructor thomas-mechanism-boundary
  field
    nuclearTranslocationAutomaticallyMeansDownstreamActivation : Bool
    nuclearTranslocationAutomaticallyMeansDownstreamActivationIsFalse : nuclearTranslocationAutomaticallyMeansDownstreamActivation ≡ false
    screenHitAutomaticallyIdentifiesDirectTarget : Bool
    screenHitAutomaticallyIdentifiesDirectTargetIsFalse : screenHitAutomaticallyIdentifiesDirectTarget ≡ false
    VPS34InhibitionStabilisesAutophagySubstrates : Bool
    VPS34InhibitionStabilisesAutophagySubstratesIsTrue : VPS34InhibitionStabilisesAutophagySubstrates ≡ true
    NCOA4TargetsFerritinToAutolysosomalDegradation : Bool
    NCOA4TargetsFerritinToAutolysosomalDegradationIsTrue : NCOA4TargetsFerritinToAutolysosomalDegradation ≡ true

canonicalThomasMechanismBoundary : ThomasMechanismBoundary
canonicalThomasMechanismBoundary = thomas-mechanism-boundary false refl false refl true refl true refl

thomasScreenReverse : Closure.ReverseClosureObligation
thomasScreenReverse = Closure.reverse-closure-obligation
  "macrophage high-content signalling screen"
  "IRF3/NFkB cytoplasm-to-nucleus translocation"
  "secondary pathway assay plus target-deconvolution / chemical-proteomics receipt"
  "mechanistic regulator hypothesis"
  "direct binding target or therapeutic efficacy by itself"

ferritinophagyReverse : Closure.ReverseClosureObligation
ferritinophagyReverse = Closure.reverse-closure-obligation
  "VPS34/autophagy/ferritinophagy"
  "NCOA4 accumulation and ferritin trafficking under autophagy perturbation"
  "binding/localisation/genetic-loss producer chain"
  "selective ferritinophagy mechanism"
  "all iron-homeostasis behaviour in every context"
