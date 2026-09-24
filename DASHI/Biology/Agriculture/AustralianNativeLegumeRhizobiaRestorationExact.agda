module DASHI.Biology.Agriculture.AustralianNativeLegumeRhizobiaRestorationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES
import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Chemistry

burdon1999DOI : String
burdon1999DOI = "10.1046/j.1365-2664.1999.00409.x"

thrall2000DOI : String
thrall2000DOI = "10.1046/j.1365-2664.2000.00470.x"

murray2001DOI : String
murray2001DOI = "10.1046/j.1442-8903.2001.00086.x"

thrall2005DOI : String
thrall2005DOI = "10.1111/j.1365-2664.2005.01058.x"

burdonEtAl1999 : Attribution.AttributedSource
burdonEtAl1999 = Attribution.mkDOISource
  "J. J. Burdon; A. H. Gibson; Suzette D. Searle; M. J. Woods; J. Brockwell"
  "Variation in the effectiveness of symbiotic associations between native rhizobia and temperate Australian Acacia: within-species interactions"
  "Journal of Applied Ecology 36(3):398-408"
  "1999" burdon1999DOI "https://doi.org/10.1046/j.1365-2664.1999.00409.x"
  Attribution.academicArticleSource
  "Australian Acacia-rhizobial effectiveness study across many host populations and isolates. Strong host-population and isolate variation is retained; no context-free elite-strain theorem is inferred."
  Attribution.publicAttribution

thrallBurdonWoods2000 : Attribution.AttributedSource
thrallBurdonWoods2000 = Attribution.mkDOISource
  "Peter H. Thrall; J. J. Burdon; Matthew J. Woods"
  "Variation in the effectiveness of symbiotic associations between native rhizobia and temperate Australian legumes: interactions within and between genera"
  "Journal of Applied Ecology 37(1):52-65"
  "2000" thrall2000DOI "https://doi.org/10.1046/j.1365-2664.2000.00470.x"
  Attribution.academicArticleSource
  "Native Australian legume-rhizobial interaction source retaining host population/species and isolate context. Cross-host performance is not promoted to universal compatibility."
  Attribution.publicAttribution

murrayThrallWoods2001 : Attribution.AttributedSource
murrayThrallWoods2001 = Attribution.mkDOISource
  "Brad R. Murray; Peter H. Thrall; Matthew J. Woods"
  "Acacia species and rhizobial interactions: Implications for restoration of native vegetation"
  "Ecological Management & Restoration 2(3):213-219"
  "2001" murray2001DOI "https://doi.org/10.1046/j.1442-8903.2001.00086.x"
  Attribution.academicArticleSource
  "Restoration-oriented synthesis of Australian Acacia-rhizobial specificity/effectiveness. Retained as restoration context, not deployment authority."
  Attribution.publicAttribution

thrallEtAl2005 : Attribution.AttributedSource
thrallEtAl2005 = Attribution.mkDOISource
  "Peter H. Thrall; David A. Millsom; Alison C. Jeavons; Meigan Waayers; Graham Harvey; David J. Bagnall; John Brockwell"
  "Seed inoculation with effective root-nodule bacteria enhances revegetation success"
  "Journal of Applied Ecology 42(4):740-751"
  "2005" thrall2005DOI "https://doi.org/10.1111/j.1365-2664.2005.01058.x"
  Attribution.academicArticleSource
  "South-eastern Australian direct-seeding field trials. Inoculation improved early establishment/growth and often survival, but responses varied by species/site and remain distinct from whole-community recovery."
  Attribution.publicAttribution

data AustralianRhizobiaWorld : Set where
  compatibleEffectiveContext : AustralianRhizobiaWorld
  compatibleIneffectiveContext : AustralianRhizobiaWorld

data SymbiosisTask : Set where
  realisedSymbiosisTask : SymbiosisTask

data StrainToken : Set where
  selectedNativeStrain : StrainToken

strainIdentityOnly : AustralianRhizobiaWorld → StrainToken
strainIdentityOnly _ = selectedNativeStrain

realisedSymbiosis : SymbiosisTask → AustralianRhizobiaWorld → Bool
realisedSymbiosis realisedSymbiosisTask compatibleEffectiveContext = true
realisedSymbiosis realisedSymbiosisTask compatibleIneffectiveContext = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

strainIdentityNotTaskSufficient : LES.TaskFactorisation strainIdentityOnly realisedSymbiosis → ⊥
strainIdentityNotTaskSufficient factor =
  trueNotFalse (LES.sameRepresentationSameTaskOutput factor realisedSymbiosisTask {compatibleEffectiveContext} {compatibleIneffectiveContext} refl)

record AustralianRhizobiaBoundary : Set where
  constructor australian-rhizobia-boundary
  field
    strainIdentityAloneDeterminesEffectiveSymbiosis : Bool
    hostSpeciesPopulationAndSiteMustRemainIndexed : Bool
    inoculationImpliesEffectiveSymbiosis : Bool
    effectiveSymbiosisImpliesEstablishment : Bool
    establishmentImpliesEarlyGrowth : Bool
    inoculationImpliesFieldSurvival : Bool
    earlyGrowthImpliesCommunityRecovery : Bool
    fieldRestorationCreatesUniversalStrainRanking : Bool
    AustralianAcaciaCreatesSenegaliaSameObject : Bool
    restorationResultCreatesDeploymentAuthority : Bool
open AustralianRhizobiaBoundary public

canonicalAustralianRhizobiaBoundary : AustralianRhizobiaBoundary
canonicalAustralianRhizobiaBoundary = australian-rhizobia-boundary
  false true false false false false false false false false

bacterialFluxStillOpen : Chemistry.stageClosed Chemistry.bacterialFixedNFlux ≡ false
bacterialFluxStillOpen = refl

attributionRule : String
attributionRule =
  "Burdon et al. 1999, Thrall/Burdon/Woods 2000, Murray/Thrall/Woods 2001 and Thrall et al. 2005 own their Australian native-legume/rhizobial observations and restoration interpretations. DASHI owns only the typed information-loss witness and no-promotion boundary. Australian Acacia systems are not identified with Senegalia senegal, and inoculation is not promoted through symbiosis, establishment, growth, survival or community recovery without explicit receipts."
