module DASHI.Law.SensibLawLegalCaseBatteryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawSharedWorldConsumerJoinExact as Join
import DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact as Adversarial
import DASHI.Law.SensibLawMaboPabaiExecutableProofSearchExact as MaboPabai

------------------------------------------------------------------------
-- S21 REAL-CASE BATTERY DISCIPLINE
--
-- The battery encodes different search/join behaviours, not desired outcomes.
-- In particular, no specimen manually seeds a substantive Mabo dependency.
------------------------------------------------------------------------

data CaseBattery : Set where
  yindjibarndiYunupingu : CaseBattery
  munkaraTipakalippa : CaseBattery
  pabai : CaseBattery
  murujuga : CaseBattery
  colonisation : CaseBattery

data JoinDiscipline : Set where
  substantiveReuseIfReviewed : JoinDiscipline
  partialOverlapNoCollapse : JoinDiscipline
  structuralAnalogyOnly : JoinDiscipline
  openDiscoveryNoExpectedJoin : JoinDiscipline
  broadMultiSourceSynthesis : JoinDiscipline

joinDiscipline : CaseBattery → JoinDiscipline
joinDiscipline yindjibarndiYunupingu = substantiveReuseIfReviewed
joinDiscipline munkaraTipakalippa = partialOverlapNoCollapse
joinDiscipline pabai = structuralAnalogyOnly
joinDiscipline murujuga = openDiscoveryNoExpectedJoin
joinDiscipline colonisation = broadMultiSourceSynthesis

manuallySeedMaboDependency : CaseBattery → Bool
manuallySeedMaboDependency yindjibarndiYunupingu = false
manuallySeedMaboDependency munkaraTipakalippa = false
manuallySeedMaboDependency pabai = false
manuallySeedMaboDependency murujuga = false
manuallySeedMaboDependency colonisation = false

allBatteryCasesForbidManualMaboSeed :
  (case : CaseBattery) →
  manuallySeedMaboDependency case ≡ false
allBatteryCasesForbidManualMaboSeed yindjibarndiYunupingu = refl
allBatteryCasesForbidManualMaboSeed munkaraTipakalippa = refl
allBatteryCasesForbidManualMaboSeed pabai = refl
allBatteryCasesForbidManualMaboSeed murujuga = refl
allBatteryCasesForbidManualMaboSeed colonisation = refl

------------------------------------------------------------------------
-- Yindjibarndi may begin with an observed Yunupingu citation/submission seed,
-- but that is still only a proposal/navigation coordinate.  It does not
-- establish a Mabo join.
------------------------------------------------------------------------

data YindjibarndiSeed : Set where
  yunupinguCitationSeed : YindjibarndiSeed

yindjibarndiSeedBasis : Join.JoinBasis
yindjibarndiSeedBasis = Join.citation

data YunupinguSeedAutomaticallyMaboJoin : Set where

yunupinguSeedDoesNotCreateMaboJoin :
  YunupinguSeedAutomaticallyMaboJoin → ⊥
yunupinguSeedDoesNotCreateMaboJoin ()

------------------------------------------------------------------------
-- Munkara/Tipakalippa partial overlap must preserve distinct legal elements.
------------------------------------------------------------------------

data NativeTitleAtomPaysOffshorePetroleumElement : Set where
data SharedCountryConceptCollapsesWrongType : Set where

nativeTitleAtomDoesNotPayOffshoreElement :
  NativeTitleAtomPaysOffshorePetroleumElement → ⊥
nativeTitleAtomDoesNotPayOffshoreElement ()

sharedConceptDoesNotCollapseWrongType :
  SharedCountryConceptCollapsesWrongType → ⊥
sharedConceptDoesNotCollapseWrongType ()

------------------------------------------------------------------------
-- Pabai reuses proof-topology transformations, not Mabo substantive doctrine.
------------------------------------------------------------------------

pabaiMaboAnalogyStillNonPromoting :
  MaboPabai.MaboPabaiSearchBoundary.maboAnalogyAutomaticallyTransfersDoctrine
    MaboPabai.canonicalMaboPabaiSearchBoundary
  ≡ false
pabaiMaboAnalogyStillNonPromoting =
  MaboPabai.MaboPabaiSearchBoundary.maboAnalogyAutomaticallyTransfersDoctrineIsFalse
    MaboPabai.canonicalMaboPabaiSearchBoundary

pabaiFacesDefeaterSearch :
  Adversarial.nextRole Adversarial.reopenedCandidate
  ≡ Adversarial.defeaterSearch
pabaiFacesDefeaterSearch =
  Adversarial.reopenedSearchesDefeaterAgain

------------------------------------------------------------------------
-- Murujuga is an anti-sycophancy/open-discovery control: no theorem requires
-- Mabo to occur in its eventual source-driven graph.
------------------------------------------------------------------------

data MurujugaMustIntersectMabo : Set where

murujugaNeedNotIntersectMabo :
  MurujugaMustIntersectMabo → ⊥
murujugaNeedNotIntersectMabo ()

------------------------------------------------------------------------
-- Colonisation is a broad consumer, not a case ontology.
------------------------------------------------------------------------

data ColonisationConsumerEqualsMaboMatter : Set where

colonisationDoesNotCollapseToMabo :
  ColonisationConsumerEqualsMaboMatter → ⊥
colonisationDoesNotCollapseToMabo ()

record LegalCaseBatteryBoundary : Set where
  constructor legalCaseBatteryBoundary
  field
    batteryTestsDifferentJoinBehaviours : Bool
    batteryTestsDifferentJoinBehavioursIsTrue :
      batteryTestsDifferentJoinBehaviours ≡ true

    batteryPreloadsDesiredMaboJoins : Bool
    batteryPreloadsDesiredMaboJoinsIsFalse :
      batteryPreloadsDesiredMaboJoins ≡ false

    yindjibarndiCitationSeedEqualsReviewedJoin : Bool
    yindjibarndiCitationSeedEqualsReviewedJoinIsFalse :
      yindjibarndiCitationSeedEqualsReviewedJoin ≡ false

    munkaraSharedContextPaysUnrelatedStatutoryElement : Bool
    munkaraSharedContextPaysUnrelatedStatutoryElementIsFalse :
      munkaraSharedContextPaysUnrelatedStatutoryElement ≡ false

    pabaiStructuralAnalogyTransfersSubstantiveDoctrine : Bool
    pabaiStructuralAnalogyTransfersSubstantiveDoctrineIsFalse :
      pabaiStructuralAnalogyTransfersSubstantiveDoctrine ≡ false

    murujugaMustDiscoverMabo : Bool
    murujugaMustDiscoverMaboIsFalse :
      murujugaMustDiscoverMabo ≡ false

    colonisationConsumerCollapsesToOneCase : Bool
    colonisationConsumerCollapsesToOneCaseIsFalse :
      colonisationConsumerCollapsesToOneCase ≡ false

open LegalCaseBatteryBoundary public

canonicalLegalCaseBatteryBoundary : LegalCaseBatteryBoundary
canonicalLegalCaseBatteryBoundary =
  legalCaseBatteryBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
