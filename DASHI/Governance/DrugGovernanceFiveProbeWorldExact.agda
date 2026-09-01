module DASHI.Governance.DrugGovernanceFiveProbeWorldExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.DrugCategoryCostedQuotientDiscriminatorExact as Costed
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Authority
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power

------------------------------------------------------------------------
-- FIVE-PROBE WORLD
--
-- Enlarges the small clinical quotient fixture so every previously candidate
-- probe has a real observer collision and a proof-bearing separator.
-- Synthetic finite states express geometry only; they do not assert empirical
-- disparity magnitudes or historical causes.
------------------------------------------------------------------------

data TherapeuticSurface : Set where
  samePositivePsychedelicLegibility : TherapeuticSurface

data SubjectPosition : Set where
  representedSubject originatingSubject : SubjectPosition

data HistoricalPosition : Set where
  erasedCriminalisationHistory retainedCriminalisationHistory : HistoricalPosition

data AuthorityPosition : Set where
  externallyImposedAuthority affectedSubjectAuthority : AuthorityPosition

data MaterialRoute : Set where
  concentratedCommercialBenefit sharedOrCommunityBenefit : MaterialRoute

data SovereigntyPosition : Set where
  externalObserverSovereignty originatingSovereignStanding : SovereigntyPosition

record ProbeWorld : Set where
  constructor probeWorld
  field
    therapeuticSurface : TherapeuticSurface
    subjectPosition : SubjectPosition
    historicalPosition : HistoricalPosition
    authorityPosition : AuthorityPosition
    materialRoute : MaterialRoute
    sovereigntyPosition : SovereigntyPosition

open ProbeWorld public

baseExternalWorld : ProbeWorld
baseExternalWorld = probeWorld
  samePositivePsychedelicLegibility
  representedSubject
  erasedCriminalisationHistory
  externallyImposedAuthority
  concentratedCommercialBenefit
  externalObserverSovereignty

subjectAuthoredWorld : ProbeWorld
subjectAuthoredWorld = probeWorld
  samePositivePsychedelicLegibility
  originatingSubject
  erasedCriminalisationHistory
  externallyImposedAuthority
  concentratedCommercialBenefit
  externalObserverSovereignty

historyRetainedWorld : ProbeWorld
historyRetainedWorld = probeWorld
  samePositivePsychedelicLegibility
  representedSubject
  retainedCriminalisationHistory
  externallyImposedAuthority
  concentratedCommercialBenefit
  externalObserverSovereignty

authorityRechartedWorld : ProbeWorld
authorityRechartedWorld = probeWorld
  samePositivePsychedelicLegibility
  representedSubject
  erasedCriminalisationHistory
  affectedSubjectAuthority
  concentratedCommercialBenefit
  externalObserverSovereignty

sharedBenefitWorld : ProbeWorld
sharedBenefitWorld = probeWorld
  samePositivePsychedelicLegibility
  representedSubject
  erasedCriminalisationHistory
  externallyImposedAuthority
  sharedOrCommunityBenefit
  externalObserverSovereignty

sovereignWorld : ProbeWorld
sovereignWorld = probeWorld
  samePositivePsychedelicLegibility
  representedSubject
  erasedCriminalisationHistory
  externallyImposedAuthority
  concentratedCommercialBenefit
  originatingSovereignStanding

coarseObserver : ProbeWorld → TherapeuticSurface
coarseObserver = therapeuticSurface

baseSubjectCollapse : coarseObserver baseExternalWorld ≡ coarseObserver subjectAuthoredWorld
baseSubjectCollapse = refl
baseHistoryCollapse : coarseObserver baseExternalWorld ≡ coarseObserver historyRetainedWorld
baseHistoryCollapse = refl
baseAuthorityCollapse : coarseObserver baseExternalWorld ≡ coarseObserver authorityRechartedWorld
baseAuthorityCollapse = refl
baseMaterialCollapse : coarseObserver baseExternalWorld ≡ coarseObserver sharedBenefitWorld
baseMaterialCollapse = refl
baseSovereigntyCollapse : coarseObserver baseExternalWorld ≡ coarseObserver sovereignWorld
baseSovereigntyCollapse = refl

------------------------------------------------------------------------
-- One typed observation bundle per live coordinate.
------------------------------------------------------------------------

subjectBundle : Discriminator.ExperimentBundle ProbeWorld
subjectBundle = Discriminator.experimentBundle
  SubjectPosition subjectPosition (Costed.probeCost Costed.subjectProbe)
  "subject-position probe over positive psychedelic legibility"
  "requires originating/represented subject-position coding"

historyBundle : Discriminator.ExperimentBundle ProbeWorld
historyBundle = Discriminator.experimentBundle
  HistoricalPosition historicalPosition (Costed.probeCost Costed.historyProbe)
  "historical-residue probe over positive psychedelic legibility"
  "requires classifier/criminalisation-history provenance"

authorityBundle : Discriminator.ExperimentBundle ProbeWorld
authorityBundle = Discriminator.experimentBundle
  AuthorityPosition authorityPosition (Costed.probeCost Costed.authorityProbe)
  "classification-authority issuer/standing probe"
  "must distinguish imposed authority from affected-subject category authority"

materialBundle : Discriminator.ExperimentBundle ProbeWorld
materialBundle = Discriminator.experimentBundle
  MaterialRoute materialRoute (Costed.probeCost Costed.materialBenefitProbe)
  "material benefit/externality routing probe"
  "must trace who captures material gain and who bears externalities"

sovereigntyBundle : Discriminator.ExperimentBundle ProbeWorld
sovereigntyBundle = Discriminator.experimentBundle
  SovereigntyPosition sovereigntyPosition (Costed.probeCost Costed.sovereigntyProbe)
  "sovereignty/permission probe"
  "must use community-governed authority evidence rather than external publication alone"

subjectSeparates : Discriminator.BundleSeparates subjectBundle baseExternalWorld subjectAuthoredWorld
subjectSeparates = Discriminator.bundleSeparates (λ ())

historySeparates : Discriminator.BundleSeparates historyBundle baseExternalWorld historyRetainedWorld
historySeparates = Discriminator.bundleSeparates (λ ())

authoritySeparates : Discriminator.BundleSeparates authorityBundle baseExternalWorld authorityRechartedWorld
authoritySeparates = Discriminator.bundleSeparates (λ ())

materialSeparates : Discriminator.BundleSeparates materialBundle baseExternalWorld sharedBenefitWorld
materialSeparates = Discriminator.bundleSeparates (λ ())

sovereigntySeparates : Discriminator.BundleSeparates sovereigntyBundle baseExternalWorld sovereignWorld
sovereigntySeparates = Discriminator.bundleSeparates (λ ())

------------------------------------------------------------------------
-- The common positive surface cannot recover any of the five fine coordinates.
------------------------------------------------------------------------

coarseCannotRecoverAuthority : INF.FactorsThrough coarseObserver authorityPosition → ⊥
coarseCannotRecoverAuthority = INF.witnessRulesOutEveryFlatFactorisation
  (INF.nonFactorabilityWitness baseExternalWorld authorityRechartedWorld refl (λ ()))

coarseCannotRecoverMaterial : INF.FactorsThrough coarseObserver materialRoute → ⊥
coarseCannotRecoverMaterial = INF.witnessRulesOutEveryFlatFactorisation
  (INF.nonFactorabilityWitness baseExternalWorld sharedBenefitWorld refl (λ ()))

coarseCannotRecoverSovereignty : INF.FactorsThrough coarseObserver sovereigntyPosition → ⊥
coarseCannotRecoverSovereignty = INF.witnessRulesOutEveryFlatFactorisation
  (INF.nonFactorabilityWitness baseExternalWorld sovereignWorld refl (λ ()))

------------------------------------------------------------------------
-- Cross-pollinated boundaries from the wider governance stack.
------------------------------------------------------------------------

authorityBoundary : Authority.FeministDrugClassificationAuthorityBoundary
authorityBoundary = Authority.canonicalFeministDrugClassificationAuthorityBoundary

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

record FiveProbeWorldBoundary : Set where
  constructor fiveProbeWorldBoundary
  field
    everyDeclaredProbeHasARealCollision : Bool
    everyDeclaredProbeHasARealCollisionIsTrue : everyDeclaredProbeHasARealCollision ≡ true
    samePositiveTherapeuticSurfaceRecoversAuthority : Bool
    samePositiveTherapeuticSurfaceRecoversAuthorityIsFalse : samePositiveTherapeuticSurfaceRecoversAuthority ≡ false
    samePositiveTherapeuticSurfaceRecoversMaterialRouting : Bool
    samePositiveTherapeuticSurfaceRecoversMaterialRoutingIsFalse : samePositiveTherapeuticSurfaceRecoversMaterialRouting ≡ false
    samePositiveTherapeuticSurfaceRecoversSovereignty : Bool
    samePositiveTherapeuticSurfaceRecoversSovereigntyIsFalse : samePositiveTherapeuticSurfaceRecoversSovereignty ≡ false
    separatorProvesHistoricalOrPoliticalCause : Bool
    separatorProvesHistoricalOrPoliticalCauseIsFalse : separatorProvesHistoricalOrPoliticalCause ≡ false

canonicalFiveProbeWorldBoundary : FiveProbeWorldBoundary
canonicalFiveProbeWorldBoundary =
  fiveProbeWorldBoundary true refl false refl false refl false refl false refl
