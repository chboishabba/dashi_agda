# Acacia BNF Situated-Protein LES Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the existing BNF, situated-protein, and merged Acacia dryland LES machinery with source-bounded Acacia/Senegalia rhizobial evidence, situated nitrogenase and nodulation witnesses, and a provenance-retaining BNF↔LES bridge without introducing a replacement ontology.

**Architecture:** Keep the current nitrogenase dependency ladder authoritative. Add four thin owners in dependency order: Acacia rhizobial source atlas → nitrogenase situated-protein witness → legume nodulation situated-protein bridge → Acacia BNF/LES joined observer. Each production owner is preceded by a focused RED regression owner; all organism/source transfer boundaries remain explicit.

**Tech Stack:** Agda; existing DASHI `AttributedSourceCore`, query-indexed projection/factorisation, situated-protein, BNF, nitrogenase chemistry, and LES owners; GitHub source acquisition only. No CI work for this tranche.

**Spec:** `docs/superpowers/specs/2026-09-17-acacia-bnf-situated-protein-design.md`

## Global Constraints

- Reuse the existing BNF, protein, attribution, query-indexed, and LES machinery; do not create a second generic ontology.
- The existing nitrogenase ladder remains authoritative: enzyme stoichiometry paid; reaction enablement, bacterial fixed-N flux, plant assimilation, seasonal plant N demand, and avoided mineral N remain independent stages.
- This tranche may refine evidence for reaction enablement and bacterial fixed-N flux only; do not promote later stages without exact receipts.
- `Acacia senegal` / `Senegalia senegal` synonym handling must remain explicit and must not collapse article identity or same-object study identity.
- Soybean, Lotus, barley, Azotobacter, or other-organism evidence may donate only the exact abstraction supported; it does not become Acacia-specific evidence.
- DOI/PMID/PMCID/PDB/UniProt/taxon/QID coordinates are provenance/identity only and do not create biological truth or authority.
- Root nodules do not prove active fixation; `nifH` presence does not prove fixation rate; nitrogenase stoichiometry does not prove whole-plant or ecosystem nitrogen balance.
- Do not rewrite the merged #980 Sudan water-carbon study as if it measured BNF.
- No CI workflows are to be added, changed, or polled. No Agda/kernel GREEN may be claimed without an exact-head execution receipt actually observed.

---

## File Map

### New production owners

- `DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasExact.agda` — source-only Acacia/Senegalia rhizobial BNF evidence atlas and synonym/source-role boundaries.
- `DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessExact.agda` — situated nitrogenase protein-state witness over `ProteinSituatedHyperfabricExact` plus reuse of the existing nitrogenase chemistry firewall.
- `DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeExact.agda` — receptor/signalling/nodulation/nodule-environment separations and cross-organism transfer firewall.
- `DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationExact.agda` — provenance-retaining joined observer between the Acacia BNF lane and merged #980 dryland LES.

### New focused regression owners

- `DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasRegression.agda`
- `DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessRegression.agda`
- `DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeRegression.agda`
- `DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationRegression.agda`

### Existing files likely modified

- `DASHI/Biology/Agriculture/Everything.agda` — export agriculture-side owners/regressions.
- Existing protein validation/root export file if one already contains `ProteinSituatedHyperfabricExact`; otherwise add only the new protein regression to the narrowest existing protein rollup.
- Do **not** widen global `DASHI/Everything` unless current rollup policy requires it.

---

### Task 1: Acquire and type the Acacia/Senegalia rhizobial source atlas

**Files:**
- Create: `DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasRegression.agda`
- Create: `DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore` or the same attribution carrier used by `HungriaBiologicalNitrogenFixationSourceAtlas`; stable source identifiers from the approved spec.
- Produces: `AcaciaBNFSource`, explicit host-name representation, source role, organism role, measurement family, bounded reading, excluded promotion, and canonical source fixtures for Fall 2008, Fall 2016, Faye 2006, and Herrmann 2012.

- [ ] **Step 1: Write the RED regression owner first**

Create a regression that imports the future production path and pins the source identifiers and non-collapse boundaries. Minimum surface:

```agda
module DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact as Acacia

fall2008DOIPinned : Acacia.doi Acacia.fall2008 ≡ "10.1111/j.1472-765X.2008.02389.x"
fall2008DOIPinned = refl

fall2016DOIPinned : Acacia.doi Acacia.fall2016 ≡ "10.3389/fpls.2016.01355"
fall2016DOIPinned = refl

hostSynonymDoesNotCollapseSourceIdentity :
  Acacia.hostSynonymImpliesSameStudy Acacia.canonicalAcaciaSourceBoundary ≡ false
hostSynonymDoesNotCollapseSourceIdentity = refl

rhizobialIdentityDoesNotCreateFixedNFlux :
  Acacia.rhizobialIdentityImpliesEffectiveFixedNFlux Acacia.canonicalAcaciaSourceBoundary ≡ false
rhizobialIdentityDoesNotCreateFixedNFlux = refl
```

- [ ] **Step 2: Verify RED by source absence, not by CI**

Check the production path before creation with repository lookup. Expected state: exact path absent/404. Record that as the RED source-order receipt. Do not invoke Actions or claim an Agda failure receipt.

- [ ] **Step 3: Implement the source atlas minimally**

Use a focused record rather than a generic new evidence framework:

```agda
data HostNameForm : Set where
  acaciaSenegalName : HostNameForm
  senegaliaSenegalName : HostNameForm

data AcaciaBNFSourceRole : Set where
  rootNodulatorDiversity : AcaciaBNFSourceRole
  matureTreeInoculation : AcaciaBNFSourceRole
  gumYieldInoculation : AcaciaBNFSourceRole
  rhizosphereSeasonality : AcaciaBNFSourceRole

data MeasurementFamily : Set where
  phenotypeGenotype : MeasurementFamily
  soilMicrobialMineralN : MeasurementFamily
  gumProduction : MeasurementFamily
  communityComposition : MeasurementFamily

record AcaciaBNFSource : Set where
  constructor acacia-bnf-source
  field
    authors title publication doi pmid pmcid site : String
    year : Nat
    hostName : HostNameForm
    role : AcaciaBNFSourceRole
    measurement : MeasurementFamily
    rhizobialIdentityReading : String
    boundedReading : String
    excludedPromotion : String
```

Add canonical fixtures with only verified identifiers. If PMID/PMCID is not verified for a source, keep the field empty or use the repository's established optional-identity representation; do not guess.

Add an explicit boundary record:

```agda
record AcaciaSourceBoundary : Set where
  constructor acacia-source-boundary
  field
    hostSynonymImpliesSameStudy : Bool
    rhizobialIdentityImpliesEffectiveFixedNFlux : Bool
    inoculationResponseImpliesNitrogenaseMediation : Bool
    gumYieldResponseIsDirectFixationRate : Bool
    localFieldResultImpliesDeploymentAuthority : Bool
```

Canonical values are all `false`.

- [ ] **Step 4: Review source-role fidelity**

Confirm each source fixture says only what its role supports. In particular, Fall 2016 and Faye 2006 must not be typed as direct nitrogenase-rate measurements, and Herrmann 2012 must not be typed as effective-fixation proof.

- [ ] **Step 5: Commit Task 1**

```bash
git add DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasRegression.agda \
        DASHI/Biology/Agriculture/AcaciaSenegalRhizobialBNFSourceAtlasExact.agda
git commit -m "feat: add Acacia rhizobial BNF source atlas"
```

---

### Task 2: Instantiate the situated-protein machinery for nitrogenase

**Files:**
- Create: `DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessRegression.agda`
- Create: `DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessExact.agda`

**Interfaces:**
- Consumes: `DASHI.Biology.Protein.ProteinSituatedHyperfabricExact`, `DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact`, and source fixtures for Seefeldt 2009, Warmack/Rees 2024, Narehood et al. 2025, and Payá Tormo et al. 2025/2026.
- Produces: a nitrogenase-specific state carrier, a `SituatedProteinQueryWitness`, and a finite collision showing protein identity is too coarse for catalytic/protected state; reuses the existing chemistry owner for stoichiometry ≠ effective flux.

- [ ] **Step 1: Write the RED regression owner**

Pin the intended public API:

```agda
module DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact as Nif

proteinIdentityProjectionIsInadequate :
  Nif.proteinIdentityAloneAdequate Nif.canonicalNitrogenaseBoundary ≡ false
proteinIdentityProjectionIsInadequate = refl

balancedStoichiometryDoesNotCreateEffectiveFlux :
  Nif.balancedStoichiometryCreatesEffectiveFlux Nif.canonicalNitrogenaseBoundary ≡ false
balancedStoichiometryDoesNotCreateEffectiveFlux = refl

azotobacterProtectionIsNotAcaciaMechanism :
  Nif.azotobacterProtectionTransfersToAcacia Nif.canonicalNitrogenaseBoundary ≡ false
azotobacterProtectionIsNotAcaciaMechanism = refl
```

- [ ] **Step 2: Verify RED by missing production owner**

Confirm the production path is absent before creation. Record only source-order RED.

- [ ] **Step 3: Define the minimum nitrogenase situated state**

Use explicit finite coordinates:

```agda
data NitrogenaseIdentity : Set where
  moNitrogenase : NitrogenaseIdentity

data OxygenContext : Set where
  lowOxygen : OxygenContext
  oxygenStress : OxygenContext

data PartnerState : Set where
  noProtectivePartner : PartnerState
  feSIIAssociated : PartnerState

data TurnoverState : Set where
  restingLike : TurnoverState
  turnoverState : TurnoverState

data NitrogenaseFunctionalState : Set where
  catalyticallyAvailable : NitrogenaseFunctionalState
  conformationallyProtected : NitrogenaseFunctionalState

record NitrogenaseSituatedState : Set where
  constructor nitrogenase-state
  field
    proteinIdentity : NitrogenaseIdentity
    oxygenContext : OxygenContext
    partnerState : PartnerState
    turnover : TurnoverState
    functionalState : NitrogenaseFunctionalState
    cofactorState : String
    historyState : String
    observerMethod : String
    sourceProvenance : String
```

Use two DASHI synthetic worlds with the same `proteinIdentity` but different `functionalState`, e.g. low-oxygen catalytic vs oxygen-stress FeSII-protected. State clearly that the source literature motivates the coordinate distinction; the two-world factorisation witness is DASHI synthesis.

- [ ] **Step 4: Bind to `ProteinSituatedHyperfabricExact`**

Instantiate a `SituatedProteinQueryWitness` using the existing generic query semantics. The projection should retain only `NitrogenaseIdentity`; the query asks for `NitrogenaseFunctionalState`. Supply the exact `QueryAdequacyDefect` using the two worlds above.

Do not define a parallel `FactorsThrough` type if `ProteinSituatedHyperfabricExact` already exposes `SituatedProteinQueryWitness` + `witnessBlocksCoarseAdequacy`.

- [ ] **Step 5: Reuse the nitrogenase chemistry firewall**

Export a local alias/witness that points at the existing false promotion:

```agda
balancedStoichiometryStillDoesNotCreateInVivoFlux =
  ChemistryBoundary.balancedEquationImpliesInVivoFlux
    ChemistryBoundary.canonicalNitrogenaseCrossDomainBoundary
```

Do not restate the Mo-nitrogenase equation in a new authoritative record.

- [ ] **Step 6: Commit Task 2**

```bash
git add DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessRegression.agda \
        DASHI/Biology/Protein/NitrogenaseSituatedProteinWitnessExact.agda
git commit -m "feat: situate nitrogenase protein state"
```

---

### Task 3: Add the legume nodulation situated-protein bridge

**Files:**
- Create: `DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeRegression.agda`
- Create: `DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeExact.agda`

**Interfaces:**
- Consumes: `ProteinSituatedHyperfabricExact`, `NitrogenaseSituatedProteinWitnessExact`, and the Tsitsikli et al. 2025 residue-level signalling source as a cross-organism structural donor.
- Produces: a nodulation/signalling state carrier, exact finite collision for receptor identity ≠ signalling output, and explicit stage firewalls from recognition through plant fixed-N delivery.

- [ ] **Step 1: Write the RED regression owner**

```agda
module DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact as Nod

receptorIdentityIsTooCoarse :
  Nod.receptorIdentityDeterminesSignalling Nod.canonicalNodulationBoundary ≡ false
receptorIdentityIsTooCoarse = refl

recognitionDoesNotCreateNodule :
  Nod.nodFactorRecognitionImpliesSuccessfulNodulation Nod.canonicalNodulationBoundary ≡ false
recognitionDoesNotCreateNodule = refl

noduleDoesNotCreatePlantFixedN :
  Nod.nodulePresenceImpliesIntegratedPlantFixedN Nod.canonicalNodulationBoundary ≡ false
noduleDoesNotCreatePlantFixedN = refl

lotusEvidenceDoesNotBecomeAcaciaEvidence :
  Nod.crossLegumeMechanismTransferAutomatic Nod.canonicalNodulationBoundary ≡ false
lotusEvidenceDoesNotBecomeAcaciaEvidence = refl
```

- [ ] **Step 2: Verify RED by source absence**

Confirm the future production owner is absent before creation; record source-order only.

- [ ] **Step 3: Implement a finite signalling collision**

Use a deliberately small state:

```agda
data ReceptorIdentity : Set where
  receptorFamilyMember : ReceptorIdentity

data ResidueState : Set where
  immuneLikeResidues : ResidueState
  symbiosisRoutingResidues : ResidueState

data SignallingOutput : Set where
  immuneBiased : SignallingOutput
  symbiosisBiased : SignallingOutput

record NodulationProteinState : Set where
  constructor nodulation-protein-state
  field
    receptorIdentity : ReceptorIdentity
    residueState : ResidueState
    signallingOutput : SignallingOutput
    ligandReading : String
    phosphorylationInteractionReading : String
    organismReading : String
    sourceReading : String
```

Construct two synthetic worlds sharing receptor identity but differing residue state/signalling output. Use the existing query-indexed/situated-protein factorisation API rather than a new generic theorem family.

- [ ] **Step 4: Encode the stage ladder as independent booleans/firewalls**

Required fields in `NodulationBoundary`:

```agda
receptorIdentityDeterminesSignalling : Bool
nodFactorRecognitionImpliesSuccessfulNodulation : Bool
successfulNodulationImpliesActiveNitrogenase : Bool
activeNitrogenaseImpliesIntegratedPlantFixedN : Bool
crossLegumeMechanismTransferAutomatic : Bool
```

Canonical values are all `false`. If a later source pays one arrow, add a separate positive receipt rather than flipping a generic implication to true.

- [ ] **Step 5: Commit Task 3**

```bash
git add DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeRegression.agda \
        DASHI/Biology/Agriculture/LegumeNodulationSituatedProteinBridgeExact.agda
git commit -m "feat: bridge legume nodulation to situated protein state"
```

---

### Task 4: Join Acacia BNF to the merged dryland LES surface

**Files:**
- Create: `DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationRegression.agda`
- Create: `DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationExact.agda`

**Interfaces:**
- Consumes: `AcaciaSenegalRhizobialBNFSourceAtlasExact`, `NitrogenaseSituatedProteinWitnessExact`, `LegumeNodulationSituatedProteinBridgeExact`, `BNFQualifiedInterventionModelExact`, `AcaciaSenegalDrylandWaterCarbonExact`, and `AcaciaSenegalDrylandTaskFactorisationExact`.
- Produces: one provenance-retaining joined observer plus finite non-factorability witnesses showing tree identity, nodule presence, rhizobial identity, or a single fixed-N metric are each insufficient for broader declared consumers.

- [ ] **Step 1: Write the RED regression owner**

Pin both reuse and no-promotion:

```agda
module DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact as Bridge

reusesMergedWaterCarbonLES :
  Bridge.reusesAcaciaWaterCarbonOwner Bridge.canonicalAcaciaBNFLESBoundary ≡ true
reusesMergedWaterCarbonLES = refl

reusesExistingBNFModel :
  Bridge.reusesBNFQualifiedInterventionOwner Bridge.canonicalAcaciaBNFLESBoundary ≡ true
reusesExistingBNFModel = refl

nodulePresenceIsNotSoilNOutcome :
  Bridge.nodulePresenceDeterminesSoilNOutcome Bridge.canonicalAcaciaBNFLESBoundary ≡ false
nodulePresenceIsNotSoilNOutcome = refl

fixedNMetricIsNotRestorationDecision :
  Bridge.fixedNMetricDeterminesRestorationDecision Bridge.canonicalAcaciaBNFLESBoundary ≡ false
fixedNMetricIsNotRestorationDecision = refl
```

- [ ] **Step 2: Verify RED by missing production owner**

Confirm exact production path absent before creation. No CI.

- [ ] **Step 3: Define a joined observer, not a replacement LES state**

Use a record whose fields point at existing owner surfaces where practical:

```agda
record AcaciaBNFLESObservation : Set₁ where
  constructor acacia-bnf-les-observation
  field
    WaterCarbonState : Set
    BNFState : Set
    waterCarbonState : WaterCarbonState
    bnfState : BNFState
    rhizobialPartnerReading : String
    nodulationReading : String
    nitrogenaseSituatedReading : String
    fixedNEvidenceReading : String
    soilNReading : String
    sourceRoleReading : String
```

The purpose is to preserve independent provenance of #980 water/carbon evidence and BNF evidence. Do not copy #980 numerical/qualitative claims into this record as if generated by the BNF sources.

- [ ] **Step 4: Add finite consumer collisions**

Create small repository-local worlds for four separate consumers:

1. `SoilNOutcome not FactorsThrough TreeIdentity`
2. `SoilNOutcome not FactorsThrough NodulePresence`
3. `FixedNFlux not FactorsThrough RhizobialIdentity`
4. `RestorationDecision not FactorsThrough FixedNMetric`

Prefer one reusable finite world carrier only if it makes all four distinctions transparent. Otherwise keep the fixtures separate; do not force unrelated consumers into one mega-state.

For each collision, explicitly annotate:

```text
source premise used
DASHI synthetic coordinates varied
consumer queried
projection shown insufficient
repair coordinate retained
```

- [ ] **Step 5: Reuse the existing BNF and LES boundaries directly**

Export aliases to:

- `BNFQualifiedInterventionModelExact.canonical...` consumer requirement/boundary surface;
- `AcaciaSenegalDrylandWaterCarbonExact` source boundary;
- `AcaciaSenegalDrylandTaskFactorisationExact` task-factorisation boundary;
- the new nitrogenase/nodulation boundaries.

Do not duplicate their Bool fields under different names unless the new bridge needs a genuinely new cross-owner proposition.

- [ ] **Step 6: Add the composed boundary**

Minimum fields:

```agda
reusesAcaciaWaterCarbonOwner : Bool
reusesBNFQualifiedInterventionOwner : Bool
reusesSituatedNitrogenaseOwner : Bool
reusesNodulationBridge : Bool
treeIdentityDeterminesSoilNOutcome : Bool
nodulePresenceDeterminesSoilNOutcome : Bool
rhizobialIdentityDeterminesFixedNFlux : Bool
fixedNMetricDeterminesRestorationDecision : Bool
waterCarbonStudyMeasuredBNF : Bool
molecularBNFEvidenceCreatesDeploymentAuthority : Bool
```

Canonical first four `true`; canonical final six `false`.

- [ ] **Step 7: Commit Task 4**

```bash
git add DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationRegression.agda \
        DASHI/Biology/Agriculture/AcaciaSenegalBNFLESCrossPollinationExact.agda
git commit -m "feat: cross-pollinate Acacia BNF with dryland LES"
```

---

### Task 5: Integrate focused rollups without widening authority

**Files:**
- Modify: `DASHI/Biology/Agriculture/Everything.agda`
- Modify: the narrowest existing protein validation/root file that already exports `ProteinSituatedHyperfabricExact`; if no such focused root exists, create `DASHI/Biology/Protein/NitrogenaseSituatedProteinValidation.agda` rather than editing global `DASHI/Everything`.

**Interfaces:**
- Consumes: all four production owners and four regression owners.
- Produces: transitive import surfaces for focused agriculture/protein validation only.

- [ ] **Step 1: Inspect current rollup policy**

Read `DASHI/Biology/Agriculture/Everything.agda` and the current protein validation/export roots. Choose the narrowest existing root consistent with neighboring recent protein work.

- [ ] **Step 2: Add agriculture imports**

Add the three agriculture production owners and their regressions, preserving current import ordering conventions.

- [ ] **Step 3: Add protein import to the focused protein root**

Import `NitrogenaseSituatedProteinWitnessExact` and its regression in the narrowest existing protein rollup/validation root. Do not add it to a global root merely for discoverability.

- [ ] **Step 4: Source-level dependency review**

Check for import cycles conceptually:

```text
Protein nitrogenase witness
  -> existing protein + agriculture nitrogenase chemistry
Agriculture nodulation bridge
  -> protein witness
Agriculture Acacia BNF/LES bridge
  -> source atlas + nodulation + protein witness + existing LES/BNF
```

If adding the protein witness to `Agriculture.Everything` would create a cycle, export it only from the protein root and let the agriculture bridge import the concrete file directly.

- [ ] **Step 5: Commit Task 5**

```bash
git add DASHI/Biology/Agriculture/Everything.agda DASHI/Biology/Protein/
git commit -m "chore: export Acacia BNF situated-protein bridge"
```

---

### Task 6: Final source/authority self-review and PR handoff

**Files:**
- Review all files from Tasks 1-5.
- Update the implementation branch PR description if/when a PR is opened.

**Interfaces:**
- Consumes: complete source-written tranche.
- Produces: an auditable source-level status report; no fabricated certification.

- [ ] **Step 1: Search for forbidden promotions**

Search the diff for claims equivalent to:

```text
nodule => fixation
nifH => fixation rate
nitrogenase identity => function
stoichiometry => in-vivo flux
fixed N => plant assimilation
plant assimilation => soil N outcome
soil N => restoration success
molecular evidence => deployment authority
Lotus/Azotobacter source => Acacia same-object mechanism
```

Any such implication must either be removed or backed by an explicit source/consumer receipt.

- [ ] **Step 2: Check source identity fidelity**

Verify every DOI/PMID/PMCID/PDB value against the source atlas/spec. Keep unresolved identifiers unresolved. Ensure `Acacia senegal` vs `Senegalia senegal` naming is source-indexed, not globally normalized away.

- [ ] **Step 3: Check reuse fidelity**

Confirm the tranche imports rather than redefines:

```text
ProteinSituatedHyperfabricExact
NitrogenaseChemistryCrossPollinationExact
BNFQualifiedInterventionModelExact
AcaciaSenegalDrylandWaterCarbonExact
AcaciaSenegalDrylandTaskFactorisationExact
```

- [ ] **Step 4: Check regression ordering**

For each new production owner, ensure the corresponding regression commit precedes it and the future path was observed absent before creation. Do not describe source-order RED as an Agda kernel RED.

- [ ] **Step 5: Report certification status exactly**

Final status language must be:

```text
source-written: yes
source-order RED receipts: yes, where observed
CI queried: no
Agda/kernel receipt: unobserved unless separately executed
```

Do not use “passes”, “green”, “certified”, or equivalent without an actual exact-head execution receipt.

- [ ] **Step 6: Commit any self-review corrections**

```bash
git add DASHI docs
 git commit -m "docs: tighten Acacia BNF source and authority boundaries"
```

Skip this commit if no correction is needed.
