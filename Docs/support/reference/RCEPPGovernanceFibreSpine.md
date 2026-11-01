# RCEPP governance/fibre spine

## Purpose

This note records the governance formalisation built from the supplied English
edition of *The Revolutionary Charter for Establishing People's Power* (11
January 2023) and its cross-pollination with existing DASHI carriers.

The source is represented as collective work by Sudanese Resistance Committees
and signatory revolutionary forces.  No DOI is assigned in the supplied edition.
The repository accepts citation identity only.  It does not claim that the PDF is
an authenticated machine-readable constitutional artifact, that this is an
official interpretation, or that the Charter is legally operative or universally
endorsed.

## The central correction: one coarse fibre over three fine roles

The relational notation is not an arithmetic theorem that `1 = 3`.

```text
one coarse relational unit
        ^ projection fibre
principal / delegate / mandate relation
```

A public representation relation is observed coarsely as one mandate-bearing
unit, while its fine carrier has three non-collapsible roles:

1. the principal or constituency;
2. the delegate or agent;
3. the scope-limited, recallable mandate relation between them.

`DASHI.Governance.RelationalMandateFibre` makes this distinction explicit.  It
reuses:

- the subject/other/relation grammar from
  `DASHI.Culture.CulturalTriadOperatorBoundary`;
- the projection-loss discipline from `DASHI.Core.FibreRestrictionCore`;
- the rank-one/depth-one ternary count from
  `DASHI.Foundations.RecursiveRadixHypervoxel`.

The hypervoxel bridge is shape-only.  It does not say that persons or public
institutions are literal voxels.  The one coarse unit projects a three-role fine
carrier, while the exact theorem remains only `siteCount 1 1 = 3`.

## Existing governance lane discovered and reused

The repository already had a substantial `DASHI.Governance` lane:

- `GovernedArtifactCore` separates candidate generation from canonical state
  mutation;
- `PromotionSpine` composes candidate, receipt, closure and authorization
  layers;
- `ArtifactAuthorityPromotionBridge` separates citation identity from
  artifact authority;
- `Governance.Everything` is the domain aggregate.

The RCEPP work extends this lane rather than creating a parallel political
architecture.  In particular,
`DASHI.Governance.Sudan.RCEPPPromotionBoundary` proves that a citation-only
Charter source remains quarantined and yields `abstain` even when the other
formal closure bits are set optimistically.  An operative constitutional
artifact and popular-recognition evidence remain external.

## Reusable governance core

### Authority as a relation

`DASHI.Governance.AuthorityMandateCore` records authority as:

```text
source + constituency + representative + scope + term + recall + review
```

Possession of force, elite agreement alone and external recognition alone are
not admissible origins of sovereign authority.  The mandate remains with the
constituency because every represented delegate carries recall and review
obligations.

Conceptual precedent:

- Hanna Fenichel Pitkin, *The Concept of Representation* (1967).  Book; no DOI
  assigned.

The Agda module formalises a relation grammar only; it does not claim to
formalise all of Pitkin's account.

### Situated constituency and axis bundles

`DASHI.Governance.SituatedConstituency` ports the existing
body/time/place/relation/institution/axis discipline into public representation.
The canonical governance axes include rural/urban position, displacement,
land, ethnicity, gender, class, religion, coloniality, armed power and
institutional access.

Intersectionality precedent:

- Kimberle Williams Crenshaw, "Mapping the Margins: Intersectionality, Identity
  Politics, and Violence against Women of Color", *Stanford Law Review* 43(6),
  1991. DOI: `10.2307/1229039`.

The finite list is explicitly non-exhaustive and cannot substitute for affected
communities' own articulation.

### Bidirectional council graph

`DASHI.Governance.CouncilDelegationGraph` distinguishes:

```text
upward delegation
!=
downward accountability and recall
```

It also supplies the typed subordination path:

```text
military/security
  -> civilian executive
  -> legislature
  -> people
```

There is no military-to-sovereignty edge.

### Proof-carrying local/global gluing

`DASHI.Governance.LocalGlobalCouncilGluing` reuses the repository's existing
`BundleSheaf` carrier.  Neighbourhood, rural-locality, elected-union and IDP-camp
sections do not become a national section merely by coexisting.  The model
requires a compatibility witness, constructs a global section only through the
gluing operation, and proves that the result restricts back exactly to each
local section.

```text
compatible local sections
        -> glue
one global section
        -> restrict
original local sections
```

This gives the council hierarchy a local-to-global consistency law without
collapsing local mandates into the global node.  The witness is internal to the
finite model: it does not establish actual political compatibility, consent,
apportionment or authority.

### Constitutional chart, residual and +1

`DASHI.Governance.TransitionResidual` reuses the existing
chart/residual/+1 topology.  A transition is not one unqualified leap from old
to new.  It is a guarded repair that:

- names the violated invariant;
- records affected axes and constituencies;
- retains unresolved residuals;
- preserves previously satisfied invariants;
- does not mint authority from a formal stage label.

The four governance validation positions are:

- satisfied;
- positively violated;
- undetermined because an axis is incomplete;
- inapplicable to the inspected role.

They map into the existing residual and tetralemma carriers without claiming
historical or philosophical equivalence.

## RCEPP instance

The Sudan-specific modules instantiate the generic spine with:

- neighbourhood, rural, elected-union and IDP-camp constituencies;
- neighbourhood/locality/state/national council nodes;
- proof-carrying local/global section gluing and exact restriction back to local
  mandate/recall sections;
- upward delegation and downward accountability;
- civilian supremacy and rejection of armed veto as legitimacy;
- one auditable civilian public-resource jurisdiction;
- peace as community participation, land, return, reparation, justice,
  institutional reform and regional development;
- a guarded transition from coup order through prefigurative organisation,
  transitional councils, constitution-making and democratic closure.

The source-specific lane remains separate from the reusable governance core so
that one Sudanese programme is not silently promoted into a universal theory of
government.

## Plural revolutionary-practice ecology

`DASHI.Governance.RevolutionaryPracticeBraid` adds five strands without
collapsing them:

```text
institutional transformation
+ relational transformation
+ epistemic transformation
+ ecological transformation
+ historical-trauma transformation
```

It cross-pollinates:

- the existing Sweetgrass braid/fabric attribution and non-promotion boundary;
- knot/weave/braid cultural operators;
- non-alienating mandate and local/global council gluing;
- reciprocity on the chart/residual/+1 topology;
- dialectical memory carry and distributed braid tension;
- the repo-local `PatternMind` repair-context vocabulary.

`PatternMind` remains a repository-local label here.  The implementation does
not attach speculative external authorship or pretend that a single doctrine
has been identified.

The relationship-anarchy adjunct records five dimensions:

```text
consent
+ autonomy
+ dependency/material asymmetry
+ obligation/reciprocity
+ exit/recall/revision
```

A relationship category alone creates no entitlement.  Declared consent does
not prove material symmetry, informal structure does not prove equality, and a
relationship label does not alienate autonomy.

The Summer of Love enters as ambivalent historical context rather than an
origin myth.  Relational experimentation, anti-war communal practice and art as
social infrastructure are retained beside informal hierarchy, gendered care
labour, racial/class exclusion and commodification residuals:

```text
removal of convention != removal of domination
sexual openness != consent
communal life != shared labour
```

### Attributed philosophy and history sources

`DASHI.Governance.RevolutionarySourceAtlas` records author, title, publication
context and DOI state.  A missing DOI means only that none is recorded by this
atlas.

- Robin Wall Kimmerer, *Braiding Sweetgrass: Indigenous Wisdom, Scientific
  Knowledge and the Teachings of Plants* (2013); no DOI recorded by the atlas.
- Andie Nordgren, *The Short Instructional Manifesto for Relationship Anarchy*
  (original Swedish circulation 2006; later English circulation); no DOI
  recorded by the atlas.
- Peter Kropotkin, *Mutual Aid: A Factor of Evolution* (1902); no DOI recorded.
- Frantz Fanon, *The Wretched of the Earth* (1961); no DOI recorded.
- Judith Butler, *Frames of War: When Is Life Grievable?* (2009); no DOI
  recorded.
- Dominick LaCapra, *Writing History, Writing Trauma* (2001); no DOI recorded.
- Kimberle Williams Crenshaw, "Mapping the Margins" (1991), DOI
  `10.2307/1229039`.
- National Commission on Terrorist Attacks Upon the United States, *The 9/11
  Commission Report* (2004); no DOI recorded.
- Edward W. Said, *The Question of Palestine* (1979); no DOI recorded.
- Rashid Khalidi, *The Hundred Years' War on Palestine* (2020); no DOI recorded.
- Ervand Abrahamian, *The Coup: 1953, the CIA, and the Roots of Modern
  U.S.-Iranian Relations* (2013); no DOI recorded.
- Todd Gitlin, *The Sixties: Years of Hope, Days of Rage* (1987); no DOI
  recorded.

The atlas does not claim that these sources agree, endorse DASHI, or exhaust the
relevant intellectual traditions.

## Trauma, memory, sublation and spectacle

`DASHI.Governance.TraumaMemorySublationBoundary` connects the existing
body-memory residual, multi-observer quotient and constitutional transition
surfaces.

Its central boundary is:

```text
trauma explains political formation
!=
trauma legitimates violence
```

Prior injury may support recognition, safety and repair claims.  It does not
authorise unlimited control, erase another population's grief, establish power
parity, or authorise civilian harm.

Historical narratives retain the selected-origin problem.  The Iran/USA lane
carries both 1953 and 1979 frames; the post-9/11 lane retains history prior to 11
September 2001; Israel/Palestine carries plural persecution, displacement,
occupation, attack, war and resistance frames; Sudan's April 2023 frame retains
prior colonial, authoritarian, regional and revolutionary history.

The reflecting pool, White House renovation and Freedom 250/WWE/combat-sport
imagery enter only as `ContemporaryMemoryObservation` values.  They permit a
candidate symbolic reading while requiring external sources and explicitly
blocking factual motive inference, legal conclusions, personality diagnosis and
closed historical meaning.

## Comparative crisis, liberation and climate atlas

`DASHI.Governance.ComparativeCrisisClimateAtlas` keeps Sudan/RCEPP as the
situated constitutional case and introduces non-equating comparative lanes for:

- Israel/Palestine;
- Iran/USA;
- United States post-9/11 trauma and war-on-terror repetition;
- the war-on-drugs enemy-carrier/punitive-state grammar;
- Trumpist traumatic-restoration and memory-spectacle analysis.

Palestinian liberatory practice is represented as plural: secular-national,
Marxist/PFLP, Islamist, trade-union/student/women, popular-committee,
diplomatic/state-building, cultural-intellectual and diaspora currents.  The
PFLP row enforces:

```text
liberatory objective != automatic legitimacy of every tactic
criticism of a tactic != erasure of the underlying liberation claim
```

No organisational label represents a whole people, determines every historical
tactic, or creates designation authority inside Agda.

The climate/social-justice lane records food/water pressure, displacement,
land/livelihood, urban pressure, energy geopolitics, border militarisation,
disaster opportunism and unequal recovery.  Climate pressure is material but is
not a sole-cause theorem.  Political responsibility, militarisation, unequal
land relations, institutional capacity and historical dispossession remain
explicit.

The ecological peace carrier requires civilian safety, land repair, voluntary
return, reciprocity, material justice, ecological continuance and affected
community participation.  Armed-elite agreement alone is insufficient, and
public ownership alone is not ecological reciprocity.

The global-attention residual records that attention is not a measure of the
scale of suffering.  Sudan is therefore neither reduced to an analogy nor
silently made secondary to conflicts with greater imperial or media centrality.

## Claim layers

The implementation keeps five layers distinct:

```text
source text
!=
DASHI interpretation
!=
typed model property
!=
operative constitutional validity
!=
actual popular legitimacy
```

Agda may prove that a model has recall, scope, subordination, local/global
restriction and fail-closed promotion properties.  It cannot determine which
real committee represents a constituency, authenticate signatories, establish
real compatibility among constituencies, enact a constitution, establish peace,
resolve collective trauma, determine historical motive, endorse an organisation
or tactic, or issue popular legitimacy.

## Validation surfaces

RCEPP-focused aggregate:

```text
DASHI/Governance/Sudan/RCEPPRegression.agda
```

Revolutionary adjunct aggregate:

```text
DASHI/Governance/RevolutionaryAdjunctRegression.agda
```

Domain aggregate:

```text
DASHI/Governance/Everything.agda
```

Source audit:

```text
python3 scripts/check_rcepp_governance_spine.py
```

Kernel checks should use the repository's Agda 2.9/Nix runner.  The Python audit
is fail-closed source inspection and is not a substitute for Agda typechecking.
