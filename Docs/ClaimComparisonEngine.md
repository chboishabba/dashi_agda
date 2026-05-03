# Claim Comparison Engine

Declared surface level: `bridge/adapter`.

This note records the current repo-accurate chain for natural-language claim
comparison. It is deliberately split into runtime emission, compiled residual
algebra, pressure adaptation, and proof-side bridge surfaces.

For the downstream attractor/orbit-classifier design that consumes receipted
residual, domain, formula, and Hecke features, see
[`AttractorOrbitClassifier.md`](./AttractorOrbitClassifier.md).

## Core Boundary

The formalism owns the conditional:

```text
if two PNFEmissionReceipt values exist,
then receiptResidual computes their deterministic residual level.
```

It does not own the antecedent:

```text
which PredicatePNF atoms the parser / shared reducer emits from text.
```

That antecedent belongs to the runtime ITIR/SensibLaw pipeline.

## Runtime Emission Layer

The runtime pipeline is outside DASHI Agda:

```text
source text
  -> spaCy token/dependency parse
  -> shared_reducer relation extraction
  -> PredicatePNF emission
  -> PNFEmissionReceipt
```

The receipt boundary is now explicit in
`DASHI.Interop.SensibLawResidualLattice`:

```text
PNFEmissionReceipt =
  parserProfile
  reducerProfile
  sourceSpan
  emittedAtom : PredicatePNF
```

No wrapper, qualifier, role, signature, or residual label is valid for a text
span until the pipeline emits a receipt carrying the atom.

## Already-Formal Inputs

Some source spans may arrive with explicit mathematical or symbolic structure,
for example a formula embedded in a political post or report. The rule is the
same:

```text
source formula
  -> parser / reducer / formula-reader profile
  -> emitted PredicatePNF or formula receipt
  -> residual comparison
```

The formalism may check the structure once a receipt exists. It must not infer
wrapper, domain, or market-causality labels merely because the source text
contains notation. The source author may have reduced their claim to a formula;
the pipeline still has to emit the typed object before DASHI can compare it.

## Operator-Level Formula Fixtures

An already-formal source span can sometimes be stronger than an ordinary PNF
claim: it can assert a property of an operator rather than a property of one
actor, event, or price. A typical shape is:

```text
condition on the system state
  -> f (f x) > f x
```

If a formula-reader receipt emits that structure, the safe interpretation is
that the source span is an operator-level hypothesis: locally, at the named
state, the emitted operator is being presented as expansive rather than
contractive. In a case-study corpus this can be treated as a sufficient
statistic for a family of mechanism hypotheses: different narratives about why
a stabilizing constraint was absent may all share the same operator-level
consequent.

The guardrail is strict:

- local `f (f x) > f x` does not prove a global dynamical model;
- local non-contraction does not construct an `AntiFascistSystem` instance;
- a source formula does not discharge entropy, invertibility, or non-collapse
  postulates without a named carrier, operator, entropy observable, and
  certificate;
- CRT or moonshine periodicity does not bound an empirical market process
  unless a model map into the CRT/J carrier has been supplied.

So the formula fixture can compress competing causal explanations for review,
but it remains a conditional receipt-driven test surface until the runtime
pipeline and a model certificate provide the missing antecedents.

## Domain-Incommensurability Fixtures

The operator formula fixture has a sharper companion: a source corpus may
contain two decision domains that do not share a utility measure. For example,
one receipted atom may frame an outcome as an economic cost while another
receipted atom frames action under a theological, ideological, or terminal
mandate. The safe formal pattern is:

```text
economic operator receipt:
  cost or expansion is stated in domain D_econ

mandate/operator receipt:
  objective is stated in domain D_mandate

candidate bridge:
  no emitted measure map D_mandate -> D_econ
```

If the pipeline and a domain model emit those fields, the comparison is not
merely a bad same-fibre comparison. It is a domain-bridge failure: the
deterrence argument only applies if a measure map or positive utility weight
from the economic domain into the decision domain exists.

This is currently a documentation and design fixture, not a compiled Agda
constructor. The existing four-level residual carrier sends cross-signature
comparison to `noTypedMeet`. The existing six-level carrier includes
`scopeExceeded6`, but it does not yet distinguish:

- ordinary cross-signature failure inside one comparison universe;
- scope-exceeded material that the runtime can still carry as a typed wrapper
  or domain flag;
- stronger domain incommensurability, where no common measure map has been
  emitted and the comparison itself is not licensed.

A future carrier may add an explicit `incommensurable` value or represent this
as metadata outside the residual chain. Until then, the repo should record
domain incommensurability as an open promotion gate rather than silently
encoding it as `contradiction`, `noTypedMeet`, or `scopeExceeded6`.

This also blocks a tempting market-reading shortcut. A formula can be used as
a classifier only after receipts show a response, non-response, utility-domain
claim, or model update. The repository must not infer that a market moved
because a decision-maker changed orbit unless the corpus receipts and market
model actually carry that transition.

## Attractor / Orbit Classification

The same receipted stream can feed an attractor/orbit classifier. The safe
abstract problem is:

```text
receipted observation stream
  -> residual / wrapper / domain / Hecke features
  -> operator-class hypothesis
```

This is a hypothesis layer over receipts, not a theorem result. Candidate
labels such as convergent, orbiting, or terminal are allowed only as model
outputs after a feature extractor exists. They must not be read directly from
raw prose or from a single defect summary.

The Hecke adapter is especially easy to overread. `stableDefect`,
`illegalDefect`, and `otherDefect` are typed representation-layer features
once emitted. They do not, by themselves, prove that a live text corpus has
entered a fixed point, a non-collapsing orbit, or a terminal regime.

For trading use, the classifier output is not a price floor or a trading
signal until a separate empirical model, backtest, transaction-cost model, and
risk-governance surface validate that mapping. For causal-source inference,
the classifier output is not a hidden-principal claim until a separate causal
model and provenance standard validate that inference.

## Market Self-Observation Fixtures

Trading psychology and market-structure fixtures introduce an additional
self-observation loop:

```text
trader state is part of the observed market system
```

The comparison engine may represent that loop only after it receives typed
receipts for both sides:

- trader-state receipts, with an explicit non-clinical / non-diagnostic
  boundary;
- market-data receipts, with venue, timestamp, latency, survivorship, and
  transaction-cost metadata;
- model receipts describing any cross-scale map from affective, theological,
  political, or RG-style features into market observables.

The engine must not compare an introspective label such as "sympathetic",
"dorsal", "DharmaSystem", or "operator-compromised" directly against a trade
outcome. It first needs a typed carrier and a validation standard explaining
what the label means operationally.

The same rule blocks period-language shortcuts. `CRTPeriod` and `JFixedPoint`
are not market-cycle estimators. A claim that a market is approaching a
cycle-exhaustion or `+1` regime-change point requires a separate market
carrier, period-estimation method, regime-change observable, pre-registered
decision rule, and out-of-sample validation. Without those receipts, the
engine records the claim as a hypothesis fixture, not as a price signal,
investment recommendation, or empirical forecast.

## Political-Label And State-Operator Fixtures

A question about whether a state, institution, or movement satisfies a named
political label is not answered directly by the residual algebra. It must be
split into two different objects:

```text
political label claim:
  a PredicatePNF atom in an evidential, advocacy, legal, or scholarly domain

operator trace:
  a receipted stream of per-domain observations that may support
  convergent, orbiting, terminal, or composite operator hypotheses
```

The residual layer can compare those objects only after receipts exist. It can
say that a political-label claim overlaps with, conflicts with, or misses a
receipted operator trace under a chosen taxonomy. It cannot identify the
political label with the formal `FascisticSystem` record merely because the
names are suggestive.

The same guardrail applies to composite operators. If a model emits one
domain trace as convergent, another as orbiting, and another as terminal, the
safe result is a composite-operator hypothesis. It is not a proof that a live
state has a single global class, and it is not a substitute for a political,
legal, or historical classification standard.

## Responsibility / Aggressor Fixtures

An "aggressor" claim is a PNF atom in a legal, political, ethical, or advocacy
domain. It is not a primitive residual level. The ordinary fixture assumes a
shared fibre:

```text
agent: Actor
theme: InitiatedViolence
goal: Dominance / coercion / territorial change / other taxonomy value
```

If the emitted atoms do not share the required fibre, the ordinary
aggressor/defender comparison is not licensed by that taxonomy. A separate
incommensurable-operator responsibility model may still be defined, but it
must say what replaces first-mover or initiation criteria.

For example, a model may introduce predicates such as:

```text
nonResponsiveTheta
costConvertedToMandate
thirdPartyCostShiftWithoutConsent
```

The residual layer can compare receipts that emit those predicates. It cannot
decide them by inspection. A valid responsibility fixture therefore requires
receipts for costs, threats, operator responses, third-party burden, and the
responsibility taxonomy being applied.

The unsafe shortcut is:

```text
because one operator is terminal-like or non-responsive,
actor X is formally the aggressor.
```

The safe statement is conditional:

```text
if taxonomy T defines aggression by non-responsiveness / cost conversion
and receipts emit the relevant atoms
then the model may emit an aggressor/responsibility label.
```

## Existential Fibre Fixtures

The engine should not collapse existential claims into economic or theological
claims. A model may introduce a separate existential fibre such as:

```text
agent: Actor
theme: PhysicalSurvival
evidence: ProximateWitness
```

`ProximateWitness` is a typed role, not a rhetorical upgrade. It requires
source-span provenance, witness or observation metadata, temporal status,
wrapper state, and validation rules before the emitted atom can be compared.
If those receipts exist, an existential atom can participate in trigger,
responsibility, or interaction-operator fixtures. If they do not, the analyst
cannot promote a live event description into `wrapper = asserted`,
`modality = actual`, or `present-continuous` by inspection.

A multi-domain interaction fixture can then be stated as:

```text
Theta_actor :
  S_economic x S_theological x S_existential -> S_epistemic
```

The ordering:

```text
existential > theological > economic
```

is not currently a law of `ResidualLevel`. It would be a warrant-ordering rule
over emitted domain receipts. The engine may carry that rule only as model
metadata until a checked carrier or theorem explains how it affects residual
comparison, trigger activation, or severity aggregation.

The unsafe shortcut is:

```text
because an existential fibre was named,
the actor has the most complete interaction operator.
```

The safe fixture is:

```text
if receipts emit economic, theological, and existential atoms
and model M defines Theta plus a warrant ordering
then the classifier may emit a triple-domain completeness hypothesis.
```

## Enemy-Classification Operator Fixtures

Enemy-classification claims require their own fixture surface. The engine may
compare two classifier shapes:

```text
K_lineage    : Person -> EnemyClass
K_behavioral : Action x Context -> EnemyClass
```

The first shape can model a projection over a fixed person or group attribute.
The second can model a behaviour-conditional classifier. Neither shape is
assigned to a named tradition by inspection. A valid fixture requires:

- textual/source-span receipts;
- translation or interpretive-profile metadata;
- a classifier-input taxonomy separating person, lineage, action, and context;
- a declassification, desistance, or peace-clause rule if invertibility is
  claimed;
- validation rules for the theological, legal, or scholarly domain being used.

The residual layer can then compare emitted classifier atoms and operator
metadata. It cannot infer that a scripture, slogan, or political phrase is
lineage-fixed, behaviour-conditional, invertible, or non-invertible without
that fixture.

The unsafe shortcut is:

```text
because source X mentions enemy Y,
K_X is a FascisticSystem or AntiFascistSystem operator.
```

The safe statement is:

```text
if textual receipts and taxonomy T emit K as behaviour-conditional
and T defines a desistance inverse
then the model may compare K with the invertible-operator fixture.
```

## Collapsed Quotient Fixtures

A one-output enemy classifier is not outside the engine. It can be modelled as
a collapsed quotient:

```text
L_source = neutral <= conditional-enemy <= active-enemy
L_target = enemy

q : L_source -> L_target
```

where `q` maps every source element to `enemy`. This is a valid quotient-style
fixture, but it is information-destroying: the inverse relation is not a
function unless the model supplies extra data to redifferentiate the source
states.

The residual consequence is also well-formed. If two emitted atoms live in
different typed lattice carriers and no comparison map has been supplied, the
comparison yields `noTypedMeet`; it does not become undefined:

```text
comparison(K_collapsed, K_source) = noTypedMeet
```

If a product lattice is supplied, comparison can continue in:

```text
L_source x L_target
```

but the collapsed coordinate remains fixed until the model supplies a lift.
Such a lift requires receipts and a rule; it is not the inverse of the quotient
by default.

The unsafe shortcut is:

```text
the collapsed operator breaks the algebra.
```

The safe statement is:

```text
the collapsed operator is well-formed in its own lattice;
cross-lattice comparison yields noTypedMeet unless a product/lift model exists.
```

## Two-Axis And Three-Body Lattice Fixtures

Some classifier models need two independent axes rather than one:

```text
L_two_axis = L_identity x L_conduct

atom signature =
  < identity : IdentityStatus, conduct : ConductStatus >
```

This shape can express that an identity/protection status and a conduct status
are compared separately. A collapsed classifier with only an identity role:

```text
< identity : CollapsedEnemyIdentity >
```

does not have the same signature arity. The residual layer can return
`noTypedMeet` unless the model supplies a projection, quotient, or product
carrier. Any projection that discards `conduct` must be recorded as
information-destroying.

A proposed lift from the collapsed carrier back to a two-axis carrier is also
model data:

```text
lift : L_collapsed -> L_identity x L_conduct
```

It requires rules and receipts for the restored conduct coordinate. It is not
a true inverse of the quotient by default.

The same principle scales to three components:

```text
L_3 = L_A x L_B x L_C
```

If `L_C` is a one-element collapsed lattice, the product still exists, but a
state or institutional decision may be dominated by `L_C` only if a decision
projection says so:

```text
Decision = Decision_C o pi_C
```

Decoupling means changing or validating the decision projection, for example by
using only a compatible subproduct:

```text
Decision = Decision_AB o pi_AB
```

The engine cannot infer this from historical analogy. It needs role-binding
taxonomies, component meet/join definitions, projection maps, decision-routing
rules, and validation.

The unsafe shortcut is:

```text
because two traditions have identity and conduct axes,
their product lattice has a proved political equilibrium.
```

The safe statement is:

```text
if model M emits compatible two-axis lattices and a decision projection,
then the engine may compare fixed-point candidates in the selected subproduct.
```

## Hostile-Provenance And Four-Body Fixtures

Historical theology examples require a source-critical wrapper layer before
they can be used as PNF atoms. The engine must distinguish:

```text
direct source
opponent report
later summary
modern diagram / infographic
```

An adversarial or heresiological source should emit wrapper and qualifier data
such as:

```text
wrapper = adversarial-report
qualifier = opponent-report / indirect / source-critical
```

not plain `asserted` doctrine. If no direct source exists for one side, the
comparison remains provenance-gapped; the engine may compare reports as
reports, but it cannot compute a direct meet with the absent original doctrine.

A four-body theology fixture can be represented as:

```text
L_4 = L_A x L_B x L_C x L_D
```

where `L_D` might be an emanation, ascent, escape, salvation, or restoration
carrier. The engine needs source receipts, role taxonomies, orientation maps,
and operator witnesses before it compares this component with the two-axis,
collapsed-quotient, Base369, or contraction fixtures.

The unsafe shortcut is:

```text
because a diagram maps a historical system to 365 heavens,
the repo has a CRT/JFixedPoint/operator-duality instance.
```

The safe statement is:

```text
if source-critical receipts emit the historical claims
and model M defines the four product carriers and orientation maps
then the engine may compare the fixture with cyclic or contraction surfaces.
```

`Ultrametric.agda` is not missing. What would be missing for this fixture is a
domain-specific metric over theological lattice morphisms, plus proofs that the
selected operators satisfy the required metric laws.

## Non-Abrahamic / N-Body Fixtures

The engine should not treat Hindu, Buddhist, Jain, or other non-Abrahamic
systems as simple extra points in the four-body product. Some comparative
fixtures change the carrier assumptions:

```text
identity-map carrier:
  K s = s

permanent-distance carrier:
  root and derived state remain distinct

telos-free action carrier:
  action is typed without an objective-result argument

process-only carrier:
  entity role bindings are replaced by dependent process relations

perspective-indexed carrier:
  every atom carries a required standpoint / perspective role
```

These are model shapes, not doctrinal classifications. A runtime or case-study
surface may emit them only after receipts identify the source span,
translation or interpretive profile, school/tradition boundary, role bindings,
and proposed morphism into or away from the PNF carrier.

The Buddhist-style process fixture needs special care. Ordinary PNF assumes
stable role bindings such as `agent` and `theme`. If a model claims those are
only conventional designations, the engine needs a typed translation from
entity atoms into process/relation atoms before residual comparison can run.
Without that translation, the result is not a mystical proof or a semantic
override; it is an unbuilt carrier bridge.

The Jain-style perspective fixture is also bounded. A required perspective
role can represent an absolute claim as "true from standpoint p", but that
does not make the claim exact against every other standpoint. The model must
define the perspective lattice and its meet/join rules.

The unsafe shortcut is:

```text
because a tradition has identity, emptiness, or perspective language,
the repo has proved a JFixedPoint, process-cessation, or universal-meet result.
```

The safe statement is:

```text
if source-critical receipts and model M define the school-level carrier,
role bindings, perspective/process/action semantics, and morphisms,
then the engine may compare those fixtures against PNF, residual, or
operator-class surfaces.
```

## East Asian / Indigenous Living-Lattice Fixtures

Some comparative fixtures change the topology more strongly than the
identity/process/perspective cases. The engine must treat these as separate
carrier models:

```text
carrier-substrate:
  the named subject is the carrier context, not an operator or atom

natural-flow:
  action follows a typed flow or least-forcing rule

relation-matrix:
  states are role/obligation matrices rather than entity atoms

immanent-node:
  sacred or divine presences are local nodes inside S

fully-connected relation graph:
  every node has a maintained relation to every other node

derivation graph:
  identity is a typed derivation or genealogy path

timeless bundle:
  material state is paired with a non-temporal layer and maintained by paths,
  ceremonies, songs, or other typed practices
```

The engine cannot infer any of those shapes from a tradition name or a
comparative summary. It needs source-critical receipts, interpretive profiles,
place and community provenance where applicable, restricted-knowledge flags
where applicable, carrier definitions, graph/bundle/flow laws, and a validation
standard.

This is also a cultural-governance boundary. Living traditions, place-based
knowledge, and sacred/restricted material must not be turned into open
engineering fixtures merely because they are useful analogies. A model may
record a public, permitted abstraction; it must not extract restricted
ceremonial, songline, genealogy, or place-specific knowledge into repo
artifacts without explicit authority.

The unsafe shortcut is:

```text
because a tradition names Tao, Li, kami, all relations, whakapapa, or Dreaming,
the repo has proved a carrier, graph, bundle, scan-order, or JFixedPoint
instance.
```

The safe statement is:

```text
if culturally governed receipts and model M define the topology-changing
carrier and its morphisms,
then the engine may compare the public fixture with DASHI carrier, graph,
bundle, or flow surfaces.
```

## Affective-State / Feelings-Wheel Fixtures

Emotion taxonomies and feelings wheels are admissible as personal-state test
fixtures only when the model separates taxonomy, measurement, labeling, and
clinical scope. A normalized fixture may include:

```text
emotion taxonomy:
  primary / secondary / tertiary labels, intensity, and specificity edges

tone carrier:
  low-cardinality pleasant / unpleasant / neutral style feeling-tone values

constructed-content carrier:
  named emotion, appraisal, memory, narrative, and context

labeling operator:
  observation -> candidate label(s), wrapper state, confidence, perspective

clinical carrier:
  diagnostic or trauma-related claim under a validated clinical taxonomy
```

The engine cannot infer those fields from a feelings-wheel diagram, meditation
forum, psychology blog, or analyst introspection. It needs a named wheel
version or emotion taxonomy, psychometric/clinical validation status,
contemplative-source profile where Buddhist or other practice terms are used,
subject/session receipts for any personal-state claim, and non-authority flags
for mental-health claims.

This boundary is especially important for trauma language. The engine may
record a model hypothesis such as "restricted affective label access" or
"threat-collapse hypothesis" only after the model supplies measurement and
clinical scope rules. It must not emit diagnosis, treatment guidance, or
claims about PTSD, healing, nervous-system state, or trauma recovery by
analogy to collapsed quotients or operator inverses.

The unsafe shortcut is:

```text
because a wheel has radial layers and named emotions,
the repo has proved Base369, Whakapapa, DharmaSystem, Amalek-collapse,
Mindfulness, Dreaming-layer, or JFixedPoint structure for a person.
```

The safe statement is:

```text
if a validated affective taxonomy and subject/session receipts exist,
then the engine may compare non-clinical labeling, tone-compression,
perspective-indexing, and collapse/lift hypotheses under explicit
clinical non-authority flags.
```

## Mathematical-Atlas / Higher-Structure Fixtures

Some proposed extensions are not new claim labels but new mathematical chart
languages. The engine may record them as promotion targets only when they name
their carriers, morphisms, laws, and validation surfaces.

The safe fixture families are:

```text
category / functor fixture:
  categories, objects, morphisms, functors, natural transformations,
  adjunction data, and preservation laws

topos / sevenfold-predication fixture:
  truth-value carrier, order, meet/join or Heyting operations,
  perspective or predication embedding, and comparison rules

HoTT / path-identity fixture:
  path types, composition, higher paths, and a translation from derivation
  or genealogy claims into path identity

ergodic / scan-order fixture:
  measure space, transformation, invariant-measure law, ergodicity predicate,
  and failure mode for cultural or data-loss claims

information-geometry / MDL fixture:
  statistical family, metric, objective, projection or geodesic rule,
  and model-selection validation

coinductive / non-well-founded fixture:
  guarded circular carrier, productivity rule, and termination or cessation
  predicate where claimed

tropical / degeneration fixture:
  valuation map, original carrier, tropical carrier, and lost-metric record

renormalization fixture:
  scale map, coarse-graining law, relevant / irrelevant / marginal criterion,
  and validation across scales

infinity-categorical fixture:
  objects, 1-morphisms, higher morphisms, equivalence notion,
  and terminal / contractible-object proof obligation
```

The engine must not infer these structures from a comparative essay, Reddit
thread, philosophical keyword, or analyst synthesis. A valid fixture requires
source receipts where interpretive content is involved, typed Agda or design
carriers where formal content is involved, explicit morphisms from existing
PNF/residual/operator surfaces, and a validation rule for any empirical or
live-world reading.

The unsafe shortcut is:

```text
because a mathematical literature exists for the analogy,
the repo already has a category, topos, HoTT, ergodic, information-geometric,
coinductive, tropical, RG, or infinity-categorical theorem.
```

The safe statement is:

```text
if a typed chart and morphism into existing receipt carriers exist,
then the engine may compare the chart as a higher-structure explanation.
```

## Cross-Scale Physics / Biology / Consciousness Fixtures

A cross-scale fixture is stricter than a higher-structure analogy. It claims
that an operator pattern survives transport across physical, biological,
neural, affective, social, or theological carriers. The engine may carry that
as a design target only after each level is typed and the scale maps are
explicit.

The safe fixture shape is:

```text
ScaleCarrier i:
  carrier, observable, law, evidence profile, and non-claim boundary

scaleMap i:
  ScaleCarrier i -> ScaleCarrier (i + 1)

preservation:
  which observable, operator law, metric, order, or residual feature survives
  the scaleMap
```

Candidate levels such as quantum Hilbert space, QFT/RG flow,
thermodynamic/free-energy systems, chemical phase transitions, DNA/epigenetic
carriers, predictive-processing neural models, autonomic-state taxonomies,
affective labeling models, IIT-style causal structures, and social/theological
classifiers each require different receipts and validation standards.

Body-brain-chemistry fixtures must be split into at least synaptic/electrical,
volume-transmission, endocrine/hormonal, and epigenetic or cultural propagation
carriers. Terms such as `GABA`, `glutamate`, `dopamine`, `serotonin`,
`norepinephrine`, `oxytocin`, `cortisol`, `insulin`, and `acetylcholine` are
not operator labels by themselves; they require receptor/context models,
biomarker measurement protocols, causal hypotheses, validation cohorts or
literature receipts, and clinical non-authority flags before they can support
any Base369, Dreaming, Whakapapa, Amalek, DharmaSystem, market, or therapeutic
claim.

The engine must not infer these bridges from shared words such as
`collapse`, `projection`, `unitary`, `free energy`, `phase transition`,
`eigenclass`, `epigenetic`, `predictive`, `polyvagal`, `Phi`, or
`consciousness`, or from shared biological roles such as inhibition,
excitation, prediction error, bonding, stress, metabolism, or attention. Those
terms are overloaded across disciplines.

The unsafe shortcut is:

```text
because two domains use the same mathematical word,
the repo has proved they instantiate the same DASHI operator.
```

The safe statement is:

```text
if typed scale carriers and preservation laws exist,
then the engine may compare scale-stability of a selected operator pattern.
```

## Relational Interaction Fixtures

Two-actor or two-institution questions require a different normalized surface
from internal state classification. The object is an interaction operator:

```text
D_pair : S_a x S_b -> S_a x S_b
```

with optional directed projections:

```text
D_a->b
D_b->a
```

The residual algebra can help build features for those directed traces, but it
does not by itself construct the product carrier, coupling metric, or
composition law. So a relational fixture may say:

```text
if receipts and a pair model emit D_pair
and if D_pair has the stated component laws
then the joint trace has the stated attractor hypothesis.
```

It must not say:

```text
one side was read as terminal by inspection, therefore no joint fixed point
exists.
```

That conclusion needs a theorem linking component non-contraction or terminal
exit to the specific joint operator. The same restriction applies to
operator-level formulas: a receipt for `f (f x) > f x` can be compared against
a pair model only after the model map says what `f`, `x`, and composition mean
on the product state.

## Conditional Trigger Fixtures

A terminal or non-convergent operator hypothesis may be conditional on a
trigger. The residual layer can support such a fixture only after the trigger
is represented as receipted PNF evidence:

```text
trigger =
  receipt a1 with qualifier q1
  and receipt a2 with qualifier q2
  and ...

operator mode =
  active when trigger holds
  latent when trigger is degraded or discharged
```

This is useful for modelling capability claims, because `potential` and
`actual` are different qualifier states. A model may compare potential and
actual claims as overlapping but not exact if the emitted fields say so. The
formalism must not assign those qualifiers by inspection.

The fixed-point claim also requires a model:

```text
if trigger is discharged
and if K_deactivated is a contraction on the stated carrier
then candidate fixed point s* is reachable.
```

Without the trigger semantics, carrier, metric, and convergence proof, a
statement such as "this Class C operator is really latent Class A" is only a
case-study hypothesis.

## Bot / Source Join-Domain Fixtures

The market-risk and causal-source readings may consume the same receipted
stream, but `same input stream` does not imply `same formal computation`.
The safe fixture shape is:

```text
Phi : Operator -> ObservableReceiptStream

bot fixture:
  Phi(D) -> candidate future-risk / attractor hypothesis

source fixture:
  Phi(D) -> candidate minimal-input-process hypothesis
```

Those fixtures meet exactly only if a model proves orbit-input bijectivity:

```text
feature orbit of Phi(D) uniquely determines the minimal operator
```

The residual layer does not provide that proof. Nor does the current Hecke PNF
adapter: it maps representation-layer defect classes into residual pressure,
but it does not construct a double-coset space of live operators or a canonical
representative theorem. Any use of "minimal operator", "canonical source", or
"same domain for trading and causal inference" is therefore a design
hypothesis until a typed observation map, minimality relation, and validation
surface exist.

This also blocks a tempting CRT/J shortcut. `CRTPeriod` proves periodicity; it
does not prove that the digit trace is injective within one period or that the
period is an empirical news/market horizon. `JFixedPoint` records the
moonshine scalar bridge; it does not turn novelty-rate collapse or
forced-stable counts into a trading signal or causal-source certificate.

## Global Phase-Space Fixtures

A claim that a local conflict, price shock, or epistemic event can push a
global system out of a dominant attractor is not a residual comparison by
itself. It is a phase-space model claim. The safe fixture shape is:

```text
S_global = S_economic x S_political x S_epistemic

Theta : S_economic x S_political -> S_epistemic

delta_s : perturbation in S_global
delta_s* : critical threshold
```

When a fixture separates theological and existential fibres, the carrier and
interaction operator must say so explicitly:

```text
S_global =
  S_economic x S_political x S_theological x S_existential x S_epistemic

Theta_actor :
  S_economic x S_theological x S_existential -> S_epistemic
```

The residual layer can help build receipted features for the corpus, but it
does not define the global carrier, the attractor basin, the threshold, or the
interaction operator. A global-bifurcation fixture may therefore say:

```text
if receipts and a model define S_global, Theta, basin(A), delta_s, delta_s*
and if delta_s exceeds delta_s*
then the model selects a candidate post-bifurcation attractor class.
```

It must not say:

```text
the analyst reads a live event as sufficient epistemic pressure and declares
the global attractor has shifted.
```

Similarly, labels such as "capitalist attractor", "socialist attractor",
"theological interaction operator", or "reactive nationalist operator" are
model labels until a taxonomy, receipts, carrier map, and validation standard
emit them. `s-mono` can support a monotone severity feature after mapping into
DASHI's carrier; it does not by itself prove a global Jacobian response, basin
exit, or political-economic phase transition.

## Compiled Residual Layer

Once receipted atoms exist, the Agda side is deterministic:

```text
receiptResidual r1 r2 =
  computeResidual (emittedAtom r1) (emittedAtom r2)
```

The comparison is fibred:

- cross-signature atoms collapse to `noTypedMeet`;
- same-signature atoms enter wrapper, qualifier, and role gates;
- wrapper mismatch blocks exactness;
- qualifier conflict inside one signature fibre yields `contradiction`;
- role overlap with compatible wrapper/qualifier can yield `exact` or
  `partial`, depending on the emitted fields.

The four-level residual carrier is:

```text
exact < partial < noTypedMeet < contradiction
```

The six-level refinement adds:

```text
underdetermined6
scopeExceeded6
```

`performativeEvidence` maps to `scopeExceeded6` only when the pipeline emits
that wrapper. The formalism does not assign it from surface reading.

## Trace Transitions

A corpus can also be studied as a sequence of receipted emissions:

```text
r0, r1, r2, ...
```

Examples include a claim moving from conditional/future framing to
asserted/present framing, or an unattributed statement becoming attributed
after a later response. These are transition hypotheses until the pipeline
emits receipts for each span.

The safe statement is:

```text
if receipts r0 and r1 exist
and the emitted atoms differ only in wrapper, qualifier, attribution, or role
binding,
then the trace has a typed transition that can be compared downstream.
```

The unsafe statement is:

```text
the analyst read the exchange and assigned the transition.
```

That shortcut is not permitted.

## Pressure Layer

`DASHI.Interop.ITIRJoinBridge` maps UFTC severity/code joins into
`DASHI.Pressure`.

`DASHI.Interop.SensibLawResidualLattice` proves:

- residual join idempotence;
- residual join commutativity;
- residual join associativity;
- least-upper-bound laws;
- residual join preservation into pressure.

So once a residual exists, aggregation is monotone: high-severity residuals
cannot be masked by joining them with lower-severity residuals.

## Logic Carrier Bridges

`Base369`, `LogicTlurey`, `DASHI.Algebra.TetralemmaBridge`, and
`DASHI.Algebra.SixfoldLogic` provide carrier alignments:

- `Base369` supplies cyclic carriers for `TriTruth`, `HexTruth`, and
  `NonaryTruth`; this is a formal cyclic-algebra surface, not a numerology
  surface;
- `TriTruth` embeds into the residual chain as
  `exact`, `partial`, and `noTypedMeet`;
- `contradiction` has no preimage in that tone embedding;
- `Stage` remains cyclic dynamics, while `ResidualLevel` remains a static join
  chain;
- `HexTruth` supports the six-level bridge through `Stage6`.

This means contradiction is a cross-claim comparison result, not something
generated by a single claim's internal stage tone.

The tempting long chain:

```text
Base369 -> LogicTlurey -> CRTPeriod/JFixedPoint
  -> operator duality -> Theta -> global attractor
```

is a design fixture, not a theorem-owned pipeline. The engine may only use it
after each lift is made explicit: carrier map, quotient or seam, dynamics
preservation, operator witness, and validation. In particular, the current
repo does not prove that `TriTruth` states are a named theological logic, that
`HexTruth` or `NonaryTruth` are actor-count semantics, that p47/p59/p71 are
theological/existential/economic fibres, or that `JFixedPoint` selects a live
global attractor.

## Hecke Adapter

`Ontology.Hecke.PNFResidualBridge` is a representation-layer adapter:

- quotient projection equality is a candidate-pool fibre;
- `stableDefect -> partial`;
- `illegalDefect -> contradiction`;
- `otherDefect -> noTypedMeet`;
- illegal defects preserve contradiction and critical pressure under residual
  joins.

This is not a runtime PNF theorem. It aligns Hecke quotient/fibre structure
with the residual-pressure carrier after both sides have typed evidence.

## CoreSpine And Operator Duality

The CoreSpine bridge is adjacent, not a runtime parser dependency:

- `Base369.TriTruth` connects to `DASHI.Algebra.Trit`;
- `TritCarrierBridge` lifts into `Vec Trit n`;
- `AgreementUltrametric` and `FascisticContractionInstance` expose contraction
  certificate surfaces;
- `CRTPeriod` / `JFixedPoint` scalar bridges are landed.

Important correction: `Ultrametric.agda` is present in the repo. The open
problem is not a missing ultrametric module. The open problem is providing
concrete descent / fixed-point certificates for specific endomaps, and
providing receipt-bearing consumers for PNF/residual evidence.

Operator-duality language is therefore allowed only as a typed analogy or as a
future instance target. A receipted expansive formula can motivate a proposed
instance such as:

```text
state carrier S
operator U : S -> S
observable H
evidence that H does not collapse under U
```

but the repo should not say that such an instance exists until those fields and
obligations are explicitly supplied.

## Case Studies

`Docs/PNFCaseStudiesWatergateIran.md` is a conditional-fixture note:

- Watergate-style examples are useful because closed archives can support
  source-span receipts.
- Iran-war rhetoric examples are useful because live claims stress wrapper
  discipline.
- Ghalibaf-formula and interview-denial examples are useful only as
  conditional trace fixtures: they stress already-formal inputs,
  qualifier/wrapper shifts, and attribution-by-response, but only after
  receipts exist.

Neither case assigns labels by hand. They are test surfaces for:

```text
run pipeline -> inspect emitted receipts -> compute residuals
```

## Non-Claims

- The repo does not currently import the live ITIR/SensibLaw runtime into Agda.
- The repo does not prove that a given sentence emits a specific PNF atom.
- The repo does not turn news text, historical prose, or analyst labels into
  theorem input.
- The Hecke adapter does not prove corpus saturation for a live text cluster
  without emitted receipts.
- The operator-duality / contraction language does not prove economic market
  expansion or convergence without a concrete model and certificate.
- The attractor/orbit classifier is not a trading bot, market predictor, or
  causal-source oracle. It is a receipt-gated hypothesis generator until
  external empirical and causal models are supplied.
- A formula treated as an operator-level sufficient statistic is a fixture for
  hypothesis compression, not a proof that any named real-world mechanism,
  beneficiary, period, or actor classification is true.
- A domain-incommensurability reading is not a truth claim about any named
  religion, law, actor, or market response. It is a conditional pattern that
  requires emitted domain receipts plus an explicit absence or failure of a
  measure bridge.
- An existential-fibre reading is not a truth claim about any named event,
  actor, or witness. It requires physical-survival witness receipts,
  provenance, temporal/wrapper/modality fields, and validation before it can
  affect trigger, responsibility, or completeness fixtures.
- A collapsed-quotient reading is not a claim that the formalism failed or
  that an operator exited the algebra. It is a conditional lattice-morphism
  fixture requiring quotient maps, lost-distinction records, product-lattice
  semantics, and any lift/redifferentiation rule.
- A non-Abrahamic or N-body comparative-lattice reading is not a claim that any
  named tradition has been classified as identity-map, permanent-distance,
  telos-free, process-dissolving, or perspective-indexed. Those claims require
  school-level source receipts, interpretive profiles, carrier definitions,
  role-binding or process translations, perspective rules where relevant, and
  validation.
- An East Asian or Indigenous living-lattice reading is not a claim that a
  named living tradition instantiates a DASHI carrier, graph, bundle,
  scan-order, metric, or fixed point. Substrate, natural-flow,
  relation-matrix, immanent-node, fully connected, derivation-graph, and
  timeless-bundle fixtures require culturally governed source receipts,
  place/community provenance where applicable, restricted-knowledge flags,
  topology-changing carrier definitions, typed morphisms, and validation.
- An affective-state or feelings-wheel reading is not a clinical claim,
  diagnosis, therapy model, or proof that a person has entered or exited any
  operator class. Emotion-wheel, vedana/sankhara, mindfulness, trauma-collapse,
  healing, high-Mana, Dreaming-centre, or personal-DASHI fixtures require a
  named taxonomy, subject/session receipts, psychometric or clinical
  validation status, contemplative-source profiles where relevant, typed
  affective carriers, and explicit mental-health non-authority flags.
- A mathematical-atlas or higher-structure reading is not a theorem that DASHI
  is already a category, topos, HoTT path space, ergodic system,
  information-geometric MDL manifold, coinductive hyperset, tropical
  degeneration, RG flow, or infinity-topos. Those readings require typed
  chart carriers, morphisms from existing PNF/residual/operator surfaces,
  preservation laws, and validation before any JFixedPoint, terminal-object,
  adjunction, subobject-classifier, path-identity, ergodicity,
  tropical-limit, or scale-relevance claim can be emitted.
- `DASHI.Physics.Closure.ClaimGovernancePromotionObligation` is the current
  W7 Agda intake for these guarded chart readings. It names the authority and
  validation receipts required for higher-structure, cross-scale, temporal,
  spacetime, neurochemical, and market lanes, but constructs no authority token
  and promotes no chart claim.
- A cross-scale physics / biology / consciousness reading is not a theorem
  that quantum measurement, vedana, projectors, unitaries, RG relevance,
  thermodynamic free energy, Landauer erasure, chemical phase transitions, DNA
  eigenclasses, epigenetic inheritance, predictive processing, DMN, amygdala,
  PFC, polyvagal states, GABA, glutamate, dopamine, serotonin,
  norepinephrine, oxytocin, cortisol, insulin, acetylcholine, IIT Phi,
  Indigenous relational cosmology, or `JFixedPoint` are one identical
  structure. Those readings require typed carriers at each scale, explicit
  scale maps, preservation laws, receptor/context models, measurement
  protocols, empirical validation, and clinical non-authority flags where
  neural, trauma, affective, endocrine, metabolic, or health-related claims are
  involved.
- A temporal-sheaf reading is not a theorem that a temporal qualifier turns the
  current PNF slice into a checked sheaf over Time, that `Overlap` is already a
  restriction map, that `MereViol` is already a sheaf non-gluability theorem,
  that exclusive properties are already line bundles, that `CRTPeriod` handles
  a changing time topology, that `JFixedPoint` is a branching/reset point of
  Time, or that `Ultrametric.agda` already supplies a metric over temporal
  sections. Those readings require typed Time, Interval, Property, Value,
  Section, and Global carriers; overlap/restriction/gluing laws;
  exclusivity-vs-multiplicity semantics; transition maps between pre/post
  temporal sheaves; a proof that the transition is not merely period
  recurrence; and a temporal section metric with validation.
- A spacetime-sheaf reading is not a theorem that temporal qualification plus
  mereological/location properties already forms a spacetime manifold, a
  3+1 decomposition, a Cauchy surface, a spacetime density matrix, a closed
  timelike-curve rejection theorem, or a GR-style singularity model. Those
  readings require typed Time and Space carriers, a mereological containment
  relation, sections over `(Time, Space)`, spatial-overlap laws, spacetime
  gluing laws, single-valued exclusive-property fibres at each coordinate,
  slice/delta/admissibility carriers for `S + delta -> S'`, validity
  preservation for evolution, pre/post spacetime sheaves for any claimed
  `JFixedPoint` transition, and an extension obstruction proving the transition
  is neither ordinary CRT recurrence nor merely temporal topology change.

## Promotion Gates

Promotion beyond `bridge/adapter` requires:

1. a runtime fixture that emits `PNFEmissionReceipt` values from canonical text;
2. a checked import or certificate format for those receipts;
3. a consumer theorem that names which DASHI proof surface receives the
   residual evidence;
4. preservation of parser profile, reducer profile, source span, wrapper state,
   structural signature fibre, residual level, and non-authority flags.
5. if domain incommensurability is promoted, either an explicit residual
   carrier extension or a separate typed metadata channel for failed
   cross-domain measure bridges.
6. if attractor/orbit classification is promoted, a checked feature extractor
   over receipts plus separate validation packs for trading or causal-source
   use cases.
7. if existential or multi-domain operator-completeness classification is
   promoted, physical-survival witness receipts, warrant-ordering rules, and a
   typed multi-domain interaction-operator carrier.
8. if collapsed-quotient classification is promoted, explicit quotient maps,
   lost-distinction records, product-lattice semantics, and lift semantics for
   any claimed redifferentiation.
9. if non-Abrahamic / N-body comparative-lattice classification is promoted,
   source-critical school receipts, carrier definitions for identity,
   distance, action, process, or perspective-indexed systems, typed
   translations into or away from PNF, and validation.
10. if East Asian / Indigenous living-lattice classification is promoted,
    culturally governed source receipts, place/community provenance where
    applicable, restricted-knowledge flags, topology-changing carrier
    definitions, graph/bundle/flow/relation laws, typed morphisms, and
    validation.
11. if affective-state / feelings-wheel classification is promoted, a named
    emotion taxonomy, subject/session receipt format, psychometric or clinical
    validation status, contemplative-source profiles where relevant, typed
    feeling-tone and labeling carriers, perspective/wrapper rules, and
    clinical non-authority flags.
12. if mathematical-atlas / higher-structure classification is promoted, typed
    category/topos/HoTT/ergodic/information-geometric/coinductive/tropical/RG
    or infinity-categorical chart interfaces, morphisms from receipted
    fixtures into those charts, preservation laws, and validation.
13. if cross-scale physics / biology / consciousness classification is
    promoted, typed carriers for each scale, explicit scale maps,
    observable-preservation laws, measurement protocols, empirical validation,
    and clinical non-authority flags for any neural, trauma, affective, or
    health-related claim.
14. if neurochemical / body-brain-chemistry classification is promoted, typed
    synaptic/electrical, volume-transmission, endocrine/hormonal, and
    epigenetic or cultural propagation carriers, receptor/context models,
    biomarker measurement protocols, causal hypotheses, validation cohorts or
    literature receipts, and clinical non-authority flags are required before
    neurotransmitter or hormone language can support operator-class, Base369,
    market, trauma, diagnosis, treatment, or therapeutic-process claims.
15. if temporal-sheaf classification is promoted, typed Time, Interval,
    Property, Value, Section, and Global carriers, overlap/restriction/gluing
    laws, `MereViol` or contradiction certificates, exclusive-property
    single-valued fibre laws, pre/post topology-transition sheaves,
    `JFixedPoint` transition semantics distinct from ordinary CRT recurrence,
    and a temporal section metric are required before the repo can treat
    temporal qualifiers as state-space dimensions rather than flat metadata.
16. if spacetime-sheaf classification is promoted, typed Time and Space
    carriers, a mereological containment relation, sections over
    `(Time, Space)`, spatial-overlap laws, spacetime compatibility/gluing
    laws, exclusive-property single-valuedness at each spacetime coordinate,
    slice/delta/admissibility carriers, Cauchy-style validity preservation,
    and pre/post spacetime transition or obstruction witnesses are required
    before the repo can treat the slice system as spacetime, 3+1 evolution,
    a spacetime density matrix, or a singularity/topology-change theorem.
