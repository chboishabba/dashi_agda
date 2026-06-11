# PNF Case Studies: Conditional Fixtures, Not Hand Labels

This note records two review-facing test patterns for the ITIR / PNF /
residual formalism. It corrects an important boundary error:

> Wrapper, qualifier, role, and signature labels are not assigned by human
> inspection. They are valid only when emitted by the parser / shared reducer /
> PNF promotion pipeline and carried by a receipt.

The examples below are therefore conditional fixtures. They say what the
formal residual layer does after receipted `PredicatePNF` atoms exist. They do
not predict which atoms the runtime pipeline will emit.

## Source Boundary

Watergate is useful as a closed-corpus pattern because evidence receipts can
point to a fixed archive of tapes, testimony, filings, and congressional
records.

The Iran-war example is live-corpus only. ABC reported on April 7, 2026 that
Trump made repeated and shifting public claims about the Iran war, including
many "won/defeated" declarations and inconsistent assistance/negotiation
postures. PBS / PolitiFact reported on April 9, 2026 that Trump and Hegseth
claimed U.S. victory while outside experts described unresolved strategic
setbacks and unclear objectives.

Those reports justify selecting candidate text spans for pipeline testing.
They do not justify assigning `WrapperState`, `QualifierState`, role bindings,
or residual levels by hand.

Sources:

- ABC, "Donald Trump's shifting rhetoric on Iran war works against his rapidly
  thinning credibility", April 7, 2026.
- PBS News / PolitiFact, "Fact-checking Trump and Hegseth's claims of U.S.
  'victory' in the Iran war", April 9, 2026.

## Receipt Discipline

`DASHI.Interop.SensibLawResidualLattice` now names this boundary explicitly:

```text
PNFEmissionReceipt =
  parserProfile
  reducerProfile
  sourceSpan
  emittedAtom : PredicatePNF
```

Residual comparison over real text must run through receipted atoms:

```text
receiptResidual r1 r2 =
  computeResidual (emittedAtom r1) (emittedAtom r2)
```

So the correct statement is:

```text
if the pipeline emits receipts r1 and r2
and their emitted atoms share a structural signature
and their emitted qualifier states conflict
then receiptResidual r1 r2 = contradiction
```

The formalism does not say, by itself, whether a Watergate sentence or an
Iran-war sentence will emit those atom fields.

## Closed-Corpus Fixture

Watergate exercises the high-integrity residual path only after citation and
pipeline emission.

Conditional examples:

- If two receipted atoms share a structural signature, have compatible wrappers,
  and overlap on roles, then the residual can become `exact` or `partial`
  depending on emitted qualifier and role agreement.
- If two receipted atoms share a structural signature and the emitted
  qualifiers conflict, then the residual is `contradiction`.
- If two receipted atoms are cross-signature, then the residual is
  `noTypedMeet` regardless of analyst expectations.

This is the non-saturated comparison regime only after receipts exist: new
receipts can still separate claim fibres.

## Live-Corpus Fixture

The Iran-war rhetoric example is useful because it stresses wrapper discipline.
It is not valid to read the surface text and assign `performativeEvidence` by
hand.

The correct conditional rule is:

```text
if the pipeline emits wrapper = performativeEvidence
then wrapperSixResidual performativeEvidence = scopeExceeded6
```

and:

```text
sameWrapper directEvidence performativeEvidence = false
```

This says a receipted performative wrapper cannot be treated as evidential
`exact` against direct evidence. It does not say that any named public claim
will necessarily be emitted as `performativeEvidence`; that is an empirical
property of `shared_reducer.py`, the parser profile, and the PNF promotion
rules.

Repeated spans can only be called a saturated performative fibre if the
pipeline emits receipts showing the same relevant fibre repeatedly. Without
those receipts, "saturation" is only a hypothesis for a test run.

## Already-Formal Claim Fixture

A formula embedded in a post or media artifact is not automatically a proved
model. It is an already-formal source span. The safe pipeline reading is:

```text
source formula span
  -> parser / reducer / formula-reader profile
  -> PNFEmissionReceipt or formula-side receipt
  -> deterministic comparison
```

Conditional examples:

- If the pipeline emits a formula receipt whose structure is an expansive
  operator claim, then it can be compared against receipted econometric or
  market-model atoms.
- If the pipeline emits only a performative or rhetorical wrapper, then the
  formula remains outside evidential exactness.
- If the pipeline emits a qualifier shift from conditional/future to
  asserted/present across two receipted spans, then that is a trace transition
  available for downstream comparison.

The system does not infer such fields merely from the presence of notation.
The source author may have written mathematics; DASHI still requires emitted
receipts before comparison.

### Operator Sufficient-Statistic Pattern

Some formula spans are best tested as operator-level fixtures rather than as
ordinary claims about one actor or event. For example, a formula receipt may
emit the shape:

```text
Delta condition holds -> f (f O) > f O
```

If that is what the formula-reader emits, the fixture says only this:

```text
the source span presents the operator as locally expansive at O
```

That emitted structure can compress multiple downstream causal hypotheses. A
corpus may contain competing explanations for why a stabilizing constraint was
absent: persuasion, structural capture, cognitive failure, external
beneficiary, or other mechanism. The operator-level formula does not choose
between them. It records the shared consequent that those hypotheses would have
to explain.

This is useful for testing the claim-comparison engine because it separates:

- the receipted operator property, which can be compared structurally;
- the unreceipted mechanism narratives, which remain hypotheses;
- the formal DASHI operator classes, which require their own model witnesses.

The unsafe shortcut is:

```text
the analyst treats the formula as a proof certificate for a real-world
AntiFascistSystem instance, market period, or actor classification.
```

A local expansive inequality is not enough for that. A concrete instance would
need a state carrier, operator, entropy observable, and evidence/certificates
for the relevant `AntiFascistSystem` obligations.

### Domain-Exit Deterrence Pattern

A stronger fixture arises when a formula is intended as a deterrent but another
receipted span places the decision objective outside the formula's cost domain.
The safe pattern is:

```text
receipt r_formula emits:
  local expansive economic-cost operator

receipt r_mandate emits:
  objective or utility in a different decision domain

no receipt/model emits:
  a positive measure bridge from the economic cost domain
  into the decision domain
```

If those antecedents are emitted, the formula can be studied as a diagnostic
or classifier rather than as a deterrent. It identifies a cost that would
matter only to agents whose objective function weights that cost. Competing
mechanism narratives then explain why the weight is absent or zero; the
formula does not choose among them.

This is not currently a compiled residual theorem. The four-level residual
chain has `noTypedMeet` for cross-signature failures. The six-level chain has
`scopeExceeded6` for typed material outside ordinary comparison scope. A
stronger `incommensurable` status, meaning "no common measure bridge was
emitted, so the comparison cannot be formed," remains an open design target.

The unsafe shortcut is:

```text
the analyst decides that a theological, ideological, legal, or political
domain has exited economic deterrence, then assigns incommensurability by
inspection.
```

That is not allowed. The corpus must emit the relevant domain receipts, and a
model must name the missing or failed measure bridge.

### Attractor / Orbit Classifier Pattern

The same case-study corpus can be used to test an attractor/orbit classifier,
but only after receipt emission. The safe pattern is:

```text
receipted corpus stream
  -> residual, wrapper, domain, and Hecke-feature traces
  -> candidate class label
```

Candidate labels such as convergent, orbiting, or terminal are model outputs,
not direct readings of the news. They may be useful for comparing a market-risk
model and a hidden-operator inference model because both consume the same
trace features. The difference is downstream validation:

- a trading model needs market data, backtesting, costs, risk limits, and
  compliance review;
- a causal-source model needs provenance, counterfactual tests, and a separate
  causal-inference standard.

The unsafe shortcut is:

```text
the analyst sees a repeated policy phrase or a stable domain and declares the
true causal source or a trade signal.
```

The fixture can test whether emitted receipts support such a hypothesis. It
does not produce the hypothesis by inspection.

### State-Operator Classification Fixture

A state-level political question is a stronger version of the hidden-operator
fixture. The safe case-study shape is:

```text
receipts for domain-specific state actions / statements
  -> per-domain residual, wrapper, domain, and Hecke-feature traces
  -> per-domain operator-class hypotheses
  -> optional composite-operator hypothesis
```

This fixture can test a claim such as:

```text
given these receipts and this taxonomy,
the legal-domain trace and territorial-domain trace have different
operator-class hypotheses.
```

It cannot directly answer:

```text
is this live state politically label L?
```

That political label is itself a PNF claim in a separate evidential or advocacy
domain. Comparing it to a formal operator trace requires a taxonomy receipt,
scope rules, source provenance, and a validation standard external to the
current Agda residual layer.

The naming collision around `FascisticSystem` is especially important here.
The Agda record denotes an entropy-collapsing projection toward a fixed
attractor. It is not, by itself, the political-science definition of fascism.
A receipted operator trace may overlap with a political-label claim, but the
residual is `exact` only if an explicit taxonomy and emitted fields make it
exact.

### Aggressor / Responsibility Fixture

An aggressor label is not a direct consequence of the attractor classifier.
The safe case-study shape is:

```text
receipts for action, threat, response, cost, and burden
  -> shared-fibre or cross-fibre responsibility taxonomy
  -> comparison under that taxonomy
  -> optional aggressor/responsibility label
```

This can test conditional statements such as:

```text
if the taxonomy requires shared response capacity
and if the model emits incommensurable interaction operators
then the ordinary aggressor/defender comparison is out of scope.
```

or:

```text
if a cross-fibre taxonomy defines responsibility by cost conversion
and if receipts emit that incoming costs are converted into mandate-strengthening
inputs rather than constraints
then the model may emit a responsibility label.
```

The fixture cannot assert by inspection that costs are irrelevant, converted
into justification, shifted to a third party, or accepted without consent.
Those are receipted model predicates, not analyst labels.

### Existential Fibre / Triple-Domain Fixture

An existential-domain fixture is distinct from the economic-cost and
theological-interpretation fixtures. The safe shape is:

```text
receipts for physical-survival witness claims
  -> existential-domain PNF atoms
  -> optional warrant-ordering rule across domains
  -> multi-domain interaction operator
  -> operator-completeness hypothesis
```

This can test conditional statements such as:

```text
if receipts emit economic, theological, and existential atoms
and if the model defines
  Theta : S_economic x S_theological x S_existential -> S_epistemic
then the case study may classify the trace as a triple-domain fixture.
```

The fixture cannot assert by inspection that any named live event has
`wrapper = asserted`, `modality = actual`, or `tense = present-continuous`.
It also cannot assert that existential evidence outranks theological or
economic evidence unless the model defines a warrant ordering and the receipts
emit the relevant atoms. `s-mono` can only aggregate severities after the
existential receipts and severity map exist.

### Enemy-Classification Operator Fixture

A theological or political enemy-classification fixture must say what the
classifier takes as input:

```text
textual / theological receipts
  -> classifier-input taxonomy
  -> K_lineage : Person -> EnemyClass
     or K_behavioral : Action x Context -> EnemyClass
  -> inverse / deactivation / peace-clause rule if claimed
  -> operator-class comparison hypothesis
```

This can test conditional statements such as:

```text
if receipts emit a behaviour-conditional classifier
and if the model defines desistance as an inverse or deactivation path
then the fixture may compare that classifier to an invertible operator model.
```

The fixture cannot assert by inspection that a named scripture, tradition, or
political phrase is lineage-fixed, behaviour-conditional, invertible, or
non-invertible. It also cannot derive a `Contraction` fixed point merely from
a claimed peace clause; the carrier, metric, and convergence theorem must be
supplied separately.

### Collapsed Quotient / Product-Lattice Fixture

A case study may model a terminal-looking classifier as a collapsed quotient
rather than as an undefined or out-of-formalism object:

```text
receipts for classifier atoms
  -> source lattice with distinctions
  -> collapsed quotient lattice
  -> quotient map q
  -> noTypedMeet or product-lattice comparison
  -> optional lift/redifferentiation hypothesis
```

This can test conditional statements such as:

```text
if q collapses neutral, conditional-enemy, and active-enemy to enemy
and if no lift map is supplied
then comparison against the uncollapsed lattice yields noTypedMeet
or a product-lattice state whose collapsed coordinate remains fixed.
```

The fixture cannot assert by inspection that a named operator has performed
that quotient, that the quotient is irreversible in the live world, or that
pressure has forced a lift. Those claims require receipts, quotient maps,
product-lattice semantics, and lift/redifferentiation rules.

### Two-Axis / Three-Body Lattice Fixture

A case study may also model protection, identity, conduct, and decision routing
as separate axes:

```text
receipts for legal / theological / political classifications
  -> identity-axis atoms
  -> conduct-axis atoms
  -> product lattice L_identity x L_conduct
  -> projection / quotient / lift maps
  -> state-decision projection
```

This can test conditional statements such as:

```text
if a model emits both identity and conduct role bindings
and if a collapsed classifier emits only identity
then direct comparison may yield noTypedMeet
unless a projection or product lattice is supplied.
```

For a three-component fixture:

```text
L_3 = L_A x L_B x L_C
```

the case study must also identify which projection drives decisions. A constant
third factor may remain present in the product while being politically
decoupled:

```text
Decision = Decision_AB o pi_AB
```

The fixture cannot assert that any named religious law, state, or historical
period instantiates the two-axis or three-body lattice by inspection. It also
cannot assert that separation of church and state is the inverse of a named
operator without a decision-projection model and validation.

### Hostile-Provenance / Four-Body Theology Fixture

A historical-theology diagram or infographic can be test data only after its
source status is represented. The safe shape is:

```text
historical source span or diagram node
  -> source-critical receipt
  -> wrapper / qualifier / witness profile
  -> claimed lattice or operator atom
  -> optional four-component product lattice
```

This can test conditional statements such as:

```text
if a source is an opponent report
then the emitted atom is about what the opponent reports,
not direct doctrine.
```

or:

```text
if a model defines L_4 = L_A x L_B x L_C x L_D
and supplies orientation maps for L_D
then the case study may compare four-body theological hypotheses.
```

The fixture cannot assert by inspection that a Basilides/Gnostic infographic
proves an emanation lattice, a CRT period, an Abraxas digit function,
`JFixedPoint`, `s-mono`, `AntiFascistSystem`, Sufi/Gnostic meet, or a current
conflict algebra. Those require source receipts, adversarial-witness
qualifiers, product-lattice maps, orientation maps, operator witnesses, and
validation.

### Non-Abrahamic / N-Body Comparative-Lattice Fixture

A case-study corpus may introduce Hindu, Buddhist, Jain, or other
non-Abrahamic systems only as source-critical, school-level fixtures. The safe
shape is:

```text
source span / school profile
  -> source-critical receipt
  -> candidate carrier kind
  -> role-binding, process, action, or perspective rules
  -> optional morphism into or away from PNF
```

Useful carrier kinds include:

```text
identity map: K s = s
permanent root/creature or root/world distance
telos-free action with no objective-result argument
process/relation carrier without stable entity bindings
perspective-indexed atoms with a required standpoint role
```

The fixture cannot assert by inspection that Advaita, Dvaita, Nishkama karma,
Buddhist anatta/sunyata, Madhyamaka catuskoti, Jain anekantavada, or any
other named school has a particular DASHI operator class. It also cannot assert
that process cessation is Class C, that perspective indexing computes all
otherwise missing meets, or that non-Abrahamic termini are the same as
`JFixedPoint`. Those require school-level source receipts, interpretive
profiles, carrier definitions, typed translations, meet/join rules, and
validation.

### East Asian / Indigenous Living-Lattice Fixture

A case-study corpus may introduce Taoist, Confucian, Shinto, Indigenous
American, Maori, Aboriginal Australian, or other living-lattice systems only as
public, culturally governed fixtures. The safe shape is:

```text
public source span / tradition profile
  -> culturally governed source-critical receipt
  -> candidate topology-changing carrier kind
  -> place/community/restricted-knowledge metadata where applicable
  -> relation, flow, graph, bundle, or derivation rules
  -> optional morphism into or away from DASHI carriers
```

Useful carrier kinds include:

```text
carrier-substrate context
natural-flow / least-forcing rule
relation-matrix over roles and obligations
immanent-node / local multi-attractor landscape
fully connected relation graph
derivation or genealogy graph
two-layer timeless bundle with maintenance paths
```

The fixture cannot assert by inspection that Tao is the DASHI carrier, wu wei
is gradient descent, Li is a `FascisticSystem`, kami are local attractors,
all-my-relations is a complete graph theorem, Whakapapa is prime
factorisation, mana is a metric, Dreaming is a fibre bundle or `JFixedPoint`,
songlines are scan orders, or cultural continuity is an empirical proof of
DASHI. Those require culturally appropriate source receipts, public/permitted
abstractions, carrier definitions, morphisms, and validation.

### Affective-State / Feelings-Wheel Fixture

A case-study corpus may introduce a feelings wheel, emotion taxonomy,
vedana/sankhara distinction, mindfulness-labelling claim, or trauma-collapse
hypothesis only as a non-clinical affective-state fixture. The safe shape is:

```text
emotion-taxonomy source / contemplative source / session observation
  -> source-critical or subject/session receipt
  -> tone, named-emotion, intensity, specificity, perspective, wrapper fields
  -> optional labeling or collapse/lift hypothesis
  -> explicit clinical non-authority flags
```

Useful carrier kinds include:

```text
radial emotion taxonomy over named labels
low-cardinality feeling-tone carrier
constructed emotional-content carrier
perspective-indexed labeling operator
restricted-label-access / collapse hypothesis
```

The fixture cannot assert by inspection that a feelings wheel is Whakapapa,
Base369, `DharmaSystem`, `FascisticSystem`, `AntiFascistSystem`, an
Amalek-collapse meter, a trauma diagnosis, a healing protocol, a high-Mana
metric, a Dreaming layer, or `JFixedPoint`. Those require a named taxonomy,
subject/session receipts where personal state is involved, psychometric or
clinical validation status, contemplative-source profiles where relevant,
typed affective carriers, and validation.

### Base369 Chain Fixture

The case-study corpus may also test whether an emitted operator can be lifted
into the repo's cyclic carrier chain:

```text
receipted operator / classifier atoms
  -> Base369 carrier map
  -> LogicTlurey or quotient/seam map
  -> CRT/J scalar bridge if relevant
  -> operator-class comparison hypothesis
  -> optional Theta / global-attractor model
```

This can test conditional statements such as:

```text
if model M maps K into TriTruth
and if K commutes with rotateTri
then K may be compared to the period-3 cyclic fixture.
```

The fixture cannot assert by inspection that a named political or theological
operator is in `Z/3Z`, `Z/6Z`, or `Z/9Z`, that a constant map is outside the
formalism, that p47/p59/p71 name live-world fibres, or that `JFixedPoint`
certifies a historical/global attractor. Those readings require model maps,
commutation or seam proofs, and validation.

### Relational Pair-Operator Fixture

A pairwise conflict or negotiation question is not the same as asking for each
actor's internal class. The fixture shape is:

```text
receipts from actor A and actor B
  -> directed residual / wrapper / domain / Hecke traces
  -> product carrier S_A x S_B
  -> interaction operator D_pair
  -> candidate joint-attractor hypothesis
```

This can test conditional statements such as:

```text
if D_A->B is modelled as responsive
and D_B->A is modelled as terminal
and the product coupling theorem says terminal components block contraction
then D_pair has no joint fixed point.
```

The fixture cannot skip the antecedents. It is unsafe to infer a joint
operator class from raw public claims, from a single formula span, or from
hand-labelled directed roles. A formula receipt shaped like `f (f O) > f O`
becomes a sufficient-statistic candidate for a pair only when a model maps
`f` to the interaction operator and supplies the joint metric/composition law.

### Conditional Trigger Fixture

A pairwise corpus can also test whether a terminal-looking operator is
actually a conditional response. The safe shape is:

```text
trigger receipts
  -> activation predicate
  -> active operator mode
  -> deactivation predicate
  -> latent fixed-point hypothesis
```

This can test conditional statements such as:

```text
if capability receipt a has modality = potential
and if actualization receipt b is absent
and if the model says the trigger requires actualization
then the terminal mode is not activated in that model.
```

The fixture cannot assert that any live nuclear, theological, recognition, or
statehood condition has that status by inspection. It also cannot assume that
a trigger is a three-way conjunction unless the model defines the conjunction
rule and the receipts emit all required atoms. A deactivated mode becomes a
contraction only after a carrier, metric, and convergence theorem are supplied.

### Bot / Causal-Source Join Fixture

A corpus can be used to test whether market-risk classification and
causal-source inference share a join domain, but the fixture must expose the
extra assumptions. The safe shape is:

```text
receipted observable stream
  -> feature/orbit trace
  -> bot-side attractor hypothesis
  -> source-side minimal-operator hypothesis
  -> optional join theorem if orbit-input bijectivity is proved
```

This fixture can test conditional statements such as:

```text
if Phi maps operators to receipt streams
and if the chosen feature orbit uniquely determines a minimal operator
then the bot-side and source-side PNFs can meet exactly in that model.
```

It cannot assert that the current Hecke adapter, CRT period, or J fixed-point
scalar already supplies that join. The digit periodicity theorem is a
recurrence fact, not an injective classifier horizon. The moonshine scalar
bridge is a formal arithmetic identity, not a market convergence certificate
or a causal-source theorem.

### Global Phase-Space Fixture

A corpus can also be used to test a global phase-space hypothesis, but this is
one level above the pair and join-domain fixtures. The safe shape is:

```text
receipts for economic, political, and epistemic spans
  -> global state feature record
  -> modelled interaction operator Theta
  -> perturbation delta_s and threshold delta_s*
  -> candidate basin / post-bifurcation attractor label
```

This can test conditional statements such as:

```text
if the model defines a dominant basin A_C
and if the emitted perturbation delta_s exceeds delta_s*
and if Theta maps that perturbation into the epistemic layer
then the model may emit a post-bifurcation attractor hypothesis.
```

The fixture cannot assert by inspection that a live oil shock, formula post,
religious framework, labour movement, nationalist reaction, or economic order
has the required model role. Those labels require receipts, a global carrier,
a basin metric, a perturbation threshold, and validation. A political-economic
phase diagram is a useful design surface; it is not a theorem until the model
objects exist.

## Attribution-By-Response Fixture

Interview exchanges can create an apparent promotion from unattributed or
inexpressible material into attributed material. This is useful as a test case
for the six-level residual carrier, but only conditionally.

The safe statement is:

```text
if receipt r0 emits an unattributed/reported atom
and receipt r1 emits a response atom with a self-attribution or denial wrapper
then the pair can be studied as a wrapper/attribution transition.
```

The unsafe statement is:

```text
the analyst decides that denial promoted attribution.
```

The latter is not a formal output. A transcript parser, reducer profile, and
source-span receipt must emit the relevant atoms first.

## Contrast

| Dimension | Closed corpus | Live rhetoric corpus | Already-formal / interview trace |
|---|---|---|---|
| Valid input | receipted PNF atoms over a fixed archive | receipted PNF atoms over live source spans | receipted formula/transcript atoms |
| Invalid shortcut | assigning `directEvidence` by historical intuition | assigning `performativeEvidence` by surface reading | assigning formula wrapper or attribution transition by analyst reading |
| Main gate | receipt first, then same-fibre residual comparison | receipt first, then wrapper pre-filter | receipt first, then trace comparison |
| Formal output | deterministic after emitted atoms exist | deterministic after emitted atoms exist | deterministic after emitted atoms exist |
| Open question | what the pipeline emits for each archival span | what the pipeline emits for each live span | what the pipeline emits for formula/transcript spans |

## Non-Claims

- This note does not adjudicate Watergate or Iran-war truth.
- This note does not assert that any news article is a theorem input.
- This note does not treat runtime PNF extraction as authoritative without
  receipts.
- This note does not assign wrapper, qualifier, role, signature, or residual
  labels by hand.
- This note does not assert that a formula post proves a market model.
- This note does not assert that a formula post proves a global period,
  `AntiFascistSystem` instance, or sufficient statistic for real events until
  formula-reader receipts and model certificates exist.
- This note does not assert domain incommensurability for any named law,
  religious framework, actor, or market response. That status requires
  receipted domain claims plus a model-level failed-measure-bridge certificate.
- This note does not assert existential-domain actuality, witness strength,
  warrant dominance, or triple-domain operator completeness for any named
  actor or event. Those claims require physical-survival witness receipts,
  provenance, temporal/wrapper/modality fields, and a typed multi-domain model.
- This note does not classify any named theological tradition, scripture, or
  enemy concept as lineage-fixed, behaviour-conditional, invertible, or
  non-invertible. Those claims require textual receipts, interpretive-profile
  metadata, classifier-input taxonomy, and inverse/deactivation semantics.
- This note does not treat a collapsed enemy-classifier as outside the
  formalism. A one-element or coarser quotient is a well-formed fixture, but
  quotient, product-lattice, `noTypedMeet`, and lift/redifferentiation claims
  require explicit maps, receipts, and validation.
- This note does not assert that any Dhimmi, Noahide, Torah, Sharia, Abrahamic,
  church/state, or three-body historical/legal/theological model has a
  specific lattice structure. Those claims require source receipts, role-axis
  taxonomies, product-lattice maps, decision-projection rules, and validation.
- This note does not assert Basilidean, Gnostic, Sufi, heresiological, or
  infographic claims as direct doctrine. Hostile-provenance and four-body
  theology fixtures require source-critical receipts, wrapper/qualifier
  profiles, orientation maps, product-lattice definitions, and validation.
- This note does not classify Advaita, Dvaita, Nishkama karma, Buddhist
  anatta/sunyata, Madhyamaka catuskoti, Jain anekantavada, or any other
  non-Abrahamic school as a DASHI operator class by inspection. N-body
  comparative-lattice fixtures require school-level source receipts,
  interpretive profiles, carrier definitions, role-binding or process
  translations, perspective rules where relevant, and validation.
- This note does not classify Taoist, Confucian, Shinto, Indigenous American,
  Maori, Aboriginal Australian, or other living-lattice traditions as DASHI
  carrier, graph, bundle, scan-order, metric, or fixed-point instances by
  inspection. Such fixtures require culturally governed public receipts,
  place/community provenance where applicable, restricted-knowledge flags,
  topology-changing carrier definitions, typed morphisms, and validation.
- This note does not classify a feelings wheel, vedana/sankhara distinction,
  mindfulness practice, trauma response, PTSD, emotional healing, or personal
  affective state as a DASHI operator-class instance by inspection. Such
  fixtures require a named affective taxonomy, subject/session receipts where
  personal state is involved, psychometric or clinical validation status,
  contemplative-source profiles where relevant, typed affective carriers, and
  explicit clinical non-authority flags.
- This note does not treat a mathematics-audit analogy as a repo theorem.
  Category-theory, Jain-topos, HoTT, ergodic, information-geometric,
  coinductive/non-well-founded, tropical, renormalization, or
  infinity-category readings require typed chart carriers, morphisms from
  receipted fixtures into those carriers, preservation laws, and validation
  before any adjunction, subobject-classifier, path-identity, scan-order,
  MDL-geodesic, hyperset, tropical-limit, scale-relevance, or terminal-object
  claim can be emitted.
- This note does not treat cross-scale physics, biology, neuroscience,
  affective, theological, or consciousness analogies as a proof that those
  domains instantiate one identical DASHI structure. Quantum collapse,
  projector/unitary language, RG relevance, free-energy minimization,
  Landauer erasure, phase-transition language, DNA eigenclasses, epigenetics,
  predictive processing, autonomic-state taxonomies, IIT Phi, and
  `JFixedPoint` require typed scale carriers, scale maps, preservation laws,
  measurement protocols, empirical validation, and clinical non-authority
  flags before any shared-operator claim can be emitted.
- This note does not treat `Base369`, `LogicTlurey`, `CRTPeriod`, or
  `JFixedPoint` as proving actor-count semantics, live-world fibre identities,
  strategy windows, resolution conditions, or global attractors. Those claims
  require typed carrier maps, commutation/seam proofs, operator witnesses, and
  validation.
- This note does not provide financial advice, a trading signal, a price floor,
  or a causal-source attribution. Attractor/orbit labels require receipted
  features and separate empirical or causal validation.
- This note does not assert attribution-by-denial unless transcript receipts
  emit the relevant atoms.
- The only formal promotion is conditional: once receipted atoms exist,
  residual comparison is deterministic and structure-preserving.
