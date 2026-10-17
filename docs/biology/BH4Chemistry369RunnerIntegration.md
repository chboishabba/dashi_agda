# BH4 chemistry / 369 / runner integration

## Current phase

PR #1159 has moved beyond identity/provenance and the first literal reaction.
The current phase is **quantitative system-state / open-metabolic closure**.

The bounded DASHI path is now:

```text
exact UniProt protein panel
  -> exact Rhea cross-references
  -> Rhea/ChEBI reaction participants + coefficients + formula/charge
  -> finite molecular reaction audits
  -> deterministic species x reaction stoichiometric matrix S
  -> interval/source/compartment/time parameter coordinates
  -> explicit environmental/compartment exchange vector e
  -> candidate witness check S v + e = 0
  -> BH4SystemState / FluxBalanceWitness boundary
  -> isoform-specific NOS coupling / product-state boundary
  -> existing CrossScaleMatterPhysics and biology-discharge parents
```

Identity, reaction identity, finite stoichiometry, quantitative state, transport,
causality and clinical authority remain separate coordinates.

## Exact QDPR anchor

The first fully literal path remains:

```text
QDPR / UniProt P09417
  -> RHEA:17869 generic reaction
  -> RHEA:17871 directed generic child
  -> RHEA:32253 specific BH4 reaction
```

with:

```text
(6R)-L-erythro-6,7-dihydrobiopterin + NADH + H+
  => (6R)-L-erythro-5,6,7,8-tetrahydrobiopterin + NAD+
```

Specific reaction microspecies:

| side | ChEBI | formula | charge |
|---|---|---:|---:|
| substrate | CHEBI:43120 | C9H13N5O3 | 0 |
| substrate | CHEBI:57945 | C21H27N7O14P2 | -2 |
| substrate | CHEBI:15378 | H | +1 |
| product | CHEBI:59560 | C9H15N5O3 | 0 |
| product | CHEBI:57540 | C21H26N7O14P2 | -1 |

The broader tetrahydrobiopterin ontology coordinate `CHEBI:15372` remains
separate from the exact reaction microspecies `CHEBI:59560`.

Both sides reduce to:

```text
C30 H41 N12 O17 P2 ; net charge -1
```

so the QDPR atom-count/net-charge witness is definitional in
`BH4MolecularStoichiometryExact`.

## Existing DASHI machinery reused

The BH4 lane does not introduce a parallel metabolic theory.

It consumes:

- `MolecularStoichiometricConservation` for exact reaction/path conservation;
- `OpenMetabolicNetwork` for reaction, state, environment and flux carriers;
- `MetabolicStoichiometricConservation` for network-level internal reaction
  conservation;
- `MetabolicOpenSystemBalance` for the exact separation between internal
  reaction increments and environmental exchange increments;
- `AtomicGenerationPipelineExact` for the atomic/electronic obligation boundary;
- `PNFHyperfabric369` and argument-level transport for retained-carrier
  coarse/fine refinement;
- `NonginNangNitrogenOxideRefinementExact` for the literal theorem that a coarse
  nitrogen-oxide observer cannot serve a consumer that needs the NO/N2O frame.

The resulting anti-collapse laws include:

```text
atomic inventory != solved molecular Hamiltonian
finite stoichiometry != quantitative physical chemistry
Rhea balanced != independently finite-formula reconstructed
missing/incomplete reaction != zero stoichiometric column
internal reaction != compartment/environmental exchange
unresolved parameter != measured zero
same molecule in two compartments != one state
same variable at two times != one same-time state
coarse BH4 availability != BH4/BH2/redox/occupancy/flux state
NO != N2O
chemistry != literally 369
feasible flux candidate != allocator causality
a whole-system balance != disease mechanism
```

## Panel reaction acquisition

The already-acquired 16-member UniProt certificate is the sole panel-membership
source. No second hand-written reaction panel is maintained.

```bash
python3 scripts/acquire_rhea_chebi_bh4_reactions.py \
  --from-uniprot-panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  -o artifacts/biology/rhea-chebi-kitzerow-bh4-panel.json
```

For each unique Rhea ID the certificate records the REST row/raw digest and an
RDF/SPARQL participant receipt with:

```text
substrate/product side
stoichiometric coefficient
Rhea participant and compound URI
ChEBI identifier when present
compound name
formula
charge
SPARQL response SHA-256
```

Polymeric/macromolecular/R-group/incomplete-formula reactions remain explicit
finite-formula residuals.

## Canonical stoichiometric matrix

`build_bh4_stoichiometric_matrix.py` converts every finite formula/charge-ready
reaction into one deterministic signed reaction column.

```bash
python3 scripts/build_bh4_stoichiometric_matrix.py \
  artifacts/biology/rhea-chebi-kitzerow-bh4-panel.json \
  --output-prefix artifacts/biology/bh4-stoichiometric-matrix
```

The result contains:

```text
species_index
reaction_index
matrix                # signed stoichiometric coefficients
columns               # sparse human-readable form
finite_formula_residuals
external_exchange=[]  # deliberately not folded into S
```

A reaction lacking a finite structural receipt is absent from `S` and present in
`finite_formula_residuals`; it is never represented as a fake all-zero column.

`BH4PanelStoichiometricMatrixExact` is the formal owner for this contract.

## Quantitative parameter coordinates

`BH4CompartmentKineticStateExact` replaces the old implicit idea of a single
number per pathway with interval-valued evidence coordinates carrying:

```text
payment status: measured | derived | bounded-literature | unresolved
lower/upper bound
unit / scale
source
same-object reference
compartment
measurement time
method
direct-measurement flag
usable-for-joint-flux-witness flag
```

Generate a fail-closed template from the concrete matrix:

```bash
python3 scripts/acquire_bh4_parameter_evidence.py \
  --template \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-parameter-template.json
```

This automatically adds `REACTION_FLUX:<RHEA-ID>` coordinates for every matrix
column. An unresolved coordinate has `lower=null`, `upper=null` and is not
usable for a joint flux witness. It is not zero.

A populated manifest can then be normalized:

```bash
python3 scripts/acquire_bh4_parameter_evidence.py \
  --manifest artifacts/biology/bh4-parameter-input.json \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-parameters.json
```

Paid values require source, same-object, compartment and measurement-time
coordinates in addition to numeric bounds and units.

## NOS coupling: what is now paid

`BH4NOSCouplingEvidenceExact` adds bounded primary-source evidence for the
NOS3/eNOS lane:

- Crabtree et al., JBC 2009, DOI `10.1074/jbc.M805403200`, PMID `19011239`;
- Crabtree et al., JBC 2009, DOI `10.1074/jbc.M109.041483`, PMID `19666465`.

The first separates BH4 relative to eNOS protein and BH4:BH2 redox status as
coupling coordinates. The second uses DHFR perturbation and observes lower BH4
relative to BH2 together with reduced NO and increased eNOS-dependent superoxide
in the studied systems.

This pays **bounded NOS3/eNOS coupling support and perturbational support**.
It does not yet pay:

```text
same single-cell / same-time BH4/BH2 + NOS state
complete compartment identity
reaction flux
all required substrates/oxygen in one state
NOS1 or NOS2 generalisation
upstream BH4/NOS -> TSC2 same-object transport
Kitzerow disease mechanism
```

`BH4NOSCouplingSameObjectExact` makes that distinction explicit.

## Joint flux witness checker

The Phase-4 runner checks a supplied candidate rather than pretending to solve
an unconstrained biochemical optimisation problem.

Candidate shape:

```json
{
  "reaction_flux": {
    "RHEA:...": 1.0
  },
  "external_exchange": {
    "CHEBI:...": 0.0
  },
  "same_state_reference": "...",
  "measurement_reference": "..."
}
```

Run:

```bash
python3 scripts/run_bh4_flux_feasibility.py \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  --parameters artifacts/biology/bh4-parameters.json \
  --candidate artifacts/biology/bh4-flux-candidate.json \
  --output-prefix artifacts/biology/bh4-flux-feasibility
```

The status is one of:

```text
feasible        complete supplied candidate is inside paid bounds and S*v+e=0
infeasible      this complete supplied candidate violates bounds or balance
underdetermined required bounds / fluxes / exchanges are missing
```

`infeasible` is intentionally candidate-relative; it does not prove that no
other feasible state exists.

A `candidate_flux_balance_witness` is emitted only for a complete balanced
candidate.

## First whole-system attempt

The formal Phase-4 roadmap records:

```text
wholeSystemFluxBalanceAttempted = true
firstJointFluxOutcome = underdetermined
```

This is a substantive result. The blocker is no longer undefined architecture.
The remaining missing coordinates are named:

```text
complete panel reaction acquisition/promotion
reaction-specific quantitative flux bounds
compartment-specific BH4/BH2/redox state
simultaneous AAAH/NOS/AGMO demand
transport/oxidation external exchange vector
isoform-specific NOS transitions beyond bounded NOS3 evidence
same-object upstream NOS -> TSC2 transport
PDB/SIFTS residue/site witnesses where mechanistically needed
alternative-mechanism discrimination
```

`BH4Phase4RoadmapExact` is the current roadmap owner.

## Open metabolic integration

`BH4OpenMetabolicNetworkAdapterExact` explicitly consumes the existing DASHI
open-system owners. Its central decomposition is:

```text
internal biochemical reactions -> S
transport / uptake / export / oxidation -> external exchange e
```

so the quantitative target is:

```text
S v + e = d x / d t
```

and a steady-state witness is the special case:

```text
S v + e = 0
```

The current interface is present but the concrete quantitative open-network
instance remains unpaid until the source-specific parameter and exchange
coordinates are populated.

## 369 / atomics / unified integration

369 remains a refinement/observer grammar, not a chemical force law. The BH4
object now moves through exact observation levels:

```text
atomic inventory
  -> molecular reaction
  -> reaction network
  -> coarse BH4 availability
  -> fine BH4/BH2/redox/compartment/flux state
  -> cell/open-system observation
```

while retaining provenance and residuals at every projection.

The end-to-end focused root is:

```text
DASHI/Unified/BH4BiochemicalEverything.agda
```

and the Phase-4 regression is:

```bash
python3 scripts/check_bh4_phase4_system_state.py
```

## Phase exit

Phase 4 exits only when enough source-specific coordinates are paid to construct
at least one meaningful joint state and challenge it against the full admitted
network.

A feasible state would establish consistency of the paid constraints, not the
Kitzerow mechanism. An infeasible state would only falsify that candidate unless
an exhaustive/convex feasibility theorem is separately supplied. An
underdetermined state proves neither truth nor falsity.

Only after this quantitative phase should the roadmap move to mechanistic
alternative discrimination, intervention/temporal causality and, separately,
clinical validity.
