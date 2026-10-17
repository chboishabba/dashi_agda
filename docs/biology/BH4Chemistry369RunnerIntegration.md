# BH4 chemistry / 369 / runner integration

## Status after PR #1159 max-cut

This tranche moves the BH4 lane from external protein/database identity into a
literal, executable biochemical path and then generalises the acquisition and
finite stoichiometry runner across every Rhea cross-reference already carried
by the exact 16-protein UniProt panel.

The bounded path is now:

```text
exact UniProt protein panel
  -> exact Rhea cross-references
  -> Rhea REST equation/row receipts
  -> Rhea RDF substrates/products + coefficients
  -> ChEBI identity/formula/charge coordinates
  -> finite formula/charge audit where structurally representable
  -> atomic/369 refinement adapter
  -> executable stoichiometric/topological runner
  -> BH4SystemState / BH4SystemPayment
  -> existing CrossScaleMatterPhysics and
     PhysicsChemistryBiologyDNAUnificationDischarge parents
```

## Exact QDPR reaction

Rhea release 142 (2026-09-02; SPARQL release label `2026_03`) records the
specific directed child:

```text
RHEA:32253
(6R)-L-erythro-6,7-dihydrobiopterin + NADH + H+
  => (6R)-L-erythro-5,6,7,8-tetrahydrobiopterin + NAD+
```

Exact reaction microspecies:

| side | ChEBI | formula | charge |
|---|---|---:|---:|
| substrate | CHEBI:43120 | C9H13N5O3 | 0 |
| substrate | CHEBI:57945 | C21H27N7O14P2 | -2 |
| substrate | CHEBI:15378 | H | +1 |
| product | CHEBI:59560 | C9H15N5O3 | 0 |
| product | CHEBI:57540 | C21H26N7O14P2 | -1 |

The broader tetrahydrobiopterin ontology coordinate `CHEBI:15372` is retained
separately from the exact Rhea microspecies `CHEBI:59560`.

Both sides reduce to:

```text
C30 H41 N12 O17 P2 ; net charge -1
```

so the finite atom-count and net-charge witness is definitional in
`BH4MolecularStoichiometryExact`.

## Existing DASHI machinery reused

`BH4MolecularStoichiometryExact` imports the existing
`MolecularStoichiometricConservation` owner. The QDPR witness supplies the
concrete finite inventory; the generic owner remains responsible for the
abstract reaction-event/path conservation interface.

`BH4Atomic369RefinementExact` consumes:

- `AtomicGenerationPipelineExact` for the atomic obligation boundary;
- `PNFHyperfabric369` for the existing nonary address/refinement receipt;
- `ArgumentLevelTransportHyperformalismExact` for retained-carrier level
  transport semantics;
- `NonginNangNitrogenOxideRefinementExact` literally, reusing the theorem that
  a coarse nitrogen-oxide observer cannot serve a consumer requiring the
  NO-versus-N2O frame.

The adapter explicitly proves/records:

```text
atomic inventory != solved molecular Hamiltonian
finite stoichiometry != quantitative chemistry
coarse BH4 availability != fine compartment/redox state
coarse nitrogen oxide != recoverable NO/N2O state
chemistry != literally 369
shared refinement shape != shared domain semantics
```

## Acquisition commands

Exact QDPR reaction:

```bash
python3 scripts/acquire_rhea_chebi_bh4_reactions.py --qdpr \
  -o artifacts/biology/rhea-chebi-qdpr.json
```

All Rhea cross-references already present in the exact 16-member UniProt panel:

```bash
python3 scripts/acquire_rhea_chebi_bh4_reactions.py \
  --from-uniprot-panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  -o artifacts/biology/rhea-chebi-kitzerow-bh4-panel.json
```

The panel mode inherits protein/accession membership from the acquired UniProt
certificate rather than maintaining a second hand-written panel. For each
unique Rhea ID it records both the REST row/raw SHA-256 and an RDF/SPARQL
participant receipt containing:

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

Rhea compounds involving polymers, macromolecules, undefined R groups, missing
formulae, non-integer coefficients, or otherwise incomplete finite formula
coordinates remain explicit `formula_charge_residual_reactions`; they are not
silently forced through the finite molecular-formula parser.

## Runner

Exact QDPR fixture:

```bash
python3 scripts/run_bh4_reaction_network.py --qdpr \
  --output-prefix artifacts/biology/bh4-qdpr-network
```

Panel certificate:

```bash
python3 scripts/run_bh4_reaction_network.py \
  --certificate artifacts/biology/rhea-chebi-kitzerow-bh4-panel.json \
  --output-prefix artifacts/biology/bh4-panel-network
```

The panel runner multiplies participant formula/charge inventories by the
Rhea stoichiometric coefficients. It independently audits every finite
formula/charge-ready reaction and reports unsupported/polymeric/R-group cases
as finite-formula residuals. A database `isChemicallyBalanced` assertion and an
independently reconstructed finite balance remain distinct receipts.

Both modes emit JSON, CSV and Markdown receipts and always leave these false
unless a future source-specific adapter pays them:

```text
kinetics_supplied = false
compartment_state_supplied = false
measured_flux_promoted = false
disease_mechanism_promoted = false
```

The formal runner receipt projects the QDPR exact slice into `BH4SystemState`
with `participantIdentityPaid=true` and `reactionIdentityPaid=true`, while
`wholeSystemFluxMeasured=false`, transport/consumer-flux payment false and
allocator causality false.

## Unified cross-scale integration

`BH4BiochemicalCrossScaleAdapter` is a bounded instance of the existing DASHI
cross-scale parent. It connects the literal chemistry/runner slice to
`CrossScaleMatterPhysics` and `PhysicsChemistryBiologyDNAUnificationDischarge`
without changing their claim strength.

Current paid path:

```text
atomic inventory
  -> molecular reaction stoichiometry
  -> biochemical reaction-network receipt
  -> BH4 system payment
```

Current unpaid continuation:

```text
molecular Hamiltonian / quantitative physical chemistry
kinetic constants
compartment-specific BH4/BH2 amounts
simultaneous enzyme demand
transport and oxidation flux
NOS coupling transitions
same-object upstream -> TSC2 transport
cell-state prediction
whole-system FluxBalanceWitness
alternative-mechanism discrimination
disease causation / clinical prediction
```

## Next max-cut

The architecture and generic acquisition/runner machinery are no longer the
blocker. Run the panel Rhea acquisition to determine the exact reaction set and
which reactions are finite-formula-auditable, then promote the successful
reaction-specific receipts into Agda owners for GCH1/PTS/SPR/PCBD1,
PAH/TH/TPH1/TPH2, NOS1/2/3 and AGMO. After those isolated chemical rewrites are
paid, the scientifically meaningful frontier is quantitative: one shared
compartment/redox state, kinetic/transport parameters and a joint
`FluxBalanceWitness`, not additional ontology work.
