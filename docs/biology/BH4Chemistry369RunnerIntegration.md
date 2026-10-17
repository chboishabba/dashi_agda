# BH4 chemistry / 369 / runner integration

## Current phase

PR #1159 is in **quantitative system-state / open-metabolic closure**.

Executed chemistry baseline (2026-10-17):

```text
16 exact UniProt proteins
  -> 24 protein/Rhea catalytic links
  -> 12 finite formula/charge reactions
  -> 3 explicit non-finite MTOR protein/R-group residual reactions
  -> 29 species x 12 reactions stoichiometric matrix S
  -> first 27-coordinate parameter template
  -> first S*v+e=0 attempt = underdetermined
```

The next-run quantitative problem is now explicit:

```text
15 core state/context coordinates
+ 12 REACTION_FLUX:<RHEA-ID> intervals
+ 29 EXCHANGE:<species-id> intervals
= 56 coordinates
```

## Exact finite reaction index

```text
RHEA:17473  GCH1
RHEA:22048  PTS
RHEA:32627  SPR
RHEA:18953  SPR
RHEA:11920  PCBD1
RHEA:17869  QDPR
RHEA:17865  QDPR
RHEA:20273  PAH
RHEA:18201  TH
RHEA:16709  TPH1 / TPH2
RHEA:19897  NOS1 / NOS2 / NOS3
RHEA:36255  AGMO
```

Explicit non-finite residuals:

```text
RHEA:10596  MTOR tyrosyl-[protein] kinase
RHEA:17989  MTOR seryl-[protein] kinase
RHEA:46608  MTOR threonyl-[protein] kinase
```

Residual reactions are acquired reaction identities, not zero columns.

## Existing DASHI machinery reused

The BH4 lane consumes the existing molecular stoichiometric conservation,
`OpenMetabolicNetwork`, metabolic stoichiometric conservation,
`MetabolicOpenSystemBalance`, atomic-generation obligation surface, 369
retained-carrier/refinement machinery, and the NONG/NANG NO-vs-N2O theorem.

The main anti-collapse laws remain:

```text
atomic inventory != solved molecular Hamiltonian
finite stoichiometry != quantitative physical chemistry
missing/incomplete reaction != zero stoichiometric column
internal reaction != environmental/compartment exchange
unresolved parameter != measured zero
same molecule in two compartments != one state
same variable at two times != one same-time state
kinetic constant != in-vivo flux bound
SIFTS mapping != catalytic mechanism
NO != N2O
chemistry != literally 369
feasible steady state != allocator causality
a whole-system balance != disease mechanism
```

## Quantitative acquisition and solving

Full runbook:

```text
docs/biology/BH4Phase4QuantitativeRunbook.md
```

One-command execution:

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

The runner:

1. refreshes Rhea/ChEBI chemistry from the exact UniProt panel;
2. rebuilds the deterministic finite matrix `S`;
3. generates the 56-coordinate quantitative template;
4. acquires SABIO-RK kinetic-law candidates by exact UniProt accession;
5. acquires bounded PDBe/SIFTS UniProt/PDB segment mappings;
6. runs interval steady-state feasibility;
7. runs the aggregate evidence/identity/chemistry/Phase-4 static regressions.

A source-paid manifest can be supplied with:

```bash
python3 scripts/run_bh4_phase4_maxcut.py \
  --manifest artifacts/biology/bh4-parameter-paid.json
```

The interval solver searches:

```text
S*v + e = 0
```

with source-paid lower/upper bounds on every reaction flux and every species
exchange coordinate. It uses `scipy.optimize.linprog(method="highs")` only after
all required bounds are marked usable for the joint witness.

Possible outcomes:

```text
feasible
infeasible
underdetermined
solver-unavailable
```

Missing reaction or exchange intervals are never silently replaced by zero or
infinity.

## Evidence lanes

`BH4QuantitativeAcquisitionExact` owns the SABIO/PDBe/SIFTS promotion boundary.
SABIO entries may provide Km, kcat, Vmax, rate laws and experimental context,
but those remain candidate evidence until translated into an explicitly sourced,
compartment/time/same-object flux interval. PDBe/SIFTS pays structure/sequence
mapping, not catalytic function or perturbational causality.

`BH4IntervalFluxSolverExact` owns the interval-feasibility boundary. A feasible
steady-state witness establishes consistency of the supplied intervals only. An
infeasible bounded steady-state problem does not rule out time-varying dynamics
or a different state space.

## Current live frontier

```text
resolve the three non-finite MTOR protein/R-group reaction representations where needed
execute/adjudicate SABIO kinetic candidate evidence
execute/adjudicate PDBe/SIFTS residue/site evidence
pay 12 reaction-specific flux intervals
pay 29 species-specific external-exchange intervals
pay compartment-specific BH4/BH2/redox state
pay simultaneous AAAH/NOS/AGMO demand
pay isoform-specific NOS coupling transitions
pay same-object upstream NOS -> TSC2 transport
discriminate alternative mechanisms
```

Identity, finite chemistry, quantitative state, transport, causality and clinical
authority remain independent payment layers.
