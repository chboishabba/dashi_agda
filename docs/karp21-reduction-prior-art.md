# Karp's 21 NP-complete problems: proof-ownership and reduction plan

## Historical provenance
- Stephen Cook (1971), *The Complexity of Theorem-Proving Procedures*, DOI 10.1145/800157.805047: original SAT complexity root.
- Richard Karp (1972), *Reducibility Among Combinatorial Problems*, DOI 10.1007/978-1-4684-2001-2_9: the original 21-problem reduction network.
- DASHI's own generic proof owner is `DASHI/Mathematics/Complexity/PolynomialReductionExact.agda`. The derived transport owner is `Karp21ReductionTransportExact.agda`.

## What is actually proved in this tranche
Given a shared encoded word carrier, polynomial-time-map composition, an NP-hard or NP-complete source and a **supplied** reduction to a target, transport NP-hardness; with target membership in NP, transport NP-completeness. This is proof composition, not a construction of any particular Karp reduction. No claim of local kernel acceptance or executed CI is made until compiled.

## Historical reduction graph (arrows mean polynomial many-one reducibility)
- SAT -> 0-1 integer programming; clique; SAT with at most 3 literals per clause.
- Clique -> set packing; vertex cover.
- Vertex cover -> set covering; feedback vertex set; feedback arc set; directed Hamiltonian cycle.
- Directed Hamiltonian cycle -> undirected Hamiltonian cycle.
- 3-SAT -> chromatic number.
- Chromatic number -> clique cover; exact cover.
- Exact cover -> hitting set; Steiner tree; 3-dimensional matching; knapsack (Karp's subset-sum-like variant).
- Knapsack -> sequencing; partition.
- Partition -> max cut.

The graph is the historical source diagram. Validate individual transformations against Karp's original definitions before turning each edge into a theorem. Do not infer the proof of any edge merely from the presence of these names.

## Required concrete interfaces
1. Heterogeneous polynomial reductions: source and target encoded instance types can differ. Encode both into a common bitstring or prove an explicit polynomial encoding/decoding bridge. No silent assumption that polynomial execution follows from definability.
2. For every node: precise decision predicate; bounded certificate, certificate verifier, size bound, and polynomial verification proof.
3. For every edge: executable transformation, forward/backward membership equivalence, explicit cost bound with bit-length accounting, and local witnesses.
4. Compose verified edges with `transportNPComplete`; record the precise upstream edge attribution and DASHI proof module ownership separately.
5. SAT root: connect the concrete SAT certificate representation to the existing `CookLevinCircuitGCTBoundary` literal BooleanFormula carrier; an abstract `satNPComplete` *field* in `PNotEqualsNPClayCoreExact` is an assumption, not the Cook-Levin proof.

## Highest-reuse edges / roadmap
- **K00**: heterogeneous encoded reductions and cost-model bridge (or explicit common-word encoding).
- **K01**: CNF SAT and 3-SAT certificates and truth-preserving clause gadgets.
- **K02**: 3-SAT -> CLIQUE and CLIQUE -> VERTEX COVER (finite graph complement, compatible literals).
- **K03**: CLIQUE -> SET PACKING; VERTEX COVER -> SET COVER (finite set incidence).
- **K04**: 3-SAT -> CHROMATIC NUMBER and the EXACT COVER/3-DIMENSIONAL MATCHING cluster.
- **K05**: EXACT COVER -> Karp KNAPSACK -> PARTITION -> weighted threshold MAX CUT (explicit arithmetic base/carry, signed weights and thresholds).
- **K06**: remaining feedback-set, Hamiltonian, Steiner tree, hitting set, and sequencing edges.
- **K07**: all 21 NP-membership proofs and end-to-end reduction-chain composition, runtime/encoding audit, independent verification.

## Important boundaries
The phrase *max-cut* used for research prioritization in DASHI is not Karp's weighted graph MAX CUT. Likewise Yang-Mills finite compatibility cliques are not the general CLIQUE NP-completeness result. Keep the two uses separate. Optimization and decision variants must be connected by explicit bridges.

Do not promote conditional assumptions, synthetic receipts, small test cases, or source-written code into kernel-verified completeness theorems.
