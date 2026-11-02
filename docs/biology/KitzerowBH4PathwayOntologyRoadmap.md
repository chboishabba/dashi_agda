# Kitzerow BH4 pathway ontology and executable-network roadmap (2026-11-02)

## Ownership and present scope

**Creator proposal:** Kimberly Kitzerow, *Autism & the Comorbidities Along the BH4 Pathway* (January 2024), DOI 10.13140/RG.2.2.23124.37761/1; *The BH4 Pathway as an Allostatic Mechanism in the Pathology of Autism and Systemic Comorbidities* (August 2024), ResearchGate publication 383021907; *Neurodivergent Biochemistry and the Autism and the Comorbidities Theory* (July 2025), DOI 10.13140/RG.2.2.30248.89606.

**Background chemistry:** UniProtKB (https://www.uniprot.org), Rhea (https://www.rhea-db.org/help/links), ChEBI (https://www.ebi.ac.uk/chebi) and older primary biology own the underlying knowledge. Credit Kitzerow for her documented selection, proposed ordering and proposed causal BH4/allostatic synthesis, not already-known NOS, AAAH, AGMO, redox, mTOR or E/I component facts.

**DASHI work:** finite extraction, xPollenation, candidate-causal reconstruction, evidence/payment rules and algorithmic interop belong to their independently attributed repository implementations. A candidate transcription cannot become a verified original quotation. Priority/contact/citation/derivation/misconduct remain five independent genealogy coordinates.

The current 16-UniProt/24-protein–Rhea-link panel yields 12 finite Rhea reactions, 29 indexed Rhea/ChEBI source species, three non-finite MTOR residuals and a 56-coordinate open-state manifest (15 state/context + 12 reaction flux + 29 exchange). This is not Kitzerow's entire proposed pathway, not a compartment-resolved model and not disease-causation evidence. The flux solver remains underdetermined.

## Canonical reuse — no parallel biological ontology

- KitzerowBH4SourceRegistry, KitzerowPriorityGenealogyExact, KitzerowBH4EvidenceAtlasExact: author/source chronology, attribution, bounded research.
- KitzerowBH4SystemNongNangMaxCutExact: proposed mechanisms and per-edge payment.
- UniProtBH4PanelCertificateExact, BH4PanelStoichiometricMatrixExact: protein identity, reaction participants and signed coefficients.
- BH4SystemStateExact, BH4OpenMetabolicNetworkAdapterExact, BH4JointFluxFeasibilityExact: shared pool and open-system law d(x)/dt = S*v + e.
- BH4JointPaymentAcquisitionExact: source and same-context rate/exchange admission.
- DASHI.Core.XPollenationExact + #1227 and ITIR #22: typed external identities, transport-only artifact receipts.
- BH4PathwayOntologyInteropExact and build_bh4_pathway_ontology.py: structural projection, not a new physiology solver.

## Executable first tranche in this stacked PR

1. Validate Rhea, ChEBI, the existing finite matrix and optional xPollenation. Reject contradictory reaction participants, a zero reaction or false promotion.
2. Preserve signed substrate/product coefficients, source revision and acquisition receipt. Rhea master-reaction orientation is not in-vivo physiological direction.
3. Export one deterministic JSON pathway manifest and one RDF-importable JSON-LD discovery graph using identifiers.org for exact Rhea, ChEBI and UniProt coordinates. When present in the newly acquired Rhea REST row, retain GO and Reactome cross-references as separately sourced, non-promoting edges. Unresolved Rhea compounds and all other namespaces remain literal source identifiers until their resolvers are independently acquired. No owl:sameAs is manufactured.
4. Keep author-level *hypothesis* edges in the independent KitzerowBH4ClaimLedgerCandidate.v1.json. Two initially transcribed edges are repo reconstructions of existing BH4 owner claims; original paper page/figure pins remain unverified.
5. Keep 12 reaction-flux and 29 external-exchange coordinates null/unresolved. No SBML, BioPAX or GO-CAM conformance, simulator kinetics or clinical finding is claimed.

Command using already-produced receipts:

    python3 scripts/build_bh4_pathway_ontology.py \
      --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
      --rhea artifacts/biology/rhea-kitzerow-bh4-reactions.json \
      --xpollenation artifacts/biology/bh4-xpollenation.json \
      --claims docs/biology/KitzerowBH4ClaimLedgerCandidate.v1.json \
      -o artifacts/biology/bh4-pathway-ontology.json \
      --jsonld-output artifacts/biology/bh4-pathway-ontology.jsonld

The Phase-4 runner invokes the exporter from receipts produced in that run, with Rhea/matrix-only fallback when no new xPollenation receipt is emitted.

## Exact outstanding max-cut obligations

| ID | Required proof, evidence or implementation | Source/owner and firewall |
|---|---|---|
| KPO-01 | Pin source passages, figures/pages, versioned dates and edge directions for every Kitzerow model assertion. Transcribe the entire documented source-level graph with unresolved statements retained. | Kitzerow primary works. No backdating from later texts. |
| KPO-02 | Compare creator graph nodes/edges against the 16-protein finite panel; report coverage, nonmatches, ambiguity and explicit prior-art subtraction. | Distinct source/claim and chemistry ownership. |
| KPO-03 | Rhea REST now requests GO and Reactome cross-reference columns and the exporter preserves source revision, mapped IDs and unparsed values. **Still required:** execute acquisition, adjudicate GO evidence/taxon/Reactome event identity, and extend to EC, MetaCyc, KEGG and pathway families. | Rhea/UniProt/Reactome. A cross-reference is not the same biological event. |
| KPO-04 | Adjudicate GO/ECO evidence codes, GO-CAM causal assertions, GO cellular components, Cell Ontology/UBERON tissue and sample/taxon scope. | Source-specific GO evidence, not generic ontology matching. |
| KPO-05 | Acquire explicit transport/uptake/export/oxidation reactions and appropriate source/sink boundaries for the 29 exchange *coordinates*. | A coordinate is not proof a transport reaction occurs. |
| KPO-06 | Pin NOS1/NOS2/NOS3 isoform, exact tissue, sample, time, compartment, BH4/BH2/redox, substrate, volume and protein abundance. | Cross-tissue abundance does not create one physical state. |
| KPO-07 | Derive justified assay-specific magnitude and unit bridges (Vmax, kcat*[E], mass/volume) for all 12 reaction-flux intervals, including PCBD1/NOS literature gaps. | Km/Kd/Ki alone do not set flux; protein intensity != enzyme molarity. |
| KPO-08 | Acquire transport/turnover/time evidence for required exchanges; supply matched AAAH/NOS/AGMO demands, then rerun source-paid S*v+e=0 and dynamics. | Unknown != zero. Feasibility != unique causal allocator. |
| KPO-09 | Validate real BioPAX Level 3 and GO-CAM exports with their respective schemas and evidence provenance; distinguish author proposal from curated pathway relation. | RDF/JSON-LD discovery graph alone is not native BioPAX/GO-CAM. |
| KPO-10 | After valid species-by-compartment mapping, produce SBML Level 3 Core (optional FBC/Groups), correct rate-of-extent units amount/time, annotations and a round-trip stoichiometry check. | Never fabricate a shared cytosol or a kinetic law. |
| KPO-11 | Compare identified alternative redox, NO, immune and non-BH4 mechanisms with matched observables, identifiability and negative controls. | Local mechanism support != whole Kitzerow hypothesis. |
| KPO-12 | Reconcile #1159 -> #1226 -> ontology PR with current master; independently reconcile #1227 and ITIR #22. Pin first-implementation commits and exact-head Agda/Python receipts. | Mergeability != type-check or scientific validity. |

KPO-03 through KPO-06 make it easier to find transport candidates and matching physiological states. They can expose assumptions and guide experiments. They cannot independently pay the numerical measurements demanded by KPO-07/08.

## External primary standard/reference roots

- Rhea REST and linked resources: https://www.rhea-db.org/help/rest-api and https://www.rhea-db.org/help/links
- Reactome Content Service: https://reactome.org/dev/content-service
- Gene Ontology / GO-CAM and evidence codes: https://geneontology.org/docs/go-annotations/ and https://geneontology.org/docs/guide-go-evidence-codes/
- BioPAX Level 3: https://www.biopax.org/
- SBML Level 3: https://sbml.org/specifications/sbml-level-3/
- Systems Biology Ontology: https://www.ebi.ac.uk/sbo/
- Cell Ontology: https://cellontology.org/
- UBERON: http://uberon.github.io/

Version/assay/source release still must be pinned in acquired receipts. No standards DOI has been invented.

## Validation (not yet observed on this new head)

    python3 scripts/check_bh4_pathway_ontology.py
    python3 scripts/check_kitzerow_bh4_priority_all.py
    scripts/run_agda29_parallel_check.sh DASHI/Biology/BH4PathwayOntologyInteropExact.agda
    scripts/run_agda29_parallel_check.sh DASHI/Biology/KitzerowBH4EvidenceEverything.agda

No exact-head Agda type-check, remote ontology verification or SBML parser receipt is asserted by this PR.
