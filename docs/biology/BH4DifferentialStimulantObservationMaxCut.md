# BH4 differential stimulant observation — Pareto cut (2026-11-20)

Status: synthetic finite countermodel, source-written; Agda exact-head kernel acceptance OPEN. Not a clinical subtype, treatment recommendation, measured flux, fitted drug model, or original 29x12 source payment.

## Attribution and provenance
- Kimberly Kitzerow owns her documented proposed redox/allostatic BH4 allocation synthesis, not all older enzyme biochemistry. Source: https://www.researchgate.net/publication/383021907_The_BH4_Pathway_as_an_Allostatic_Mechanism_in_the_Pathology_of_Autism_and_Systemic_Comorbidities (version/date and exact original passage pins remain review obligations). The public author page https://www.kimberlyedu.org/the-bh4-shunt is a separate manifestation, not evidence of priority.
- Original biochemical investigators own their findings; the 2020 consensus guideline https://doi.org/10.1186/s13023-020-01379-8 synthesises evidence for BH4-dependent monoamine synthesis; Faraone's 2018 review https://doi.org/10.1016/j.neubiorev.2018.02.001 synthesises stimulant pharmacology. Neither establishes this candidate causal mechanism.
- Kay et al. https://doi.org/10.1016/j.cell.2025.11.039 own the network-level arousal/reward imaging findings, not BH4 evidence. The precision trial uses methylphenidate, not a BH4-stratified head-to-head comparison.
- https://www.instagram.com/reel/Df8V7Y6N9mE/ is the trigger, a user-supplied transcript of the creator's hypothesis; creator identity, exact manifestation and time coordinates remain unverified. No patient data or clinical authority admitted.
- DASHI contributors retain existing geometry, countermodels and implementation priority; this new finite construction is assistant implementation assistance within that programme; no priority claim for pharmacology or clinical science. Rhea/ChEBI and other databases retain curation credit; original experiment authors retain scientific credit.
- Scientific support, priority/chronology, and contact/exposure are independent tracks. Citation is not proof, support is not priority, priority is not correctness, exposure is not derivation/plagiarism, unpaid is not zero, Pareto rank is not truth rank. Preserve source-coordinate, manifestation, context, estimand and source-role matching.

## Minimal construction
Reuse BH4CatalyticTurnoverFutureCountermodelExact.CatalyticCapacityScenario. Capacity = pool * turns; realised synthesis + unused capacity = capacity. Initial accessible reserve + realised synthesis = basal release + extra release + final reserve. No BH4 molecule is consumed per synthetic turnover count. The reserve represents a lumped monoamine stock, not a source-paid vesicular kinetics model.

The fixed illustrative observation is (r/2, r, r+a), scaled by 2 in Agda, with r basal release and a additional mobilisation. The three challenge observations are counterfactuals with common starting state, not sequential doses. The stock balance pays the maximum-release window. Clearance 2/1/1 is synthetic and not a pharmacological parameter or dosage. The model omits NET, receptor sensitivity, metabolism, clinical effects, feedback and explicit vesicle/cytosol compartments.

| pool | turns | synthesis | unused | initial reserve | basal | extra | final reserve |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 | 3 | 1 | 1 | 2 |
| 2 | 1 | 2 | 0 | 2 | 1 | 1 | 2 |
| 2 | 2 | 1 | 3 | 3 | 1 | 1 | 2 |

All yield the scaled observation (1,2,4). The first two differ in pool and synthesis; the first and third have the same synthesis and different pool. Exact rational fixture arithmetic independently checked locally (3/3); no Agda kernel or exact-head aggregate run claimed. This proves a source-written non-factorisation in the selected toy model, not non-identifiability for every physiological model or a proof that BH4 is irrelevant.

## Pareto continuation
S1 (source-written): pool and synthesis non-factorisation, import focused root.
S2 OPEN: compartment-resolved TH to L-DOPA to DA and DBH to NE, QDPR/redox recycling, independently sourced same-object stoichiometry and units (reuse original owners; don't alter the 29x12 chart).
S3 OPEN: conserving cytosolic/vesicular/extracellular balances, DAT/NET direction, degradation, explicit time-indexed challenge and washout; no invented zero exchange.
S4 OPEN: compare allocation against recycling, redox, transport, independent enzyme regulation, reserve depletion, receptor/PK and stress histories; use actual estimand-specific observer receipts and held-out responses.
S5 OPEN: source-paid spatial/PNP attachment, exact-head local Agda/parallel_checker, independent empirical discrimination. No clinical promotion.
Existing P0-P3 and L01-L12 gates are unchanged. Prioritize source and measurements that split the collision, not a stronger unneeded model.

## S3a — compartment-resolved matched endpoint obstruction (2026-11-20)

Extended the existing included `BH4StimulantResponseCountermodelExact` owner, not the 29x12 chemistry or PNP constructors. The source-written `TransferStep` carries separate cytosolic, vesicular and extracellular stock balance proofs. Synthesis, packing, exocytosis, efflux, return/reuptake and two loss coordinates are explicit. Unit transfer and zero losses/packing are selected synthetic fixtures, not assumed zero physical fluxes. There is no claim that the endpoints are equilibria or that any intervention has only these effects. The common initial stock is (2,2,1); each alternative begins from that same stock. Synthesis obeys the existing catalytic-capacity ledger; no reaction-level TH or DBH payment is manufactured.

| case | pool | synthesis | baseline after (C,V,E) | MPH-like after | AMP-like after |
|---|---:|---:|---|---|---|
| resolvedLow | 1 | 1 | (4,1,1) | (3,1,2) | (2,1,3) |
| resolvedHigh | 2 | 2 | (5,1,1) | (4,1,2) | (3,1,3) |
| resolvedGross | 1 | 1 | (5,0,1) | (4,0,2) | (3,0,3) |

All observe endpoints (1,1,2,3), yet pool, synthesis and gross basal release do not factor through that observer on this finite domain. In the gross witness exocytosis and reuptake each increase by one under all three alternatives. The baseline terminal cytosolic stock splits the low/high witness; terminal vesicular stock splits the low/gross witness. These measurements split these selected pairs, not every possible mechanism; assay feasibility and independent sources are OPEN. The common starting stock removes the earlier initial-reserve confound from the pool/synthesis collision.

S3a source-written; independent integer arithmetic checked for nine steps (27 balance equations), not an Agda receipt. S2 and remaining S3 (DA/NE same-source chemistry, actual transport kinetics, loss, time course and washout), S4/S5 and P0–P3 remain OPEN. Attribution remains as above; no new empirical or clinical claims, no medication recommendation. Preserve the original geometry and source ownership; this construction is assistant implementation assistance.

## S2a — selected source-grounded catecholamine chemistry (2026-11-20)

Executable local SymPy 1.14.0 cut: `python scripts/check_bh4_catecholamine_sympy.py`. Reuses existing `build_bh4_stoichiometric_matrix.build_matrix`; exact original builder blob b852084a9ff04e079975354d87a1d3b26a109fa3 reconstructed locally and hash-verified. The new selected 15x5 matrix is NOT the original 29x12 panel; the separate web-row schema prevents that confusion.

Source-observed directed reactions, Rhea / ChEBI microspecies and coefficient identities (web access 2026-11-20; release and full response bytes unpinned):
- TH: https://www.rhea-db.org/rhea/18202; human P07101.
- PCD: https://www.rhea-db.org/rhea/11921.
- QDPR: https://www.rhea-db.org/rhea/32253; exact same participant IDs, direction and NADH inventory as existing BH4RheaChEBIReactionExact / BH4SpatialOriginalQDPRStoichiometryExact.
- DDC: https://www.rhea-db.org/rhea/12273; human P20711.
- DBH: https://www.rhea-db.org/rhea/19118; human P09172; two monodehydroascorbate radicals, not generic dehydroascorbate; ascorbate charge -1 and DA/NE charge +1.

Exact local acceptance: native builder 75/75 coefficients; 30/30 CHNOP/signed-charge residual entries zero; both net paths, pterin invariant, exact nullspace, two reactant-available chronological histories and three negative controls pass. New script blob 23cc570382150a0946429471d01b92903589e34e matches executed content. No CI or Agda kernel receipt.

For extent vector (t,p,q,d,b) = TH,PCD,QDPR,DDC,DBH, delta BH4=q-t, delta hydroxylated BH4=t-p, delta quinonoid DHB=p-q, delta DOPA=t-d, delta DA=d-b, delta NE=b. In the selected closed reaction slice with no pterin or DOPA accumulation, t=p=q=d, and net monoamine increment identifies d and b. Without DOPA closure, two histories with same initial stock of one BH4, two tyrosines, two O2, two NADH and three protons have extents (1,1,1,1,0) and (2,2,2,1,0), same DA/NE net increments (1,0), distinct DOPA and NADH changes. Both restore the initial BH4 stock. This is a constructive collision, not evidence of differential stimulant efficacy. The selected observer has rank 2 versus reaction rank 5. No physiological flux inferred.

S2a selected row identities and exact symbolic cut executed. S2b archived original 29x12 column/ChEBI mapping, original 369 spatial bond/simplex attachment, compartment-qualified DBH and DDC transport, measured kinetics and source payment remain OPEN. The old S3 synthesis field may correspond to DDC extent only after the matching physical boundary/units are supplied; DA net change also subtracts DBH extent where present. Do not substitute TH turnover for DA synthesis across that boundary. No original panel mutation, unearned same-object equality, rate assignment or assumed physical zero exchange. Priority/attribution: Rhea/ChEBI and cited experiment authors for established reactions, Kitzerow for source-qualified proposed ordering, existing DASHI/369 owners for native construction, assistant for selected implementation and collision. All S3b/S4/S5 and original P0-P3 gates retain their prior status.

## S3b/S4a — joint reaction/transfer observer and sampled history (2026-11-20)

Run `python scripts/check_bh4_joint_observer_sympy.py`. Imports existing S2a SPECIES/REACTIONS and native reactive_pnp_369 POINTS/BONDS, preserving the prior source and geometric owners. Local SymPy 1.14.0 replay used literal reconstructed definitions from the two fetched files (not full-module replay); new checker blob b1d668c15fc5c53c8224a66aa05f2296c5454fa8 matches local execution. No CI or kernel acceptance. Selected C/V/E topology assigns TH/PCD/QDPR/DDC to C and DBH to V, not a source-certified physical compartment mapping. The six transfer coordinates per DA/NE follow TransferStep: packing, exocytosis, efflux, reuptake, C/E boundary loss. Loss is intact molecular export, not chemically unbalanced destruction. Separate exchange J is not silently zero in the general model.

M=[R T] has 45 rows, 17 columns, rank 11, nullity 6. E DA/NE observer rank 2, nullity 15. CHNOP/charge conserve for reaction and internal transfer; explicit loss equals exported elemental/charge inventory. Three independent null vectors per monoamine, in transfer order, are (1,1,0,1,0,0), (0,0,1,1,0,0), (0,0,1,0,-1,1). Full-stock observations cannot identify gross cycling or loss location, although all five reaction extents factor through full-stock changes when other exchange is known. Eight repeated positive DA packing/exocytosis/reuptake cycles have identical sampled stocks to no events. This is a finite chronological counterexample, not continuous-time kinetic equivalence.

Of nine declared scalar non-monoamine stock-change candidates, 33 of 126 five-row subsets reconstruct all five reaction extents independent of the twelve transfer/loss extents; fewer than five cannot attain rank five. Extracellular DA/NE adds no reaction-only rank with free transport. Example: cytosolic tyrosine, hydroxylated BH4, NADH, CO2 and vesicular monodehydroascorbate changes identify t,p,q,d,b via t=-delta Tyr, p=t-delta OHBH4, q=-delta NADH, d=delta CO2, b=delta radical/2. Explicit additional exchange must be absent by selected boundary or independently paid/subtracted; arbitrary J makes even full-stock reaction reconstruction non-identifiable (augmented exact witness). Cardinality minimality is restricted to the mathematical menu; assay costs, feasibility and noise remain unpaid.

Native 27-site/54-bond incidence rank 26, nullity 28; all 54 column sums zero; the 45-species tensor spatial aggregation annihilates all internal bond fluxes. This uses the actual ordered POINTS/BONDS definitions, not a physical mapping of C/V/E to 369 sites. Spatial aggregation leaves 28 circulation directions per species. Source-paid original 29x12 mapping, physical compartment embedding, measured boundary terms, actual transport kinetics and washout remain OPEN. S3b finite sampled-history obstruction and S4a conditional reaction-observer cut executed only. Attribution as above: original DASHI/369 geometry and existing theorem owners, Rhea/ChEBI and experimental authors for chemistry, Kitzerow for verified proposed architecture, assistant implementation assistance; no new empirical or priority claim. Original P0-P3 unchanged.
