# MMP max-cut 2026-10-25: Pareto / Ibrahim / Dewey-source snowball and BVP same-object test

**Status:** executed P1/P2 *effective-model* constraint audit; source-specific original-literature graph; non-promoting physical prerequisites. This document distinguishes the existing two-mouth numerical interior, one-ended same-universe physical topology, generic Hadamard state existence, and one selected quantum state.

## Reproducible implementation: consume, do not duplicate, the original BVP

New `scripts/check_mmp_effective_bvp_radial_same_state_cut_20261025.py` **imports** the canonical existing `scripts/check_mmp_global_effective_bvp_replay_20261024.py` and evaluates its actual ODE solution at 81 interior samples for q=10,12,24. It compares, with the same solver-chosen effective matter and the same geometry:

- Einstein radial null: `Gkk = 2 [ F v/r - r''/r ]`, `v=r'`, `F=N'/N`;
- effective matter source: `Tkk=[c F'/(12 pi)+4t/N²]/(4 pi r²)`, `t=-pi c/(12L²)`;
- radial constraint `C=v²-1+2rvF+Q²/r² - 2p`, with `p=-cF²/(24pi)+2t/N²-U(r)`;
- symbolic **exact** identity for the same ODE: `Gkk - 8 pi Tkk = C/r²`;
- geometry-only exact finite-interval budget: `integral_0^X (r/N) Gkk dx = -2 [(r'/N)(X) -(r'/N)(0)]`;
- independently integrated matter `8 pi integral_0^X (r/N) Tkk dx` versus that boundary.

The identity follows directly by differentiating `r'/N` for `ds²=-N²dt²+dx²+r²dOmega²`; it is a **finite throat segment** with an RN interface at its endpoint, *not* a complete two-ended asymptotically flat integration and not a complete one-ended return-loop solution.

Local executed results, default q and L=20, Python SciPy/SymPy, 2026-10-25:

| q | Max |C| on 81 interior nodes | Max |Gkk−8πTkk| | |integral geom − boundary| | |integral 8πsource − boundary| |
|---|---:|---:|---:|---:|
| 10 | 5.615731e-12 | 1.221262e-13 | 8.24299e-13 | 1.14350e-13 |
| 12 | 4.268142e-12 | 4.045625e-14 | 4.78555e-13 | 3.12826e-13 |
| 24 | 4.365733e-12 | 1.353428e-14 | 1.70974e-14 | 9.97327e-13 |

Actual computed effective geometric budgets: q10 `-0.02787042341554`; q12 `-0.03956700102417`; q24 `-0.10157394399799` (dimensionless chosen effective BVP units), NOT physical ANEC detection. Negative control shifts the source budget by +0.025 and is correctly rejected. Exact symbolic algebra `Gkk−8πTkk=C/r²` passed SymPy. Locally executed script SHA256 **0220035006e4ecfff743625bcc27a9c93422cf118ff961b44ad541d2f96154d2**. The local reproduction used a functionally equivalent **manually reconstructed original BVP producer** from its GitHub source, not a byte-hashed repo export; the new checker matched its GitHub upload by length and codepoint sum. The checker also passes under `python -O` with explicit always-on error guards. No GitHub exact-head CI or kernel certificate.

**Important scope:** this verifies **one** radial Einstein equation and its integrated consequence for the **effective chosen Polyakov + truncated massive spherical tower**. It does not validate independent Maxwell gauge variation, angular/timelike Einstein equations against an independently renormalized full 4D quantum Dirac state, the exterior same-universe mouth gluing, or the validity of externally specified negative Casimir energy as a selected Hadamard source.

## Ibrahim/Pareto/snowball protocol actually applied

Same-object consumer first → check the repository's existing owner → acquire source root with DOI/arXiv/dates → classify relation to consumer as theorem, model precedent, correction, challenge, review or mere discovery → snowball only to original producer or discriminating counterexample → rank by *claim closure/rejection*, reproducibility, availability and next-dependency cost. Reprints and arXiv/journal versions of one work are **one source root**; DOIs and source titles do not constitute independent experimental corroboration. Unverified Wikidata QIDs and Dewey identifiers remain **unresolved**; do not invent them. Dewey/Ibrahim are routing/lineage aids, not evidence authority. Preserve the original author/date and do not promote abstract's claims to local derivations.

| Root / original author and verified locator | Typed edge and relevant original claim | Match to this project | Decision |
|---|---|---|---|
| **MMP**: J. Maldacena, A. Milekhin, F. Popov, arXiv:1807.04726 (2018), CQG 40, 155016 (2023), DOI `10.1088/1361-6382/acde30` | **ORIGINAL MODEL ROOT**. Charged massless fermions, negative Casimir-like energy, long 4D Einstein–Maxwell wormhole. The 2018 preprint and 2023 publication are not independent witnesses. | Defines the actual consumer and its nonconstant throat, mouths and quantum fermions | P0 must retain |
| **Gérard–Stoskopf**: C. Gérard, T. Stoskopf, 2022, `arXiv:2108.11630`, DOI `10.1142/S0129055X22500088` | **EXTERNAL EXISTENCE THEOREM**: Hadamard states for free Dirac operators, including general globally hyperbolic spin-spacetime existence. | Generic existence alone does NOT select the magnetic-return state or its stress | Already reusable; promote no further |
| **Capoferri–Murro**: M. Capoferri, S. Murro, 2025, `arXiv:2201.12104`, DOI `10.1002/mana.12032` | **CONSTRUCTION DONOR**, propagator/Hadamard on Cauchy-compact setting with local finite-time double reduction. | Supports local finite propagation; not full global noncompact state selection | Retain as conditional local donor |
| **Zahn**: J. Zahn, 2014, `arXiv:1210.4031`, DOI `10.1142/S0129055X13300124` | **RENORMALIZATION ORIGINAL**: charged Dirac Wick current/stress and conserved/forced Ward relations with finite renormalization ambiguity. | Crucial same-state 4D current/stress extraction and counterterm agreement | P1 highest forward source |
| **Kontou**: E.-A. Kontou, *Wormhole Restrictions from Quantum Energy Inequalities*, Universe 10 (2024) 291, `arXiv:2405.05963`, DOI `10.3390/universe10070291` | **REVIEW + SPECIFIC ADVERSARIAL RESULT**: includes new bound for the long MMP construction from a doubled smeared null energy condition. | Must check selected state against quantum negativity bounds, not merely `ANEC<0` | P1 adversarial highest |
| **Fewster–Verch**: C. Fewster, R. Verch, CMP 225 (2002) 331–359 (original Dirac weak quantum energy inequality) | **ORIGINAL THEOREM**: timelike-averaged Dirac QWEI on globally hyperbolic backgrounds. | Restriction, but not automatically the null-averaged MMP inequality | P1 conditional |
| **Dawson–Fewster**: S. Dawson, C. Fewster (2006/2007), *An explicit quantum weak energy inequality for Dirac fields in curved spacetimes* | **METHOD ORIGINAL**: explicit curved static Dirac QWEI. | Potential direct stress inequality only after reference-state/mode and geometry match | P2 alternate |
| **Friedman–Schleich–Witt**: J. Friedman, K. Schleich, D. Witt, PRL 71 (1993) 1486, DOI `10.1103/PhysRevLett.71.1486`; **erratum 1995** DOI `10.1103/PhysRevLett.75.1872` | **TOPOLOGICAL CENSORSHIP THEOREM** under global assumptions plus NEC. 1995 erratum retracts **secondary passive-censorship attribution**, not the main theorem. | Negative energy is needed for the proposed accessible topology; no automatic theorem against the proposed quantum scenario | Topology assumption audit |
| **Freivogel–Fumagalli–Tomašević**: B. Freivogel, A. Fumagalli, M. Tomašević, `arXiv:2606.12528`, first 10 June 2026, revised 14 Sep 2026 | **SOURCE-SPECIFIC FORWARD STUDY**: 4D MMP low-frequency scattering; charged massless fermions can transmit efficiently, scalars often suppressed except resonances. | Tests channel species and actual scattering **given** MMP effective geometry, not the Hadamard stress producer | P3/Q consumer |
| **Weinbaum**: R. J. Weinbaum, `arXiv:2607.28738` (2026), PRD 114 084004 (5 October 2026), DOI `10.1103/g89c-gqyf` | **INDEPENDENT ADVERSARIAL NUMERICAL STUDY**: failures of static classical definite-positive-frequency Einstein–Dirac(-Maxwell) source constructions, including improper electromagnetic self-interaction treatments. | NOT a refutation of quantized Dirac *vacuum* Casimir source; sharp warning against conflating classical one-particle spinor and renormalized quantum expectation | P1 source-type comparator |

No paper's mere presence in this atlas constitutes a proof of the user's physical model; a novel paper alone does not pay an unbound state/current counterterm/mouth-matching prerequisite. Unverified Dewey/QID fields are explicitly `unresolved` rather than guessed. The Freivogel 2026 revised paper is a **single root**, not new independent empirical corroboration.

## Precise same-object cut: topology versus truncated two-mouth BVP

Existing `scripts/check_mmp_cauchy_handle_thom_flux_20261024.py` specifies `Sigma=(S1×S2)\{point}` with **one** asymptotically Euclidean end, `H1=Z,H2=Z`, and an independent magnetic flux/spin/Wilson sector. The canonical numerical BVP `check_mmp_global_effective_bvp_replay_20261024.py` constructs **one reflected throat segment and two local RN junctions**, i.e. a two-mouth local model. These are not contradictory if the mouths are subsequently glued to a shared, common ambient exterior, but they are **not equal global spatial manifolds before that construction**. The finite-integral radial constraint checks only the spherical interior; no exterior-return field line, global spin-c bundle, quantum two-point covariance across the exterior, or global one-ended Einstein/Maxwell current follows.

**Stop rule:** a full 2-ended globally spherically symmetric `R_x×S2` with both `x→±∞` asymptotically flat has 2 spatial ends; that is not homeomorphic to the selected 1-ended `(S1×S2)\{pt}`. Local end-to-end throat profiles are admissible *local collars*, but no two-ended BVP can silently become the correct one-ended global topology.

## Pareto ranking / falsifiable physical max-cut

1. **P0: Source identity & topology weld (HIGH alpha, low/reusable cost):** declare one actual global one-ended metric and magnetic spin-c bundle with both mouths in the *same* exterior and a selected global Wilson phase. Consume the existing Thom/Cauchy owners. Current BVP acceptance passes its *interior* radial identity only.
2. **P1: Same-state selected charged Dirac Hadamard covariance (HIGH alpha, hardest):** provide a specific CAR two-point distribution with spin-c gauge connection and antiperiodic/Wilson holonomy on that actual 4D geometry; show wavefront, state positivity, global return and no assumed 2D/4D equality. Gérard–Stoskopf's *existence* theorem is not the source-selection step.
3. **P1: Physical sourced tensors and QEI (HIGH alpha, high rejection power):** one same state/parametrix yields `<J>` and all `<Tμν>`, including finite counterterms, `∇J=0` and `∇T=F·J`. Apply Kontou's MMP-specific inequality and the appropriate Dirac QWEI in **their stated domains**, not by swapping timelike/null averaging measures.
4. **P2: Einstein/Maxwell gluing/fixed point (HIGH alpha, expensive):** re-use reduced BVP as initial guess only; solve all tensor/current components, both mouth/exterior jumps, charge/flux and the actual 4D state response; check full curvature/integrated null budget against the same quantum source. Do not relabel q=12 finite model as physical 4D fixed point.
5. **P3/Q: Actual fermionic detector/scattering channel** (medium, dependent): now consume 2026 Freivogel et al. and Lean PR #85 selected q rail labels, but do not promote finite erasure algebra to actual physical quantum capacity without the same state's scattering operators.
6. **P4–P6: Three plasma material regions, source control, external gravity** (dependent; high experimental cost): the existing 3D finite U1 ports are toy classical current drives. Real plasma current, transport, constitutive material stress and independent gravity instruments remain external gates.

**Stop indiscriminate snowballing when no new original source object supplies a missing state, stress, QEI, topological gluing or scattering acceptance.** Closure/rejection/redirection must be identified by the specific theorem, not source counts or repeated citation chains.


## Snowball second generation: classical-Dirac junction and dynamical challenge (2021–2026)

**This citation branch changes an acceptance test, rather than merely enlarging a reading list.**

- Blázquez-Salcedo, Knoll, Radu (2021), *Traversable Wormholes in Einstein-Dirac-Maxwell Theory*, PRL 126 101102, DOI `10.1103/PhysRevLett.126.101102`, **original classical EDM numerical claim**; distinct from MMP's quantized fermion vacuum.
- Danielson, Satishchandran, Wald, Weinbaum (2021), *Blázquez-Salcedo–Knoll–Radu wormholes are not solutions to the Einstein-Dirac-Maxwell equations*, PRD 104 124055, DOI `10.1103/PhysRevD.104.124055`, **direct source-critical reply**: matched classical EDM throat violates sufficient smoothness, with Maxwell and Dirac gluing source defects. This critique belongs to that classical solution, not automatically to MMP or our effective BVP.
- Konoplya and Zhidenko (2022), *Traversable Wormholes in General Relativity*, PRL 128 091104, DOI `10.1103/PhysRevLett.128.091104`, **separate alternative classical asymmetrical continuation**; a response to the prior symmetry objection, not proof of quantum Casimir state.
- Ben Kain (2023), *Are Einstein-Dirac-Maxwell wormholes traversable?*, PRD 108 044019, DOI `10.1103/PhysRevD.108.044019`, **independent classical time-evolution test**; reported black-hole formation/trapping in its simulated models.
- Weinbaum (2026), DOI `10.1103/g89c-gqyf`, **later original numerical follow-up** on positive-frequency classical fields. This is not an independent corroboration of every specific 2021 gluing argument; same author network and source chain are marked.
- 2026 PRD 113 064026, DOI `10.1103/dsnv-gq47`, *Wormholes as perturbations of near-horizon black hole geometries: No-go theorems within effective field theories*, **separate near-horizon EFT constraint**; higher-derivative perturbations alone differ from the specifically negative-Casimir MMP mechanism.

**New original-repo numerical junction discriminator:** for the selected effective BVP's finite proper-radial RN matching, verify *metric and first derivatives* (up to the trivial static clock rescaling), then calculate proper-radial `r''` and `(log N)''` on BOTH sides. At `r=r_m`, `f=1-2M/r+Q²/r²` and `A=M/r²-Q²/r³`, the RN exterior gives `r'_RN=sqrt(f)`, `r''_RN=A`, `(log N)'_RN=A/sqrt(f)`, `(log N)''_RN=-2M/r³+3Q²/r⁴-A²/f`. No independent tensor equations are invented.

| q | Max selected first-derivative junction mismatch | `r''_interior-r''_RN` | `(log N)''_interior-(log N)''_RN` |
|---|---:|---:|---:|
| 10 | 4.97623e-13 | +1.11101e-4 | +3.76627e-6 |
| 12 | 3.75151e-13 | +1.03726e-4 | +5.65731e-6 |
| 24 | 3.60031e-13 | +1.25975e-4 | +1.20664e-5 |

Thus the canonical *sharp-cutoff* BVP has excellent **C1** finite matching, but **nonzero C2 jumps** in this coordinate. C1 is enough to avoid automatically inferring an Israel delta-function shell **from the metric alone**. A C2 jump in a piecewise smooth metric is not by itself a proof of a distributional shell or a physical contradiction: the effective quantum source was deliberately switched off, potentially allowing finite-step stress. It **does** show that the model is not a smooth globally selected renormalized fermionic Hadamard source without further work. Spinor/Maxwell matching is independently unpaid.

**Updated cut:** prioritize source- and state-controlled smooth global exterior glue and matching of fermion 2-point/Hadamard and Maxwell field, not arbitrary improvement of the interior radial numerical residual. The always-on `must` guards were rerun with `python -O` and both intended positive/negative controls passed. Latest committed-source SHA256: `0220035006e4ecfff743625bcc27a9c93422cf118ff961b44ad541d2f96154d2`.
