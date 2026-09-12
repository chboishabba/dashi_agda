# Yang–Mills / Riemann Hypothesis Pull Request Survey Index

Status: repository archaeology / navigation reference. **Not theorem authority.**

Canonical companion owner: `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`  
Maintenance PR: #883 — `Collate NS/YM/RH/GRQ proof archaeology into one canonical ledger`

## Purpose

This is the **card catalogue** for DASHI Yang–Mills and Riemann-hypothesis work. Its job is not to explain the mathematics. Its job is to let a future investigator survey the repository without repeatedly searching GitHub from scratch.

The index is intentionally broad. It retains:

- early foundational PRs;
- substantive theorem/proof-search PRs;
- alternate and abandoned routes;
- superseded/corrected branches;
- validation, CI, profiling and integration PRs when they identify a proof-search epoch;
- cross-pollination PRs that materially contributed machinery or changed route selection;
- PRs whose title does not say `YM` or `RH` but whose body materially carries the lane;
- internal rounds when no standalone PR title can honestly be located;
- external Lean/Aristotle return labels and RH G-lane labels as separate clocks.

**Coverage claim:** this is the union located by chronological PR-history inspection plus broad title/body alias sweeps. It is meant to be over-inclusive. It is not a claim that GitHub search can prove no additional historical body-only PR exists. If a newly found PR belongs here, append it; do not rewrite the older route away.

## How to use this file

Search first by one of:

```text
#PR-number
route tag
round number
module-round Rxxx
G20 / G21
8883 / 8885 / 8889 / 8894
Balaban / Bałaban / Path13 / Eq119 / CMP119 / Row C
Riemann / zeta / Weil / pole-quotient / DBN / certificate
```

Then open the PR. Only after that descend into exact modules/commits if the investigation needs them.

## Clocks — never collapse these

| Clock | Example | Meaning |
|---|---|---|
| GitHub PR | `#440` | repository integration object |
| PR-title/submission/highest-alpha round | `Round30` | programme label used by a PR lineage |
| internal Agda round | `R214`, `R246` | module-local proof-search round |
| RH G-lane | `G20`, `G21` | RH architecture family |
| Lean/Aristotle return | `8883`, `8885`, `8889`, `8894` | external checked-return/session label |
| commit chronology | SHA + timestamp | first source appearance / correction / recut |

## Row tags

- `CORE` — substantive lane work.
- `ALT` — alternative route or experiment worth retaining.
- `SUPPORT` — donor/cross-pollination/source/metadata work.
- `VALIDATION` — checker, CI, profiling or integration-only tranche.
- `CORRECTED` — later work fixed a semantic/carrier/sign/scope defect.
- `SUPERSEDED` — no longer preferred, but historically useful.
- `BODY-ONLY` — material lane content found primarily in PR body rather than title.
- `CURRENT` — current archaeology/current conceptual route pointer.

---

# A. Master YM PR registry

The dedicated GitHub-era YM sequence begins at **PR #5**, not around #200.

| PR | Tags | Title | Round / route search coordinates |
|---:|---|---|---|
| #5 | CORE | `feat(ym): formalize cumulative nested-constraint beta route` | earliest explicit YM PR located; beta / nested constraint |
| #6 | SUPPORT | `feat(ym): generate source-aware critical-path theory atlas` | source/status atlas |
| #7 | CORE | `feat(ym): construct literal periodic lattice transport` | literal lattice / periodic transport |
| #8 | CORE | `feat(ym): add literal Balaban lattice operator realization` | Bałaban operator |
| #9 | CORE | `feat(ym): construct a concrete SU(2) quaternion carrier` | SU(2), quaternion |
| #10 | CORE | `feat(ym): realize the concrete SU(2) adjoint operator lane` | SU(2), adjoint |
| #16 | CORE | `Formalize concrete SU(2) geometry, ad reduction, path transport, and Q0` | SU(2), Q0, path transport |
| #49 | CORE | `feat(ym): package uniform SU(2) radial inverse families` | chart/radial inverse |
| #92 | CORE | `Integrate finite Bałaban one-step SU(2) RG frontier` | one-step RG |
| #125 | SUPPORT | `Extract generic Schur coercivity and join NS/YM` | Schur/coercivity donor |
| #143 | CORE | `Formalise generic compact Lie group theory for Yang–Mills` | compact Lie |
| #146 | CORE | `Close compact Lie exact stack and formalise Yang–Mills frontier` | compact Lie consolidation |
| #151 | CORE | `Instantiate SU(N) matrices and constructive Yang–Mills closure stack` | SU(N) |
| #153 | CORE | `Land concrete SU(N) and constructive Yang–Mills analytic stack` | SU(N), constructive analysis |
| #191 | SUPPORT | `Cross-pollinate shift geometry, Lorentz uniqueness, constraints, and YM frontier` | cross-domain donor |
| #248 | CORE | `Formalize uniform Yang–Mills contraction through continuum gap survival` | contraction / gap survival |
| #260 | CORE | `feat(ym): add compact-simple group-parametric coverage` | compact-simple groups |
| #262 | CORE | `Refine all-scale RG invariant-domain obligations` | all-scale RG |
| #264 | CORE | `Formalize infinite-volume continuum limits C1-C9` | continuum / C1-C9 |
| #269 | CORE | `Derive dominant-free background closure bridges` | background closure |
| #288 | CORE | `Add infinite-volume and continuum OS bridge` | OS / continuum |
| #290 | CORE, BODY-ONLY | `Add critical-map and one-step RG closure package` | YM critical-map/RG |
| #291 | CORE | `Formalize explicit Step V and all-scale invariant chains` | Step V |
| #303 | CORE | `Add exact continuum OS and physical mass-gap cutset` | OS / mass gap |
| #304 | CORE | `Complete finite-background critical-map and one-step RG cutset` | critical-map |
| #305 | CORE | `Add proof-relevant all-scale and thermodynamic cutset` | thermodynamic |
| #306 | CORE | `Implement complete Yang-Mills analytic inhabitation cutset` | broad analytic cutset |
| #307 | SUPPORT, VALIDATION | `Add published-analytic authority boundary and proof-branch CI` | source authority / CI |
| #309 | CORE | `Add source-faithful Bałaban matching and finite Fourier Hodge reduction` | source matching / Hodge |
| #313 | CORE | `Add periodic four-torus and finite Fourier Hodge foundation` | torus / Hodge |
| #315 | CORE | `Close periodic physical fibres, exact finite reductions and terminal-scale assembly` | periodic / terminal scale |
| #328 | VALIDATION | `Add trusted clean Agda CI for the YM coercivity cone` | coercivity CI |
| #329 | CORE | `Close side-four bond coercivity and repair the SU2 chart-radius lane` | coercivity / chart repair |
| #334 | CORE | `Close configured-side C1 identification and radial chart interfaces` | C1 / chart |
| #335 | CORE | `Prove exact SU(2) Wilson plaquette second-order jet` | Wilson / Hessian precursor |
| #339 | CORE | `Close side-four averages and instantiate the C2 coarse propagator frontier` | C2 / propagator |
| #342 | CORE | `Expose and advance the P1–P5 Clay Yang–Mills frontier` | P1-P5 |
| #343 | CORE | `Close the configured Green inverse and advance the literal Clay frontier` | Green inverse |
| #344 | CORE | `Construct T1–T5 Yang–Mills frontier reductions and physical transport` | T1-T5 |
| #346 | CORE | `Internalize literal Yang–Mills frontier producer cutset` | literal producer cutset |
| #348 | CORE, SUPPORT | `Integrate Bishop and DASHI constructive-real backends with literal Yang–Mills frontier` | Bishop / constructive reals |
| #349 | VALIDATION | `Merge literal Yang–Mills frontier into Bishop integration branch` | integration |
| #350 | VALIDATION | `Sync current master into Bishop integration branch` | sync |
| #353 | CORE | `Advance Gate 4 through physical involutions, Bishop parity, P06/P11, Step-V and SI` | Gate 4; submission rounds 7–9 aggregate |
| #357 | VALIDATION | `Validate Yang-Mills submission round eight` | submission R8 |
| #358 | VALIDATION | round-eight validation continuation | submission R8 |
| #359 | VALIDATION | round-eight validation continuation | submission R8 |
| #360 | VALIDATION | round-eight validation continuation | submission R8 |
| #361 | VALIDATION | `Validate Yang-Mills submission round nine` | submission R9 |
| #362 | VALIDATION | `Validate latest Yang-Mills submission round nine` | submission R9 |
| #365 | CORE | `Discharge Bishop factorial/parity/interlacing and finite Step-V sums; isolate lightweight P06` | submission R10 |
| #366 | VALIDATION | `Validate Yang-Mills submission round ten` | submission R10 |
| #367 | CORE | `Add direct-ratio Step-V reducer, audit P06 diameter claims, and order P33 before Gate 4` | submission R11 |
| #369 | CORE | `Complete Round-11 full-ball, P11, and fixed-lattice-to-continuum dependency spines` | submission R11 |
| #370 | CORE | `Advance Yang-Mills Round 11: direct-ratio, P06/P11 audit, Gate-4 ordering, and OS spine` | submission R11 |
| #372 | CORE | `Prove concrete signed P33 coercivity from exact LDL and five local Hessian channels` | P33 / LDL |
| #377 | CORE | `Advance the Clay path with inverse-dexp bounds, Wilson budgets, and continuum-limit reuse` | highest-alpha R14 |
| #378 | CORE | `Audit physical-unit mass-gap transport and close new P33 algebra` | highest-alpha R15 |
| #380 | CORE | `Close inverse-dexp positivity and advance the local SU2 chart engine` | highest-alpha R16 |
| #381 | CORE | `Close the actual endpoint modulus and coupled RG factor audits` | highest-alpha R17 |
| #386 | CORE | `Close the literal quaternion chord lane and calibrate the physical residual` | highest-alpha R18 |
| #391 | CORE | `Replace the collar residual lane with exact Combes–Thomas conjugation` | highest-alpha R19 |
| #393 | CORE | `Close the finite Schur and physical Combes–Thomas endgame` | highest-alpha R20 |
| #394 | CORE, CORRECTED | `Cancel exact gauge and constraint jets from the physical Hessian remainder` | R21; corrected by R22 |
| #396 | CORE, CORRECTED | `Repair the physical Hodge split and construct the rational Wilson sixteen-atom Hessian` | R22 |
| #399 | SUPPORT, BODY-ONLY | broad ternary/cross-domain tranche with NS/YM interface | cross-domain donor |
| #402 | CORE, SUPERSEDED | `Block bare volume-uniform coercivity and formalize terminal-scale gap pullback` | early/diverged R23 |
| #403 | CORE | clean Round23 integration of same programme | R23 |
| #409 | CORE | `Reduce physical Wilson atoms and prove the signed gauge defect modulo the literal link radius` | R24 |
| #415 | SUPPORT, BODY-ONLY | NS commutator tranche carrying YM projection-leakage cross-pollination | donor |
| #416 | CORE, SUPPORT | `Cross-pollinate Yang–Mills RG with projection leakage and reduced modes` | R25 |
| #421 | CORE | `Separate physical gap scaling from RG compatibility and quantify uniform Schur inputs` | R26 |
| #425 | SUPPORT, BODY-ONLY | harmonic carrier / shared NS-YM filtered-estimate algebra | donor |
| #427 | SUPPORT | `Cross-pollinate YM gap scaling with harmonic and wreath refinement` | around R27 |
| #430 | CORE | `Close signed Wilson incidence, same-h terminal coercivity, and exact RG tails` | R27 |
| #432 | VALIDATION | `Validation probe: round 27 signed Wilson and terminal Hessian` | R27 |
| #433 | SUPPORT, BODY-ONLY | VOA finite-mode/trace probes with shared NS/YM material | donor |
| #435 | CORE, SUPERSEDED | `Separate observable and spectral uniformity and formalize RG good-class preservation` | R28; integrated by R29 |
| #439 | CORE, CORRECTED | `Unify YM highest-alpha head and isolate correlated W-local cancellation` | R29 |
| #440 | CORE, ALT | `Add strong-coupling functional-inequality route and exact SU(2) margin arithmetic` | R30; strong-coupling route |
| #443 | SUPPORT | `Formalize Hurwitz, Hopf, Klein, and Noether cross-pollination` | stacked on R30 |
| #444 | CORE | `Reconcile SO/SU curvature rates, weighted Wasserstein contraction, and all-beta scaling` | R31 |
| #457 | SUPPORT | `Add complete frontier Hodge, automorphic, spectral, YM and NS cross-pollination` | cross-domain frontier donor |
| #458 | CORE | `State the literal Clay YM contract and derive the Hessian coefficient from sixteen atoms` | R32 |
| #461 | CORE, SUPPORT | `Formalize Yang-Mills claim papers, all-group promotion guards, and gap scaling` | R33 / source claims |
| #462 | CORE | `Derive the physical selected-background radius and construct W-local` | R34 |
| #466 | CORE | `Derive the plaquette curl and isolate the sharp Wilson deep remainder` | R35 |
| #470 | CORE | `Close the finite Wilson pair/deep channels and expose the exact variation selector` | R36 |
| #473 | CORE | `Construct the finite selected-variation repair and spillover ledger` | R37 |
| #476 | CORE | `Construct the physical projector and split the selected-variation spillover` | R37 continuation |
| #486 | CORE | `Construct the redundancy-safe KKT projector and local constrained Green algebra` | R39; successor says R38 existed internally |
| #487 | VALIDATION | temporary Round39 checker/probe | R39 |
| #488 | VALIDATION | temporary Round39 checker/probe | R39 |
| #489 | CORE | `Localize the KKT multiplier and close the correlated singleton reducer` | R40 |
| #491 | VALIDATION | Round40 checker/probe | R40 |
| #496 | CORE | `Build the physical Yang–Mills constraint producer and SZZ decision tranche` | R41 lineage |
| #497 | CORE, ALT | `Certify the single-plaquette owner envelope with exact budget slack` | certified-enclosure fork after R40 / branch R41 |
| #505 | VALIDATION | `TEMP: merge master into YM Round 41 working branch` | integration only |
| #507 | CORE, CORRECTED | `Reconcile the physical YM constraint floor and recovery route onto master` | post-R41/R42 reconciliation |
| #519 | CORE, SUPERSEDED | `Close the reduced KKT multiplier seam on the selected YM tangent projector` | stale first follow-up |
| #520 | CORE | same reduced-KKT seam on clean/current ancestry | supersedes #519 branch state |
| #522 | CORE | `Close the nonlinear gauge derivative budget and telescope RG covariance` | Round44 lineage |
| #540 | CORE | `YM Gate I: normal-form authority and canonical correction` | Round46 aggregate lineage |
| #542 | CORE | `YM Gate I: tighten physical producer seams` | R47 |
| #543 | CORE | `YM Gate I + source-faithful complete-density RG reuse` | post-R47 / CMP119/CMP122 source route |
| #547 | CORE | `YM Round52: source-native physical leaf reductions` | R52 |
| #554 | CORE | `YM Round54: derive Federbush cancellation and finite physical producer spine` | R54; body references R53 predecessor |
| #564 | CORE | `YM Round56: normalized pi momentum bridge + five-channel quartic beta adapter` | R56 |
| #566 | CORE | `YM Round57: four-orbit beta, Bishop interval semantics, grouped G2 and source-native RG` | R57 |
| #568 | CORE | `YM Round58: canonical G2, compact-group one-loop, and published 4D UV boundary` | R58 |
| #571 | CORE | `YM Round59: positive RG geometry, Cheeger gap, and two-metric cutoff gate` | R59 |
| #574 | CORE, ALT | `YM Round57: hyperoctahedral orbit reduction + Walsh cancellation` | parallel R57 symmetry route |
| #575 | CORE | `YM Round60: Walsh cancellation before Bishop intervals and G2 symmetry falsifier` | R60 |
| #578 | CORE, ALT | `YM Round60: literal G2 support, charge-relative Green closure, FP ghost and Wilson transfer positivity` | parallel R60 |
| #583 | CORE | `YM Round61–87: literal Clay four-family frontier; marked stress fields and beta trig reduction` | aggregate of many internal rounds; do not assume one PR per round |
| #644 | CORE | `YM Round112: pay A2 marginal sensitivity with mixed-Cauchy cubic telescope` | R112 |
| #670 | CORE | `Close theorem-level Path13 exactness and compress the mass-gap frontier` | Path13 precursor |
| #732 | CORE | `Narrow YM Eq119 and split the physical Hamiltonian cut` | Path13 / Eq119 / Hamiltonian |
| #753 | CORE | `Construct the Path13 two-carrier Eq119 source-family compiler` | Path13 / CMP98 Eq.(119) |
| #764 | CORE | `YM: prune per-bond geometry and pointwise Eq. (119) chart receipts` | Path13 Eq119 minimization |
| #789 | CORE | `YM: split Path13 uniform calculus source payment` | Path13 Eq119 |
| #790 | CORE | `YM: minimize Path13 Eq119 semantic calculus payments` | Path13 Eq119 |
| #792 | CORE, CORRECTED | `YM: correct Path13 Eq119 printed dexp/J roles` | sign/operator correction |
| #793 | CORE, SUPPORT | `YM: x-pollinate T3 right Jacobian into corrected Eq119 roles` | T3 donor |
| #795 | CORE | `YM: minimize T3 Eq119 scalar source boundary` | scalar cut |
| #796 | CORE | `YM: split Path13 physical data from standard operator representation` | physical vs representation split |
| #797 | CORE | `YM: add current preferred Path13 Eq119 source frontier` | Eq119 frontier at that epoch |
| #799 | CORE | `YM: make mass-gap route consume current Eq119 frontier` | route integration |
| #800 | CORE | `YM: synchronize spectral statement with current Eq119 frontier` | spectral sync |
| #801 | CORE | `YM: specialize Bałaban variational theorem directly to Path13` | variational specialization |
| #803 | CORE | `YM: align Path13 selected defect with R171 and minimize printed semantics` | R171 alignment |
| #804 | CORE, CORRECTED | `YM: replace 1/24 cut with exact 74-link Eq119 budget` | threshold correction |
| #806 | CORE, SUPPORT | `YM: reduce M7 domain/self-adjointness through Kato closed forms` | operator-domain route |
| #809 | CORE | `YM: minimize T5 physical continuum OS-gap source cut` | T5 / continuum / OS |
| #811 | CORE | `YM: construct finite projected P33 Hamiltonian domain and floor` | finite Hamiltonian precursor |
| #821 | CORE, SUPERSEDED | `YM: isolate literal CMP119 raw-source family as first preferred source wall` | internal R212–217; broad raw-source wall |
| #829 | SUPPORT | `Wikimedia: attach scientific reference QIDs across YM, NS and RH` | metadata / source identity |
| #846 | CORE, CORRECTED | `YM: recut preferred source frontier to regular-E and marked-history seams` | internal R218–228; BC1 route recut |
| #849 | SUPPORT, VALIDATION | `YM Path13: fibre-native aggregation and OOM profiling follow-up` | elaboration/resource route |
| #857 | CORE, ALT | `YM Row C: minimize Heat/Doob debt to real majorants and one weighted generator row` | internal R251–259; Row-C tactic |
| #867 | CORE, SUPERSEDED | `YM Row C: split Langevin commutator from symmetric Hessian row weld` | explicitly superseded by #869 |
| #869 | CORE, CURRENT | `YM: normalize mass-gap search to quantitative clustering consumer` | internal R270–275; Row C demoted to optional tactic |
| #883 | SUPPORT, CURRENT | `Collate NS/YM/RH/GRQ proof archaeology into one canonical ledger` | archaeology / current survey branch |

### YM internal-round-only gaps explicitly retained

These are known/visible in successor modules or PR bodies but **no trustworthy standalone PR title is assigned here**:

```text
R38
R42
R43
R45
R48–R51 (unless later PR archaeology locates exact standalone titles)
R53 predecessor referenced by #554
R55 / R60-adjacent internal steps represented inside aggregate branches
many R61–R87 steps represented by #583 rather than one PR each
```

A search for `Round43` returns NS #527, not YM. Do not attach that PR to YM merely to fill the number.

### YM high-value route families for browsing

```text
early beta/lattice/SU2        #5–#16, #49, #92
compact-Lie / SU(N)           #143, #146, #151, #153
all-scale / continuum / OS    #248, #262, #264, #288–#315
Gate4 / submission rounds     #353–#370
P33 / Combes–Thomas           #372, #377–#403
highest-alpha Wilson/KKT       #409–#522
Gate-I / source-native RG      #540–#583
Path13 / CMP98 Eq.(119)        #670, #732, #753, #764, #789–#804
Hamiltonian / OS support       #806, #809, #811
CMP119/CMP122 source recuts    #821, #846
Row C / mass-gap recut         #857, #867, #869
```

**Search warning:** `CMP98 Eq.(119)` / `Eq119` is not `CMP119` the Bałaban journal paper. Keep those search families separate.

---

# B. Master RH PR registry — every located route, not only the current one

| PR | Tags | Title | Route / search coordinates |
|---:|---|---|---|
| #100 | CORE | `Formalise Riemann zeta and the DASHI–Weil RH proof route` | foundational zeta / Weil / explicit formula |
| #121 | CORE | `Extend zeta with von Mangoldt exhaustion and Weil-square coercivity` | von Mangoldt / Weil-square |
| #128 | SUPPORT | `Formalise prime counting, Chebyshev functions, and Riemann transforms` | prime-counting background |
| #449 | ALT, SUPPORT | `Add substantive RH, Hodge, BSD, P-v-NP, Poincare, and graded-VOA tranches` | Xi symmetry / Hilbert–Pólya-style support |
| #457 | SUPPORT, BODY-ONLY | broad spectral/frontier cross-pollination including RH | Hodge/spectral donor |
| #604 | CORE, ALT | `Formalize zeta Hermitian defect, finite retention, interference and detectability route` | Hermitian-zeta / Alpöge–Furman / G1–G4-style top-down route |
| #605 | SUPPORT, BODY-ONLY | `Round11: symmetry-resolved traveling-wave conscious-access formalism` | includes `RiemannReflectionOrbitDefectExact`; reflection-block support |
| #610 | SUPPORT, BODY-ONLY | `Formalize C3 Fourier conjugation and SSP15 affine phase closure` | critical-line reflection fixed-locus grammar |
| #620 | SUPPORT, BODY-ONLY | `Formalise coarse/fine criticality, stage genealogy, contradiction and recharting` | RH role/provenance / erased-coordinate support |
| #622 | CORE, ALT | `G21: pole-quotiented two-channel exterior explicit-formula desk test` | G21; two-channel exterior; four-sample rank-two route |
| #630 | CORE, ALT | `Aristotle RH bidi: explicit cutoff tail and finite post-Schur near core` | Lean return 8883; every-J near/far; finite near carrier |
| #642 | CORE, ALT, SUPERSEDED | `RH bidi cut: checked scalarization plus balance no-go frontier` | Lean return 8885; determinant scalarization; balance no-go |
| #646 | CORE, CORRECTED | `RH bidi: pole-quotient complement margin after balance no-go` | universal pole quotient becomes final carrier; Off + Gamma split |
| #661 | SUPPORT | `Math 2026: source-bounded audits for DBN, prime gaps, D(p^2) and autoformalization` | de Bruijn–Newman / source audit |
| #676 | SUPPORT | `Math 2026: source-exact Dujella/DBN BIDI cross-pollination with RH/NS/YM` | DBN / source-exact cross-pollination |
| #677 | CORE, ALT | `RH: bidi-aware experimental proof search and 8889 feedback` | Lean return 8889; H_X→H_A→H_M→H_T→H_W→H_E; cluster/Gamma feedback |
| #686 | CORE, ALT | `RH BIDI: 8894 gap-split no-go and adaptive clustering reconciliation` | Lean 8894; taper/gap-split no-go; adaptive clustering; target modulation recovery |
| #691 | CORE, CORRECTED | `RH: H_A consumer-quotient active recovery cross-pollination` | source-native H_A / modulation dependent producer |
| #721 | CORE | `BIDI-weld ζ density, literal target-gap moment, and direct finite producer into the live RH cut` | determinant/G2d diagnostic vs final-carrier weld |
| #751 | CORE, CORRECTED | `Reconcile merged RH diagnostics with final pole-quotient cut` | final-carrier correction; one crossing J; signed near + far; Gamma |
| #770 | SUPPORT, BODY-ONLY | `Cross-pollinate residual action with agentic, Base369/Monster, Pareto, tetration and literal frontier search` | `RiemannZetaLiteralFrontierSchedulerExact`; literal frontier scheduler |
| #774 | CORE | `Reconcile post-751 RH final carrier and Gamma proof routes` | Off/Gamma analytic-core compression |
| #813 | CORE, SUPERSEDED | `Fix and wire direct RH terminal compiler` | explicitly superseded by #818 |
| #818 | CORE | `RH: unify current terminal compiler with analytic-core prize path` | analytic-core / high-low prize path |
| #824 | CORE, CORRECTED | `RH: direct one-leaf pole-quotient cut with proof-gap introspection` | direct one-leaf; literal final near; still used intermediate M_cluster |
| #829 | SUPPORT | `Wikimedia: attach scientific reference QIDs across YM, NS and RH` | bibliographic/QID support |
| #847 | CORE, CURRENT | `RH: reduce high leaf to balance-free actual ClusterResponse` | removes M_cluster; actual ClusterResponse; balance-free context |
| #855 | CORE, ALT | `RH: generic high contradiction and certified final-near follow-up` | direct + certified producer families; R0/R1/R2/R3 decomposition |
| #856 | SUPPORT, BODY-ONLY | `J invariant Base369 formulaic renderer and pants/q-series follow-up` | carries RH observer-governance / fibre BIDI support |
| #865 | CORE, ALT | `RH: fold-local concrete certificate bridge and R3 min-cut` | certificate scalar need not equal final analytic scalar |
| #868 | CORE, ALT | `RH: reduce certified near route to cellwise integral uppers` | cellwise one-sided numerical certification route |
| #883 | SUPPORT, CURRENT | `Collate NS/YM/RH/GRQ proof archaeology into one canonical ledger` | archaeology / current survey branch |

## RH route-family index

This section is intentionally route-oriented so **failed/abandoned routes remain discoverable**.

### RH-01 — base zeta / Weil / explicit-formula route

```text
#100 -> #121 -> #128
```

Search aliases: `Riemann`, `zeta`, `Weil`, `von Mangoldt`, `Chebyshev`, `explicit formula`.

### RH-02 — Xi symmetry / Hilbert–Pólya / broad spectral experiments

```text
#449
#457 (support)
```

Keep as historical spectral route; do not equate it with the later pole-quotient route.

### RH-03 — Hermitian defect / finite retention / interference route

```text
#604
#605 support
#610 support
```

Search aliases: `Hermitian defect`, `reflection orbit`, `critical-line reflection`, `Alpöge`, `Furman`.

### RH-04 — G20 predecessor

A separate **G20 cutset project is referenced by #622 but is not present in this GitHub tree**. This is an honest archaeology gap. Do not invent a PR number.

### RH-05 — G21 two-channel exterior route

```text
#622
```

Four samples / rank <=2 nuisance / parity minors / exterior observable. This route matters historically even though later proof search moved elsewhere.

### RH-06 — Aristotle/Lean 8883 explicit-cutoff route

```text
#630
```

Coordinates: every-cutoff near/far split, finite near carrier, explicit far-shell modulus, cutoff transport. Checked Lean status is not Agda proof transport.

### RH-07 — 8885 determinant scalarization / balance no-go

```text
#642 -> #646
```

#642 finds the balanced determinant obstruction. #646 pivots to the universal pole quotient rather than forcing a strict contradiction on a balanced carrier.

### RH-08 — universal pole-quotient split-complement route

```text
#646 -> #751 -> #774 -> #818
```

Search aliases: `pole quotient`, `Off`, `Gamma`, `allowance`, `analytic core`, `split complement`.

### RH-09 — DBN / contemporary-source cross-pollination

```text
#661 -> #676
```

Source/support route; retains de Bruijn–Newman and 2026 math context without becoming the final RH carrier automatically.

### RH-10 — 8889 BIDI experimental architecture

```text
#677
```

Search aliases: `8889`, `H_X`, `H_A`, `H_M`, `H_T`, `H_W`, `H_E`, `quantitative cluster`, `Gamma`.

### RH-11 — 8894 gap-split/taper no-go + adaptive clustering

```text
#686
```

Search aliases: `8894`, `gap split`, `taper`, `adaptive clustering`, `J*Lambda`.

### RH-12 — H_A source-native modulation / consumer quotient

```text
#686 -> #691
```

Recover source modulation/transform-shift structure and avoid charging generic Fourier translation machinery as new proof debt.

### RH-13 — determinant/G2d target-gap diagnostic and live-carrier weld

```text
#721
```

Important diagnostic/same-object route; determinant/G2d scalarization is not automatically the final universal pole-quotient carrier.

### RH-14 — final-carrier reconciliation / allowance route

```text
#751 -> #774
```

One common cutoff `J`, signed near estimate, far bound, same-taper Gamma; then analytic-core compression.

### RH-15 — generic terminal compiler / analytic-core prize path

```text
#813 (superseded) -> #818
```

#813 is kept because it records the old compiler transition; #818 is the clean successor.

### RH-16 — direct one-leaf route

```text
#824
```

Direct target against a cluster margin; literal final-near observer refinement. Retain even though #847 later removes the intermediate margin object.

### RH-17 — actual-ClusterResponse / balance-free route

```text
#847
```

Current conceptual high-route correction: independent strict theorem targets actual `ClusterResponse`, with final balance withheld until downstream contradiction assembly.

### RH-18 — certified numerical route

```text
#855 -> #865 -> #868
```

R0 concrete scalar bridge; R1 literal final-near identity; proof-carrying finite upper; cellwise one-sided integral upper; R2 strict actual-ClusterResponse margin. This is an **optional sufficient producer**, not the only RH route.

### RH-19 — terminal low-ordinate / critical-coordinate route

Mostly developed inside #824/#855/#865/#868:

```text
criticalLine <-> Re = 1/2
constructive equality stability
Platt–Trudgian verified region on same carrier
verified-region-or-High cover
```

Search aliases: `Platt`, `Trudgian`, `critical line`, `verified region`, `R3`.

### RH-20 — observer / Base369 / J / Monster support

```text
#620
#770
#856
```

Support/cross-pollination only. Keep because these PRs influenced observer/refinement/search machinery, but do not treat them as independent RH proof routes unless their exact RH owners are being investigated.

---

# C. Internal YM source-frontier round crosswalk

These are **module rounds, not PR-title rounds**. They are indexed here because GitHub searches often land on the wrong clock.

| Internal round | Search meaning |
|---:|---|
| R58 | source-native raw-state ancestry / finite-cutoff UV-stability lineage |
| R61–R87 | large four-family tranche largely aggregated by #583 |
| R103 | finite effective-action/Hessian A1/A2/BC1/BC2 family |
| R108 | CombinedRG / source semantics / same-density family |
| R112 | A2 marginal sensitivity; visible in #644 |
| R131 | same-family finite/continuum/Schwinger/common-metric stress endpoint |
| R132–133 | generated-action + first-variation/stress weld |
| R145 | detects post-hoc/circular density-action semantics |
| R191–211 | terminal-cutset iterations before source recut |
| R212 | compatibility source-realization route |
| R214 | source-fixed `rho_k -> A_k`; generated-action provenance |
| R215 | BC1 route reversal to literal regular `E_k` |
| R216–217 | raw source realization split / broad raw-source frontier |
| R218 | published source flow |
| R219 | beta-driven residual/complete-density family |
| R221 | regular-E source projection |
| R225 | preferred regular-E route |
| R234 | source-fixed regular-E semantics |
| R235 | localization-radius split |
| R236 | preferred source frontier recomputation |
| R237 | selected-scale semantics |
| R240 | priority router |
| R241 | regular-E projection compiler |
| R242 | function-valued `RegularTerm = Background -> Real` |
| R243 | extraction/evaluation become compiler output |
| R244 | CMP119 localization theorem vs carrier realization split |
| R245 | function-valued E + localization -> CMP109/116 continuation |
| R246 | active-scale Section-2 form/predicate |
| R247 | active continuation / focused validation |
| R251–259 | least-privilege Row-C Heat/Doob/Hessian/generator-row tranche |
| R260 | anchored Hessian-majorant correction |
| R270–275 | canonical quantitative-clustering/mass-gap consumer |

---

# D. RH clock crosswalk

| Clock | PR | Route meaning |
|---|---:|---|
| G20 | — | predecessor referenced by #622; standalone GitHub project/PR not located in this tree |
| G21 | #622 | two-channel exterior explicit-formula route |
| 8883 | #630 | explicit cutoff / near-far / far shell / finite near carrier |
| 8885 | #642 | determinant scalarization + balance no-go |
| 8889 | #677 | BIDI feedback / cluster-Gamma return; later optional donor |
| 8894 | #686 | gap-split/taper no-go / adaptive clustering / modulation recovery |
| R0 | #855+ | optional concrete numeric/certificate scalar realization |
| R1 | #855+ | final-near same-object representation |
| R2 | #847/#855+ | independent strict high theorem vs actual ClusterResponse |
| R3 | #855+ | critical-coordinate / verified-low-region / high-low terminal lane |

---

# E. Known supersession / correction map

## YM

```text
R21 #394
  -> corrected by R22 #396

R23 early/diverged #402
  -> clean R23 #403

R28 #435
  -> integrated/corrected by R29 #439

stale reduced-KKT follow-up #519
  -> clean/current ancestry #520

broad raw-source-first #821 / R216–217
  -> regular-E preferred recut #846 / R218–228
  -> later R242–247 function-valued active regular-E route

Row-C tactic #857 / R251–260
  -> canonical clustering consumer #869 / R270–275
     (Row C retained as optional producer)

#867
  -> explicitly superseded by #869
```

## RH

```text
broad Weil / window / explicit-formula architectures
  -> retained as historical routes/donors

G21 #622
  -> retained alternate observer route

8885 determinant lane #642
  -> balance no-go
  -> universal pole quotient #646

determinant scalarization remains diagnostic only

#751 allowance/payment API
  -> compressed by #774 / #818 analytic cores

#813
  -> explicitly superseded by #818

#824 direct one-leaf with intermediate M_cluster
  -> #847 targets actual ClusterResponse and removes M_cluster

#855/#865/#868 certified route
  -> optional sufficient producer, not mandatory replacement of direct analytic R2

8889 status/return
  -> optional donor unless theorem-bearing same-carrier transport is recovered
```

---

# F. Search aliases for future rescans

Use these exact families when updating the catalogue. Search **titles and bodies**, not titles alone.

### YM aliases

```text
YM
Yang
Yang-Mills
Yang–Mills
Balaban
Bałaban
mass gap
Gate I
highest-alpha
submission round
Path13
Eq119
CMP98
CMP109
CMP116
CMP119
CMP122
P33
Combes
KKT
Federbush
Row C
Heat/Doob
Langevin
cluster
Wilson
SU(2)
SU(N)
OS bridge
```

### RH aliases

```text
RH
Riemann
zeta
Weil
explicit formula
Xi
Hilbert
G20
G21
Aristotle RH
8883
8885
8889
8894
pole quotient
pole-quotient
Gamma
DBN
de Bruijn
modulation
Schur
critical line
Platt
Trudgian
certificate
ClusterResponse
nearOffFinset
```

### Inclusion rule

Include a PR when the route is materially present in the title/body/diff ancestry. Do **not** include a PR merely because its boundary says something like “does not prove YM/RH”. Examples of false-positive search hits should remain excluded rather than padding the catalogue.

---

# G. Fast investigation pointers

These are navigation shortcuts, not mathematical claims.

| Question | Start here |
|---|---|
| earliest explicit YM PR? | #5, then #6–#10 and #16 |
| early finite Bałaban RG? | #92 |
| compact-Lie/SU(N) expansion? | #143, #146, #151, #153 |
| continuum/OS historical work? | #248, #264, #288–#315 |
| submission-round era? | #353–#370 |
| P33/Combes–Thomas era? | #372, #377–#403 |
| Wilson/KKT highest-alpha era? | #409–#522 |
| Gate-I/source-native RG era? | #540–#583 |
| Path13 / CMP98 Eq119? | #670, #732, #753, #764, #789–#804 |
| Kato/Hamiltonian/T5 support? | #806, #809, #811 |
| CMP119 raw/source recut? | #821, #846, then internal R242–247 |
| Row-C / mass-gap recut? | #857, #867, #869 |
| first RH Weil route? | #100, #121, #128 |
| Hermitian-zeta alternate route? | #604 |
| G21? | #622 |
| G20? | referenced by #622; no standalone PR located in this tree |
| 8883? | #630 |
| 8885 / determinant no-go? | #642, then #646 |
| DBN cross-pollination? | #661, #676 |
| 8889? | #677 |
| 8894? | #686 |
| H_A source/modulation recut? | #691 |
| target-gap/determinant diagnostic? | #721 |
| final pole-quotient reconciliation? | #751, #774 |
| analytic-core terminal path? | #818 |
| direct one-leaf introspection? | #824 |
| actual ClusterResponse correction? | #847 |
| certified/computational route? | #855, #865, #868 |
| current archaeology branch? | #883 |

---

# H. Maintenance rule

When a future PR materially changes YM or RH, append/update this catalogue in the same tranche with:

1. exact PR number and title;
2. lane (`YM`, `RH`, or both/support);
3. route tags/search aliases;
4. round clock if one exists;
5. whether it is core, alternate, validation, support, corrected, superseded, or current;
6. predecessor/successor relationship;
7. if an internal round has no standalone PR, leave the gap explicit instead of guessing.

Do not delete failed routes just because a newer route is preferred. The failed and superseded routes are exactly what make this document useful for investigation.
