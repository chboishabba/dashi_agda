# DASHI X369: C3² exact Fourier, neural source actions and cross-lane maximum-cut roadmap
Owner: Agda PR #1442 (the existing LILA signed-history formal lane). Date: 2026-11-14.
Paired neural execution owner: LeechTransformer PR #4, docs/X369_C2_C3_C3SQUARED_FULL_MAXCUT_20261114.md. Do not create parallel PRs for the same programme. This document supersedes claims in older roadmap sections only where explicitly contradicted by dated evidence; retain historic evidence and attribution.

## Scope and status vocabulary

The aim is to distinguish the exact finite C3 and C3xC3 algebra, a source-bound neural representation, task-level phase composition, causal utility, and the independent physical / Moonshine cross-lane statements. A declaration found in source is not a new kernel check. A Python check is not Agda kernel acceptance. A 55/55 test suite is not a trained-model equivariance proof. A finite construction for a different model is not a same-source Leech model theorem.

DASHI master at user-identified 7a83556a contains existing X369-F0..F5 roadmap sections. Leech PR #4 at 9aa6ad0 held the first F5 lockbox scorer; user subsequently reported host 55/55 after device and exact 16-token regression fixes. Leech PR #4 was then advanced with its full roadmap and those source corrections; do not attribute those commits to Agda. The original RX580 9-row/576-token F0/F1 audit has p0=0.850, p1=0.742 signed-coordinate regrouping; layer 1 D_iso=0.1243 and pooled 3x3 D_C3=0.2125. This does NOT establish isotropy or absence of learned C3.

## Verified finite original-owner declarations: reuse, do not rewrite

1. DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda — authoritative common finite 3x3 torus carrier used by physics and biology. The selected c3x3 proof must use this actual carrier, not an invented synonym.
2. DASHI/Algebra/TriadicDepthOneCharacters.agda — exact C3Phase ring and characterValue/characterAdditive/depthOneCharacter.
3. DASHI/Moonshine/C3FourierConjugationExact.agda — zetaCubedIsOne, chi1ConjugateIsChi2, chi2ConjugateIsChi1.
4. DASHI/Moonshine/OggSSPP2CenteredTernaryGroupExact.agda — centerSheet-assoc, centerSheet-inverse, sheetPhaseRoundTrip, sheetToPhase-preserves-addition; origin is a distinguished signed zero.
5. DASHI/Moonshine/OggSSPP2BalancedTernaryPuncturedPlaneExact.agda — puncturedNineSheetCountIsThreeSquaredMinusOne and duplicated-centre caveat.
6. DASHI/Cognition/PNF/ModularFourierGrokkingC3Exact.agda — algorithmicRuleIsCharacterComposition, memorizerAndAlgorithmTrainingEquivalent, memorizerAndAlgorithmNotFullTaskEquivalent.
7. DASHI/Cognition/PNF/GrokkingEquivarianceDefectGeometryExact.agda — algorithmicEquivarianceDefectIsZero, memorizerEquivarianceDefectIsTwo.
8. DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda — algorithmicPairLinearises, phaseOneActsByOmegaOnEveryState.
9. DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda — antipodeConjugatesCycleToInverse, qutritPresentationIntertwinesCycle. This is C2 semidirect C3 on a three-state carrier; not automatically C2xC3 or the full neural action.
10. DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda — finite block-index translation exact; its module explicitly excludes the physical side-4 SU(N) Wilson action.
11. DASHI/Physics/Closure/NSTriadKNLuoGalerkinFourierModePairExact.agda and DASHI/Physics/Chemistry/AtomicPeriodicTable369GenerativeExact.agda are separate physical donor types, not derived from a common numerical label.

All listed names are observed in source, not freshly replayed Agda kernel acceptances by this roadmap. In the main master roadmap, 4/4 Python exact integer Z[omega] C3² orthogonality/Parseval/convolution verification was previously host-accepted. That is a finite calculation receipt, not the selected Agda same-carrier theorem.

## Exact formal obligation register — PROPOSED names, NOT declarations already proved

### Part A: C3xC3 on the original physical common finite torus

A01 c3x3SameCarrierGroupLaw:
  G = FiniteThreeCycleTorusExact.Channel (or exact original nine-index type); exhibit identity, inverse, commuting generators and the explicit dictionary to the nine balanced-ternary sheets, with two-sided inverse maps. Do not duplicate a nine-element carrier.
A02 c3x3CharacterOrthogonalityOnOriginalCarrier:
  For frequencies k,l in G, sum over x in G of chi_k(x)*conj(chi_l(x)) equals 9 when k=l and 0 otherwise, over the existing exact Z[omega]/phase structure. Define the sum and ring morphism once.
A03 c3x3FourierConvolutionSameCarrier:
  FT(f*g)(k) = FT(f)(k) FT(g)(k) in the same ring, finite sum, convolution and normalisation convention. Supply inversion.
A04 c3x3ConjugationParsevalAndReality:
  Real-valued source fields produce conjugate k/-k Fourier pairs; Parseval with correct nine-point normalisation and no swallowed DC/centre contribution.
A05 c3x3PunctureCentreGaugeBidi:
  The original pointed-eight amplitudes plus independent centre -> nine sheet -> four complex character pairs -> inverse -> original eight+centre, including re-gauging when translating. State which norm is preserved (zero-mean nine-sheet), not naive punctured-eight norm.
A06 c3x3AgdaKernelSelectedSourceAccepted:
  Exact selected module path, verified transitively imported sources, Agda pinned toolchain and successful existing script wrapper output. Reject unsolved metas/postulates and reflexive wrappers over unrelated carriers.

### Part B: exact C2 / C3 / S3 action distinctions

B01 originalC3SimultaneousRouteRotationInvariant:
  For the actual Leech source trialectic directed-channel formulas I(x,h), show I(Rx,Rh)=I(x,h) for cyclic triad shift R. Additionally check scalar unary channel invariance and top-k behavior with ties.
B02 originalC3RelativePhaseChangesDirectedChannels:
  Construct a selected exact witness with I(Rx,h) != I(x,h) and equal norm, proving a simultaneous group action is not a phase-destruction intervention. Example triads x=h=(1,0,0).
B03 originalC3ShiftVsBalancedInversion:
  Distinguish shift of order 3, inversion automorphism on C3 (phase conjugation), independent central sign C2=-I and semantic opposition. C2xC3, C2 semi-direct C3 and diagram S3 cannot be conflated.
B04 originalC3Punctured9DiagonalAndOneSidedAction:
  Fourier four-pair F3² translation of x and history has invariant relative dot/wedge routing channels; a one-sided shift need not. Prove source function exact under stated centre-gauge.
B05 originalC3NeuralSiteTransportBidi:
  Every claimed equivariance must name (input action, activation site, history, expert routing, output consumer), tie/precision conditions, and source revision. No theorem solely about a hand-coded chart can close this.

### Part C: learned representation and causal soundness, formal interfaces before source instantiation

C01 originalC3InputLabelActionTyped:
  A task T with a genuine input G-action and label/output G-action; source has to provide meaningful R on original inputs, not coordinate rotations.
C02 originalC3HiddenActionGaugeIndependent:
  A specified learned-layer chart h and representation rho with transformation law well-typed modulo admissible readout gauge.
C03 trainedC3TaskActionEquivarianceDefectBound:
  Finite-evaluation evidence of normed h(Rx)-rho(R)h(x); the formal target must state the verified finite set and tolerance, not universal all-input neural symmetry unless supported by the model.
C04 trainedC3LearnedPhaseReadoutIdentifiable:
  A trained u and independently labelled residues; constant/collapsed or teacher-substituted Fourier maps rejected.
C05 learnedC3PhaseCompositionHeldout:
  u(a)u(b) approx u(a+b mod3) on unseen combinations and across seeds; exact modular carrier formal theorem is only a specification for learned approximate behaviour.
C06 originalC3PhaseInterventionSourceConsumerBidi:
  Actual model site (pre/post router, relative activation/history, recurrent step, expert identities) with reversibility and norm preservation; original logits and off-target labels are observed.
C07 learnedC3PhaseCausalExcessLoss:
  Paired selective ablation vs equal-norm/gauge/random-phase control, predeclared improvement direction and clustered uncertainty. This is empirical acceptance, NOT an Agda closed numeric theorem in advance.
C08 originalC3SemanticTrialecticFaceBoundary:
  Independent semantic label/action source needed; orthogonal three-axis chart alone is insufficient to identify reasoning face/opposition.

### Part D: original trained model, frozen scoring and independent C3² comparison

D01 originalLeechC2PairedOddEvenCrossCancellationAllRelevantStates — expand 9-row teacher-input test to all named original recurrent states or explicit counterexample; no universal theorem from a zero paired mean.
D02 originalLeechSignedHistoryRecurrentActionBidi — same original MoE top-k, expert history, R64 and 32+ token original trace with correct finite-precision refinement.
D03 originalC2C3RouterOnlySourceIdentity — shared source state, trained parameter/frozen weights equality, matched seeds and optimiser schedule; fail on any accidental state change.
D04 freshC2C3DevelopmentDocumentDisjoint — documentary source IDs, original tokenizer and genuine separate split, not only token-n-gram exclusion.
D05 matchedBoundedRouterPredictiveGainOrCounterexample — measured development delta CE(C2C3)-CE(C2) across paired seeds, explicitly selection-exposed.
D06 frozenSelectionIndependentOfLockbox — chosen from development CE before locking, all arm checkpoints and hashes frozen, independently compared on one never-tuned test.
D07 frozenC2C3PairedCEOrCounterexample — original repaired C2, frozen C2, frozen C2C3 on SAME lockbox corpus; no cross-dataset CE comparison to historical 4.5966.
D08 originalPunctured9CapacityMatchedRouterAdapter — 2d vs 3d/2 original source router input widths reconciled under predeclared parameter/compute budget.
D09 originalPunctured9TranslationAndRelativePhaseSourceAction — 9-point F3² action on actual learned source state with centre gauge, negative controls.
D10 frozenC3SquareIndependentLockboxAndMechanism — separately preregistered three-arm architecture comparison; never reuse F5 after seeing its results.
D11 originalC2C3FinalStudentAgdaBidi — actual source student observables and Agda formal state/transition commute both ways for named inputs.
D12 originalC2C3MeasuredQualityComputePareto — full original resource/quality comparison, no FLOP/parameter count alone as performance proof.

These names form the formal ledger of what REMAINS. A source file or mathematical donor may already implement part of a lemma; the selected original source weld is still open until the exact signature and evidence are recorded.

## Cross-lane programme X369-A to X369-G (separate physical frontiers)

X369-A c3x3ExactCyclotomicCharacterConvolution — A01-A06 same carrier. Finite exact evidence exists; Agda full weld OPEN.
X369-B atomic369PhysicalOrbitalRepresentationIntertwiner — map from 369 labels to actual antisymmetric Hamiltonian eigenstates, shell energies and calibrated source; OPEN.
X369-C nsPeriodicGalerkinNonlinearPhaseConvolutionBidi — integer Z³ Fourier mode and nonlinear Leray-projected source solution, not a modular-3 quotient; OPEN.
X369-D ymOriginalWilsonC3BlockFourierTransport — actual SU(N) lattice Wilson fields and coarse block translations/Haar/Ward/RG, not index symmetry; OPEN.
X369-E quantumC3TritQutritFourierIntertwiner — actual Hilbert operator on selected qutrit register, unitary intertwiner and physical gate/readout; OPEN.
X369-F lilaGrokkingC3PhaseVsC2RepairedRepresentations — all C and D evidence; no learned neural C3 claim before mechanism tests. OPEN.
X369-G monster369RegularTracePhaseVsRiemannZetaTypeBoundary — type-separate cyclotomic omega, Monster multiplicity phases, analytic zeta/Epstein etc; actual same-object map or explicit no-go required. OPEN.

## Phase, delivery, and proof order

| Phase | Agda deliverable | Parallel Leech deliverable | Exit |
|---|---|---|---|
| P0 provenance | chosen module/branch hashes, currently accepted finite declarations | host detached fixes joined to PR #4; exact 55/55 receipt | working checked-out SHA and PR head agree |
| P1 exact algebra | A01-A06 Agda full kernel source | Python four finite C3² tests remain regression | one same-carrier Agda proof (not isolated integer test) |
| P2 action and negative controls | B01-B05 and named source signatures | full hidden covariance uncertainties, recurrent C2 history | simultaneous/relative phase distinction falsifiable on original state |
| P3 learned mechanism | C01-C08 interface and counterexamples | task-labelled learned u, equivariance, composition, causal paired intervention | success or independently reproducible negative result |
| P4 2-arm screen | D03-D05 source contract | genuine untouched development data, two-seed 24-step screen | F4 per-seed CE/checkpoint receipts |
| P5 frozen F5 | D06-D07 and D11-D12 same-model proof interfaces | independent one-time lockbox, 32+ replay, Pareto | F5 admission or counterexample |
| P6 full 9-sheet | B04, D08-D10 source law and matched adapter | new 3-arm C2/C3/C3² comparison with separate data | genuine C3² claim decided, not inherited from F4 |
| P7 cross-lane | X369-A-G domain-by-domain same original map | independent physical or semantic empirical sources | no claim of physical universality from finite G-action |

Operational rule: use repo AGENTS.md / Docs/AgentOperationalNotes.md and pinned Agda 2.9 script wrapper, DASHI_NO_TMUX=1 as specified by repository; inspect original owner before adding duplicate lemmas. Every purported closed lemma needs exact source path, theorem statement, command, checker version, kernel log and a negative test if possible. Avoid a new PR per subproblem. Existing Agda PR #1442 is the neural/semantic formal rollup; separate Clay/NS/quantum physical owners stay on their original respective PRs.

## Explicit decision outcomes

If F2/F3 fail, the learned circuit assertion is unsupported even if F4/F5 C3-invariant features reduce CE. If F2/F3 pass without F4/F5 predictive gain, report a mechanism with no demonstrated advantage at the chosen budget. F4 development improvements are biased by best-step selection; F5 must independently confirm on a locked same-corpus control. F6 requires new matched capacity/compute and cannot be folded into the existing 2-arm F4 result after the fact. Physical continuum statements, Monster/Leech, D4/S3 and semantic triadic-face interpretations require separately selected input/output intertwiners and are NOT proved by these finite group identities.

## 2026-11-14 maximum-cut implementation receipts — source-written versus accepted

**Agda sources added on this same PR #1442:**

| Source file / declaration | Proposed gate partially paid | Actual state |
|---|---|---|
| `DASHI/Cognition/PNF/X369FiniteTorusAndRouterActionWeldExact.agda`: `sameTorusFirstCharacterEigen`, `sameTorusSecondCharacterEigen`, `sameTorusFirstActionOrderThree`, `sameTorusSecondActionOrderThree`, `sameTorusActionsCommute` | A01 selected common torus + eigenaction | SOURCE-WRITTEN, selected Agda kernel OPEN |
| Same file: `directedChannelsSimultaneousC3Invariant` and explicit `relativePhaseOriginalChannels` / `relativePhaseShiftedChannels` | B01/B02 symbolic source polynomial and one-sided witness | SOURCE-WRITTEN on ℕ semiring only; signed-real original activation weld OPEN |
| `DASHI/Cognition/PNF/X369OriginalTorusCharacterOrthogonalityExact.agda`: `originalTorusC3SquareCharacterOrthogonality` | A02 original torus exact 9x9-character orthogonality | SOURCE-WRITTEN in Z[omega], 81 explicit cases, kernel OPEN |
| `scripts/check_x369_finite_original_torus_maxcut.sh` | A06 selected leaf checker entrypoint | IMPLEMENTED; actual Agda 2.9/authoritative pinned receipt OPEN |

The 81 algebraic character-pair orthogonality cases were also checked independently by an exact integer Z[omega] verifier outside Agda (81/81). This is NOT proof that the just-written Agda module typechecks; it is a preflight arithmetic receipt only. A03 convolution/inverse, A04 Parseval/real descent, A05 centred puncture bijection, A06 complete kernel acceptance remain OPEN until genuine same-carrier Agda proofs/replay exist.

**Leech PR #4 corresponding source implementation (commit 45a8bbc and later):** F1 full hidden d×d/cross-triad/cluster bootstrap; original source C3/C3² feature-action report; nonpersistent routing-site intervention hooks; F3 causal CE runner requiring frozen original F4 candidate; optional F6 three-arm screen using new `punctured9_wave_matched` nonlinear fixed feature lift and prior official F4/F5 receipt exclusion. The three-arm new geometry has same 2d router *parameter dimensions*, but not demonstrated equal effective feature capacity. A further F2 held-out task-orbit supervised linear-phase readout probe is a source-implementation deliverable only; it is not an actual trained original model Fourier circuit, and its manifest is source-attested until independently verified.

**Exact remaining Agda lemmas after source implementation (none silently closed):**
- A03 `c3x3FourierConvolutionSameCarrier`: full normalized convolution theorem + inverse on original nine-point carrier
- A04 `c3x3ConjugationParsevalAndReality`: conjugate/Parseval and all nine Fourier coefficients
- A05 `c3x3PunctureCentreGaugeBidi`: nine-sheet and pointed-eight real source chart with retained centre
- A06 `c3x3AgdaKernelSelectedSourceAccepted`: pinned repository-checker receipts and no hidden assumptions
- B01/B02/B04/B05: transport polynomial and Fourier pair mathematical actions to *actual signed real model*, selected router source, top-k/tie and recurrent history
- C01–C08: real task group action, supervised readout limitation, unseen actual learned phase composition, causal CE, semantic validation and original consumer BIDI
- D01–D12: full original model recurrent evidence, documentary data independence, matched CE, frozen F5, three-arm F6 separate final, compute Pareto
- X369-B/C/D/E/G: atomic, NS, YM, quantum and Monster physical/semantic source maps, still independent OPEN frontiers

**Kernel command:** `DASHI_NO_TMUX=1 bash scripts/check_x369_finite_original_torus_maxcut.sh`, which delegates to the existing pinned `scripts/run_agda29_parallel_check.sh`; subsequently run authoritative Track A flake checks before promotion. No Agda checker was executable in the current environment, and no fresh kernel result is claimed.

**Formal status:** P1 mathematical source progressed materially, Agda acceptance still OPEN; P2/P3 source code implemented in Leech, neural evidence OPEN; P4/P5 original GPU/data gates OPEN; P6 matched three-arm code implemented but native/new-data and independent final F6 OPEN; P7 original physical source gates OPEN. Keep mathematical proof, experimental code, source-level tested invariants, real GPU measurements and interpretive claims in separate status columns.

### Additive formal P1 closure source and full F6 implementation (2026-11-14)

- `DASHI/Cognition/PNF/X369OriginalTorusGroupLawExact.agda` now defines `addResidue3`, `inverseResidue3`, `originalTorusAdd`, `originalTorusInverse`, `originalTorusAddAssociative`, `originalTorusAddCommutative`, `originalTorusInverseRight`, `originalTorusInverseLeft`, and original generator translations, all directly on `FiniteThreeCycleTorusExact.Torus3x3`. The finite 27 associativity / nine commutativity / three inverse arithmetic cases were independently checked outside Agda. **SOURCE-WRITTEN, kernel OPEN**.
- The Agda selected checker is `DASHI_NO_TMUX=1 bash scripts/check_x369_finite_original_torus_maxcut.sh`, registering original group law, paired characters and exact 81-character orthogonality. The authoritative pinned Track A promotion remains separate.
- Leech PR #4 now also has `scripts/score_frozen_three_arm_c3square_f6.py` and `tests/test_frozen_three_arm_c3square_f6.py`. This adds a separately frozen F6 three-arm *final* scorer, SHA-binds official earlier F4/F5 receipts, excludes previously evaluated tokens, and includes the original repaired C2 on the same independent test. It has not run on original RX580 or a genuinely unseen documentary corpus. **F6 empirical exit OPEN**.
- The actual original LM F2 source-function readout has been implemented as `scripts/audit_trained_c3_task_orbits.py`: a separately trained supervised two-coordinate readout of frozen original-layer activations on externally supplied task-defined orbit triples, with new orbit/doc IDs and heldout composition/equivariance diagnostics. No independently certified semantic C3 input action or autonomous neural Fourier addition mechanism is claimed; F2 and F3 scientific result remain OPEN.
- The older master document `Docs/roadmaps/LILASophonticMoESOTAMaxCut20261111.md` may have historical X369 status rows. It does not exist at the current diverged #1442 branch head, so this PR keeps the full X369 ledger here rather than copying a conflicting stale master file. Reconcile with master before promoting and update the old master index as part of the non-destructive PR rebase.


## 2026-11-14 next formal max-cut: A03–A05 exact coefficient witness, original-centre BIDI and F2 gauge correction

**Owner:** Existing DASHI Agda neural-formal PR #1442. **Companion:** Existing
LeechTransformer neural PR #4; these are not new PRs. Historical Clay
rollup PR #1499 and independent physical owners are not reclassified as
neural proof owners.

### Source-written Agda A05 original-carrier advancement

New `DASHI/Cognition/PNF/X369OriginalTorusPointedAffineBidiExact.agda`
uses the **already existing** `FiniteThreeCycleTorusExact.Torus3x3` and
`X369OriginalTorusGroupLawExact`. It does not construct a competing
nine-element torus. Its explicit conditional algebra parameters are an
additive operation, a difference operation, zero, difference
cancellation, self-difference zero and relative-difference gauge
cancellation. These are **hypotheses**, not supplied physical facts or
implicit postulates.

The new exact declarations and their precise scope:

| Name | Original-carrier theorem / condition | Status |
|---|---|---|
| `originalPointedReopenBidi` | At every original torus point, reopen retained centre + centre-relative offset and obtain the original sheet value | SOURCE-WRITTEN, conditional, selected Agda kernel OPEN |
| `originalOffsetsCentreIsZero` | Pointed relative offset vanishes at distinguished origin, given `selfDifferenceZero` | SOURCE-WRITTEN, conditional, kernel OPEN |
| `originalPointedTranslationGaugeLaw` | Translate an original sheet and subtract the **new** origin equals translating centre-relative offsets followed by re-gauge; uses the actual original torus add/inverse | SOURCE-WRITTEN, conditional, kernel OPEN |
| `c3x3PunctureCentreGaugeBidi` | Upgrade conditional all-nine sheet result to original eight-puncture/Fourier-pair/independently retained centre, same coefficients and source waveform | OPEN — not silently solved by the three declarations |

The selected leaf checker now includes this fourth source:
`DASHI_NO_TMUX=1 bash scripts/check_x369_finite_original_torus_maxcut.sh`.
Actual Agda 2.9 kernel execution, transitive safety and authoritative Track
A acceptance were NOT available in this execution environment.

### Exact companion coefficient results on the Python original site order

Leech PR #4 adds
`scripts/certify_x369_original_torus_maxcut.py` and
`tests/test_x369_original_torus_maxcut.py`, reusing
`models/punctured_nine_wave_prior.SITES`, with integer-pair
`Z[omega]` arithmetic and no floating approximation. Locally the
source-matched finite harness passed its three regression cases and
reported:

- **A03**: 81 inverse Fourier matrix coefficients; 729 bilinear
  convolution and 729 product/frequency-convolution coefficients. The
  basis-expansion argument justifies arbitrary finite inputs at the
  Python algebra level.
- **A04**: 81 sesquilinear Parseval coefficients; 81 real-conjugation
  coefficients; all 729 centred Gram coefficients across nine
  translations, rather than diagonal-only samples.
- **A05**: Nine basis centre/offset recoveries, 648 single-translation
  gauge coefficients, 5,832 induced composition coefficients.
  Counterexample to naive punctured-eight norm preservation:
  squared norm 8 becomes 1 under original-centre re-gauge by (1,0).

These exact finite results are **not Agda theorems**, not proof that
`SITES` and the original Agda enumeration are definitionally the
same object, and not a neural, semantic, Leech-lattice, NS, YM or
Monster theorem. They provide an executable normalization/orientation
oracle for formal A03–A05, with an explicit falsification target.

### Next Agda exact lemmas (A00–A06)

| Exact name to close | Input/parent owners | Required output |
|---|---|---|
| `x369PythonSignedSitesToOriginalTorusBidi` (new A00) | `punctured_nine_wave_prior.SITES`, original `Torus3x3` and canonical mode ordering | Both-way 9-site table and character frequency/sign convention, not simply matching cardinality |
| `c3x3SameCarrierGroupLaw` A01 | `X369OriginalTorusGroupLawExact` | Pinned kernel proof and original translation equivalence |
| `c3x3CharacterOrthogonalityOnOriginalCarrier` A02 | `X369OriginalTorusCharacterOrthogonalityExact` | 81 exact Z[omega] cases, freshly checked |
| `c3x3FourierConvolutionSameCarrier` A03 | A00/A01/A02, `Eisenstein` multiplication and group convolution | Original FT inversion, convolution-multiplication and pointwise-product frequency convolution, correctly factor 9 |
| `c3x3ConjugationParsevalAndReality` A04 | A03 and selected `Eisenstein` conjugation | All nine modes, full centred/DC treatment, real descent and 9-point Parseval |
| `c3x3PunctureCentreGaugeBidi` A05 | new conditional pointed BIDI + A00/A03/A04, source wave basis | Original eight puncture+independent centre ↔ nine amplitudes ↔ four real character pairs, with re-gauged translations and true norm |
| `c3x3AgdaKernelSelectedSourceAccepted` A06 | Selected source check + pinned toolchain | Zero postulates/metas in selected path, exact checker version, log, pinned SHA, authoritative Track A |

There is no Agda claim beyond the actual conditional declarations. A
finite integer-coefficient checker is an independent oracle, not an
imported formal proof.

### F2/F3 empirical ownership and exact remaining source obligations

The companion Leech PR #4 additionally introduces
`certify_c3_task_orbits_original_tokens.py` and six negative/positive
action-regression cases. A token-position C3 input action can be
structurally verified on supplied original token IDs, while supplied
external label semantics and logit consumers remain **unverified**.
The frozen hidden readout now accepts the declared **absolute phase
labels** for training and held-out composition scoring. A valid orbit
may start at 1 or 2; otherwise a perfect character can be falsely
scored as noncompositional. A three-orbit numerical witness gave
mean false defect around 1.1547 before alignment, approximately zero
after alignment. F2/C03–C08 and F3 source-semantic/causal results are
not thereby closed.

New exact formal handoffs:

- `originalC3TaskMachineActionLabelBidi`: from the machine-checked
  original token permutations and externally labelled phase action to
  Agda's finite action, **conditional on** a verified label-source map
  (OPEN).
- `originalC3OrbitAbsoluteGaugeCompositionBidi`: define phase
  label transport under orbit base changes, and prove that composition
  is tested after reindexing by the absolute label rather than the
  orbit's enumeration index (OPEN in Agda; tested numeric negative
  control in Leech).
- `originalC3HiddenToOutputConsumerIntertwiner`: chosen checkpoint
  site, recurrent memory, phase decoder, task label and downstream
  logits commute on the **actual trained model** (OPEN).
- `learnedC3RelativePhaseCausalExcessLoss`: predeclared paired
  intervention over named fresh documents beats proper
  displacement-matched and memoriser controls (OPEN empirical).

### F6 tightening and phase exit audit

`score_frozen_three_arm_c3square_f6.py` now refuses a one-seed final
selection: at least two precommitted **paired** development seeds are
necessary. Distinct F4/F5/F6 source/document sets, exact SHA/provenance,
matched effective rank/compute, final never-tuned evaluation and actual
learned F3² mechanism remain **OPEN**. This is procedural acceptance,
not F6 neural performance evidence.

P0: current branch/source revisions and latest full test receipts OPEN.
P1: A01/A02 source plus conditional A05 partial progressed; A00/A03/A04/full
A05 and kernel A06 OPEN. P2: actual row provenance and original recurrent
source statistics OPEN. P3: structural F2 input action and corrected
phase-score code present; real semantic F2/F3 OPEN. P4: fresh matched
two-arm GPU/data OPEN. P5: F5 independent final/recurrent replay OPEN.
P6: two-seed F6 guard present; independent three-arm scientific evidence
OPEN. P7: original physical cross-lane source maps OPEN.

**Do not promote mathematical code, a Python exact certificate, a
source-written Agda conditional theorem, and an independently
trained neural mechanism as the same level of acceptance.**


### Additional finite F2 counterexample and normalization source

`DASHI/Cognition/PNF/X369OrbitAbsolutePhaseGaugeExact.agda` now reuses
the **existing** `DASHI.Algebra.TriadicDepthOneCharacters.C3Phase`,
`multiplyPhase`, and `conjugatePhase` without making a second cyclic
group. The exact source declarations are
`absolutePhaseNormalizeCancelsBase` (all nine phase/base cases),
`absolutePhaseCompositionAfterReindexing` (character composition
after removing a nonzero orbit origin),
`shiftedBaseNaivePhaseSquareIsPhase2`, and
`shiftedBaseNaiveCompositionCannotEqualPhase1` (a finite no-go:
multiplying the shifted base `phase1` by itself produces `phase2`,
not `phase1`). The selected Agda checker now includes this module.

**SOURCE-WRITTEN ONLY, kernel still OPEN**. The formal normalized
character result closes a finite *specification/counterexample* lane,
not an actual learned network's supervised phase, semantic output
equivariance, or causal mechanism. The corresponding Leech readout
change corrects the empirical scoring semantics, but its real-model
evaluation is still unrun.


## 2026-11-14 A00–A05 next formal tranche — source written, kernel acceptance pending

The owner remains **DASHI Agda PR #1442**, with neural and empirical original owner **LeechTransformer PR #4**. No extra rollup was created. This tranche adds the following source modules to the selected `scripts/check_x369_finite_original_torus_maxcut.sh` entrypoint:

| Original Agda source module | Exact declared theorems | Acceptance status |
|---|---|---|
| `DASHI/Cognition/PNF/X369OriginalSignedSiteOrderBidiExact.agda` | `sourceSlotRoundTrip`, `originalTorusPointRoundTrip`, `sourceFirstTranslationOriginalWeld`, `sourceSecondTranslationOriginalWeld`, original character phase signs | SOURCE-WRITTEN; selected kernel OPEN |
| `DASHI/Cognition/PNF/X369OriginalTorusSpectralBasisExact.agda` | `encodeOriginalResidueAddition`, `originalFirstCharacterAdd`, `originalSecondCharacterAdd`, `originalCombinedCharacterAdd`, `originalDeltaFourierConvolutionCoefficient`, `originalDualInverseCoefficient`, `originalParsevalBasisCoefficient`, `originalRealConjugationBasis` | SOURCE-WRITTEN; basis coefficient proofs, kernel OPEN |
| `DASHI/Cognition/PNF/X369OriginalPointedEightSlotBidiExact.agda` | `originalEightDecodeEncodeAt`, `originalEightEncodeDecodeAt` over all nine actual original slots, using explicit centre+eight slot record with cancellation hypotheses | SOURCE-WRITTEN; conditional spatial BIDI, kernel OPEN |

The new A00 module is an **index representation of the Leech Python SITES ordering**, not a second nine-element group. The mapped points are

`[(0,0),(-1,0),(1,0),(0,-1),(0,1),(-1,-1),(1,1),(-1,1),(1,-1)]`.

An independent direct GitHub source-blob comparison checked the live Leech `models/punctured_nine_wave_prior.py` blob `d0d890c17ecaf18ea3efa14833405cd116038511` against the live A00 Agda blob `1007f95db7f5fea41bf57dfacda57111a3971893`: **all nine exact signed-index entries agree**. This is a source-table verification, not kernel acceptance or model-state refinement.

### Remaining exact formal obligations, in dependency order

**A00** `x369PythonSignedSitesToOriginalTorusBidi`: source table matched; Agda kernel and orientation/normalisation witness selected replay open. The source site order differs from `Fourier.canonicalModes` lexicographic enumeration, so the proof must preserve permutation rather than presume identical list ordering.

**A01/A02** original group law and 81-case character orthogonality: source-written in previous files; fresh Agda 2.9 replay still open.

**A03** `c3x3FourierConvolutionSameCarrier`: the new spectral module targets pointwise additive-character multiplicativity and the unnormalised delta Fourier coefficient, with 81 inverse basis coefficients. Still needed: the checked coefficient-ring multiplication/normalisation, a formal arbitrary **nine-site function** expansion/finite distributivity result and all-function convolution (plus the 1/9 inverse normalization convention). The Leech exact integer coefficient oracle remains independent.

**A04** `c3x3ConjugationParsevalAndReality`: the new spectral module states 81 sesquilinear delta basis Parseval cases and 81 conjugation basis cases. Still needed: formal arbitrary-function complex sesquilinear extension, all Fourier/DC components, real descent and the zero-mean nine-sheet bilinear norm (all 729 Gram coefficients checked only in the independent Python oracle).

**A05** `c3x3PunctureCentreGaugeBidi`: now has explicit source-order spatial eight+centre decode–encode in both directions under stated algebraic cancellation. Still needed: instantiate selected exact Eisenstein coefficient ring, full four conjugate real Fourier pair transform, original pointed-eight ↔ wave chart, true norm preservation on **centred nine** (not naive punctured-eight) and the source translation re-gauge theorem in the same Fourier basis. Actual signed floating-point Leech input/consumer mapping remains separate.

**A06** `c3x3AgdaKernelSelectedSourceAccepted`: pinned `DASHI_NO_TMUX=1 bash scripts/check_x369_finite_original_torus_maxcut.sh` successful trace, transitive assumption audit and authoritative Track A checker. **Not executed in this environment.** Do not declare A00–A05 kernel accepted on source-writing alone.

**B01–B05/F2/F3**: the Leech companion now has an actual router-site matched random perturbation preserving both norm and displacement relative to the cyclic action. This improves the negative control. No actual trained checkpoint causal CE or independent task/label input action was provided. `originalC3HiddenToOutputConsumerIntertwiner`, `learnedC3RelativePhaseCausalExcessLoss`, and all original recurrent/semantic welds remain open.

**F4/F5/F6**: the live PR diff carries no `.pt`, `.npy`, `.npz`, or similar original checkpoint/data artifacts. Therefore the original physical development/frozen tests have not been executed in this tranche; do not manufacture a positive CE result. Freeze selection on development before using independent F5 or F6 final.

### Phase deliverables and release sequence

- **P1a:** A00 source/kernel, original carrier conventions and A01/A02 replay.
- **P1b:** A03/A04 arbitrary-field theorem, ring representation, normalized inverse and Parseval.
- **P1c:** A05 original spatial eight ↔ exact Fourier four-pair+centre, with centred norm and source re-gauge.
- **P2:** S1/S2/S3 original recurrent source and covariance uncertainty with documentary row provenance.
- **P3:** F2/F3 independently meaningful source action, trained h/rho/readout, causal CE excess and negative controls.
- **P4/P5/P6:** development-only matched two-arm, once-only independent F5, separate once-only matched F6.
- **P7:** domain-owner X369-B/C/D/E/G physical map and assumption checks; no propagation from finite ternary index coincidences.

Preserve **one active X369 formal PR (#1442)** and **one neural PR (#4)**. DASHI branch is still diverged from master; perform non-destructive merge/rebase with transitive type-checking only when the golden checker can execute. No scientific closure is inferred from absence of CI checks.

## 14 November 2026 host replay — selected eight Agda leaves pass, current remote-head replay pending

A host run against the source revision **`7c549c9892f5`**, on local testing worktree `test/pr1442`, reports that the **selected** `scripts/check_x369_finite_original_torus_maxcut.sh` using `scripts/run_agda29_parallel_check.sh` completed with exit 0, zero errors and zero warnings. Its exact per-leaf reported checks:

| Selected leaf | Host count | Host disposition |
|---|---:|---|
| `X369OriginalTorusGroupLawExact` | 64 | PASS |
| `X369FiniteTorusAndRouterActionWeldExact` | 157 | PASS |
| `X369OriginalTorusCharacterOrthogonalityExact` | 194 | PASS |
| `X369OriginalSignedSiteOrderBidiExact` | 158 | PASS |
| `X369OriginalTorusSpectralBasisExact` | 196 | PASS |
| `X369OriginalPointedEightSlotBidiExact` | 159 | PASS |
| `X369OriginalTorusPointedAffineBidiExact` | 65 | PASS |
| `X369OrbitAbsolutePhaseGaugeExact` | 18 | PASS |

The **1011** checks above are the host's count of selected leaf checks and are not 1011 newly proved independent general theorems. A00, A01/A02, and the finite delta-basis cases of A03/A04 and conditional A05 spatial BIDI now have a positive **host-reported kernel receipt** at that tested worktree.

**Important branch reconciliation:** the testing branch `test/pr1442` has not been pushed as a named branch to GitHub. The connected remote PR branch still showed Agda 2.9 parser issues in the imported original files despite the host's clean local run. To avoid leaving the fixes stranded on an untracked local worktree, this continuation synchronized the same described compatibility patch directly into the existing PR #1442 branch:
1. `DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda`: binder `field` → `fld` (preserving the actual `field` record declaration), `FiniteTorusBoundary : Set₁`.
2. `DASHI/Biology/BalancedTernaryFourierModeExact.agda`: `field` binder → `fld`; `FourierModeBoundary : Set₁`; remove unsupported/unused Equality `cong` import.
3. `DASHI/Cognition/PNF/X369OriginalSignedSiteOrderBidiExact.agda`: clean Equality `cong` import.

**A fresh Agda 2.9 replay of the later remote PR head is still mandatory.** Reassigning the earlier local checker result to unexecuted later commits would violate source/verification provenance; no whole-repository/Track A proof is claimed.

### Revised exact formal gates

- **A00 / site & sign:** original Python SITES ↔ existing nine-point torus BIDI, exact positive and negative generator phase conventions. Host-reported kernel PASS for the selected leaf; remote-head replay OPEN.
- **A01/A02 / group & orthogonality:** finite original group and 81-character normalisation selected leaf host PASS, current remote-head replay OPEN.
- **A03 / original arbitrary-field Fourier:** delta-character multiplicativity and basis inverse/convolution leaf host PASS. Required next named lemmas: `originalNineSiteFieldExpansion`, `originalEisensteinFiniteDoubleSumInterchange`, `originalAllFieldFourierConvolution`, `originalNineSiteInverseScaledByNine`. State ring identities and exact 1/9 convention explicitly; do NOT promote basis tests into these general theorems.
- **A04 / full Parseval and real descent:** 81 sesquilinear Parseval/reality delta coefficients source host PASS. Next: `originalAllFieldParsevalBilinear`, `originalConjugateFrequencyRealityAllSites`, `originalCentredNineSheetGramInvariant`. Reuse original orthogonality and character ring rather than introducing a synthetic torus.
- **A05 / original eight+centre ↔ real Fourier four-pair:** original spatial eight+centre pointwise BIDI leaf host PASS under explicitly stated affine cancellation. Next: `originalEightCentreToFourWavePairs`, `originalFourWavePairsToEightCentre`, `originalCentredNineNormUnderReGauge`, and source `signedFloatWaveConsumerRefinement`.
- **A06 / authoritative Track A:** selected Track B acceptance is now host-reported, not equivalent to full transitive kernel audit/whole-repo acceptance. Need a current-branch pinned Agda 2.9 zero-warning log, assumptions/termination/sort audit and integration with master without force rewriting the many intervening master changes.
- **F1/F2/F3** companion Leech owner: host reports 9-row pooled C3 bootstrap with layer-1 CI above 0.05, but NOT a bootstrap of the original full d×d hidden commutator; the new Leech code now performs both full-matrix and pooled row bootstrap. Task-defined original model consumer/causal agreement remains unmeasured.
- **F4/F5/F6:** no original fresh corpus is included in a PR source diff; Leech now has a SHA-bound and 16-gram-distinct real source-document token-split generator with a provisional path if the historical document inventory is unavailable. Document identity must not be inferred merely from token nonoverlap.

**Next handoff:** run `DASHI_NO_TMUX=1 bash scripts/check_x369_finite_original_torus_maxcut.sh` on the pushed PR #1442 head; run the Leech full native test command on the latest PR #4 head; separately rerun F1 from the existing TrueNAS residual `.npy` files to generate **actual full-hidden** row-cluster confidence intervals. Do not consume frozen F5/F6 sets to explore source actions.

## Later 14 November 2026 replay — current selected Agda head accepted, full hidden C3 refuted

### Corrected selected Agda Track B acceptance

Host subsequently ran `scripts/check_x369_finite_original_torus_maxcut.sh` on the **synchronized branch revision `81542ade028f`** after the Agda 2.9 keyword/universe import repairs were in the PR itself. Report: **8/8 selected modules checked, exit 0, 0 errors, 0 warnings**. Individual checks: group 64, router 157, orthogonality 194, original site index BIDI 158, spectral basis 196, explicit eight-slot BIDI 159, affine BIDI 65, absolute-phase gauge 18. This supersedes the earlier ambiguity between local `test/pr1442` and the remote source head; it does NOT establish all-field A03/A04/A05, whole-repo Track A, or physical/neural mechanism.

Still exact unproved:
- **A03:** `originalNineSiteFieldExpansion`, `originalEisensteinFiniteDoubleSumInterchange`, `originalAllFieldFourierConvolution`, `originalNineSiteInverseScaledByNine`.
- **A04:** `originalAllFieldParsevalBilinear`, `originalConjugateFrequencyRealityAllSites`, `originalCentredNineSheetGramInvariant`.
- **A05:** `originalEightCentreToFourWavePairs`, `originalFourWavePairsToEightCentre`, `originalCentredNineNormUnderReGauge`, `signedFloatWaveConsumerRefinement`.
- **A06:** authoritative master integrated whole-programme Track A, original carrier and assumption closure. Preserve original YAML/golden source ownership and avoid non-destructive history rewrites.

### F1 cross-lane negative result, proper scope

Host ran the **actual 384×384** covariance bootstrap on nine source-row clusters with 1999 draws. Reported primary full hidden defect:
- Layer 0: `D_C3=1.33227`, familywise CI `[1.33199,1.35126]`.
- Layer 1: `D_C3=1.41233`, familywise CI `[1.41198,1.41259]`.
- Both exceed tolerance `0.05` in the selected fixed hidden coordinate action. Cross-triad `||C-offblockdiag||F/||C||F`: `0.9354` and `0.9926`. These are Frobenius covariance fractions, **not percent total variance**. Independent historical source-document identity has not been established, so the row-cluster population inference remains conditional.

For an exact order-three orthogonal permutation `P`, with empirical PSD covariance `C`:
```text
D = ||C-PCP^T||F/||C||F <= sqrt(2).
Frobenius overlap = 1 - D^2/2.
Reynolds projection R=(C+PCP^T+P²C(P²)^T)/3.
||C-R||F/||C||F = D/sqrt(3).
```
The reported point values therefore imply overlap `[0.112528, 0.002662]` and noninvariant Frobenius components `[0.769186, 0.815409]`. They **disprove approximate covariance equivariance for the particular native coherent triad generator on the measured residuals**, not all possible learned bases or group actions. A finite original-torus theorem is not automatically a learned hidden-state action.

Leech PR #4 now owns a seeded `audit_x369_f1_rank_and_orientation_null.py` to quantify the PSD ceiling, Reynolds projection, covariance effective rank and an order-three *mixed-triad-orientation* null (each triad uses +1 or -1 nonidentity generator). This is a matched spectral negative control, not a physical or neural intertwiner. Five focused tests passed locally; original-model/TrueNAS rerun is still an empirical gate. No new synthetic Agda group or fabricated experimental proof should be created.

### Empirical release ledger

- **F1:** full hidden source covariance refutation for fixed triad action; compare rank/orientation, document provenance and alternative predeclared representations before any claim of learned group.
- **F2/F3:** original frozen checkpoint, independently semantic C3 task action, source hidden readout and actual output consumer, paired causal CE against equal-displacement random null.
- **F4/F5/F6:** source-bound truly fresh documents, non-overlapping 16-token windows and original model training; reserved independent holdouts must remain untouched.
- **P0:** Host reports 103/103 Leech tests across 22 suites on a working tree referencing `4761459` with a local Python multiline syntax correction. The correction has since been pushed to the existing PR branch; later source changes require a new current-head replay. Do not label those 103 tests as an execution of a subsequent GitHub head.


## 15 Nov 2026 — source formal candidate and 12-draw frozen F3 ensemble (post-09:20)

**Host prior-head acceptance:** Leech PR #4 commit `33a34876bf13`: full native 125/125 across 26 suites, portable 37/37, targeted original mixed-C3 source + CE tests 12/12. Agda PR #1442 commit `272bb1be33ee`: selected original torus 8/8 leaves accepted on Agda 2.9. Independent host float64 original source polynomial test over 4×384×8 reported coherent/polynomial max absolute squared-energy error 9.09e−13 and mixed/polynomial 4.55e−13. These acceptance receipts do not automatically apply to later GitHub heads.

**New actual Agda module drafted, on existing PR #1442:** `DASHI/Cognition/PNF/X369OriginalDirectedTriadC3PolynomialCandidate.agda` uses `Data.Integer.Tactic.RingSolver.solve-∀` for six-variable original directed triadic correlation displacement identities, and structurally inducts over arbitrarily many original triads with arbitrary independent ±120° orientation and original per-expert history coordinates. It contains these proposed lemma names:
```text
originalTriadRotationSquaredDisplacementEqualsTwoQ
originalTriadInverseRotationSquaredDisplacementEqualsTwoQ
originalDirectedTriadC3DisplacementSquaredFactors
originalDirectedInverseC3DisplacementSquaredFactors
originalDirectedTriadMixedOrientationEnergyEqualsCoherent
originalBlockMixedEqualsCoherent
originalMixedTriadC3RouterFeatureEnergyEqualsCoherent
```
This source is **NOT AGDA KERNEL CHECKED** in the received host evidence. The standalone new runner `scripts/check_x369_original_directed_c3_polynomial_candidate.sh` requires Agda 2.9 validation. It deliberately leaves the accepted 8-leaf Track B suite untouched. This candidate proves only an integer polynomial analogue if the kernel accepts it; full abstract-real scalar transport and exact trained neural consumer remain separate and OPEN.

**F3 next source:** `scripts/audit_x369_f3_mixed_orientation_ensemble_ce.py` on Leech PR #4 does a frozen original model CE comparison using **12 predeclared independent mask draws** versus a single coherent C3 action, with separate seed41 (best step 0) and seed42 (best step 24), document-row paired bootstrap and deterministic whole-original-source SHA/provenance receipts. The original 16 F3 probe rows are already viewed: this is an exploratory sensitivity result, never a calibrated null-test p-value or final F5 release. F5 reserved token bytes are not loaded by the new scorer; original old F3 overlap-producer *did* inspect them, but did not score F5 CE. Five new test contracts are included and need new-head native acceptance. The **physical RX 580 new ensemble CE is not yet measured in evidence supplied**.

**Decision order:** (1) exact new-head Leech native and portable acceptance; (2) isolated Agda candidate checker, repair parser/ring normalizer if needed and only then add the kernel proof receipt; (3) physical seed41/42 frozen 12-draw F3 CE on previously viewed probe (with no F5 raw data); (4) independently task-labelled new-document F2/L0 original spectral action; (5) separately calibrated zero-initial C3 residual feature F4 on new documents; (6) retain F5 final CE seal and A03–A06 arbitrary-field/full neural weld OPEN.

Attribution: original Leech-LILA trained model owned by original author; DASHI proposed integer ring proofs and C3/C3² finite-torus kernel proofs are mathematically distinct; prior negative F4-C2 development result not overwritten by the new F3 exploratory plan.


## 15 Nov integrated maximum cut: binary/ternary zero, punctured gluing, Monster-C3/S3, time/tetration, SLR and grokking

**Ownership and acceptance:** Keep all this source and formal work on existing Agda PR #1442, and original student experiments on Leech PR #4. Consume existing Monster/FLM PR #1472 and SensibLaw/SLR spaCy producer, rather than asserting they have merged. Original Leech 383ad3f35350 had **130/130 native tests and 37/37 portable**, host-reported; original Agda 2c079f536028 had **8/8 selected torus leaves**. The isolated NEW polynomial candidate failed Agda with Nat 2 where integer ℤ is required; e909cf6 replaces all four integer multipliers with (+ 2), and 3e38f04 replaces the two integer list-fold bases with (+ 0). **Agda kernel rerun and solver closure OPEN.** Local integer Python exhaustive checks are not Agda-kernel acceptance.

### Z — Binary versus ternary and the typed meanings of zero

Reuse these already-existing exact owners:
- DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda, DASHI/Codec/BalancedTritBitFibre.agda: support-plus-sign binary **roundtrips** a balanced trit. A Boolean support-only/absolute-value quotient loses sign; binary representation in general does **not** necessarily lose sign. On one trit, antipode and successor satisfy the dihedral S3 law.
- DASHI/Reasoning/LeechParityC3ActionKernelExact.agda: inversion of the whole triple and cycling of its three sites **commute**; their faithful combined product may be C6. That is a different action, not the prior S3.
- DASHI/Foundations/SignedZeroTernaryOrientationExact.agda: −0, unoriented 0 and +0 are separate orientation phases projecting to a single neutral scalar.
- DASHI/Cognition/PNF/OrientedZeroFutureQuotientExact.agda: signed zeros with identical current observations but distinct future values; an exact source non-factorability witness.
- DASHI/Cognition/PhaseEnrichedTrit.agda: neutral dominance, balanced opposition and phase-bearing ties can share observed zero without the same hidden state.

Do not merge: scalar additive identity, zero-frequency Fourier character (DC), zero vector amplitude, punctured absent origin, centre residual, unobserved evidence, unknown truth, explicit false, withheld judgment, conflicting evidence, router tie, padding and missing spaCy attribute. Each has a different constructor/evidence authority. Lack of a parser label is not a grammatical zero and unknown epistemic status is not the negative trit.

**Exact proposed Z lemmas** (source owner first; original same-neural-object instances OPEN):
Z1 originalBinarySupportSignRoundtripReused;
Z2 supportOnlyQuotientErasesSignedFutureWitness;
Z3 signedZeroWaveTransitionNonDescentToScalar;
Z4 phaseEnrichedZeroCannotPromoteUnknownEvidence;
Z5 spaCyMissingFeatureDistinctFromNeutralTrinary;
Z6 puncturedSpatialCentreDistinctFromDCFourierMode;
Z7 selectedSourceLeechC6VersusS3ActionDiscriminator;
Z8 sourceExpertHistorySignChartConjugationWeld.

### P — Punctured nine, twenty-seven, fifty-three; pants and wave

Source Docs/LeechLILAPrimePuncturedNineJWaveMaxCut20261101.md already defines 384 = 16×3×(3²−1), the eight-site punctured-nine carrier, 9-site completion, 4 conjugate Fourier pairs, and essential missing-centre residual. The additive group is C3×C3, **not C9**; translation moves the puncture, so original eight-site action requires centre re-gauging. Do not equate eight nonzero spatial points with eight nonconstant dual characters.

Source docs/punctured27_nine_pants_xor_crosspollination_20261026.md has punctured T³ without origin, **26=8+9+9**, and its antipodal **13** unoriented point directions in support orbits 3+6+4. It is not 3×8. ReducedFiftyThreeFibreExact has the independent 54 = 1 + 53 constant-plus-reduced decomposition. An additional oriented count-compatible chart is **53 = one seam + two copies of the punctured 27 (1+2×26)**. This is not yet a geometric isomorphism with the selected 6×9 Laplacian, or a proven pants gluing.

**Exact proposed P lemmas:**
P1 punctured27CentralEightOuterNineNineBidi — constructive converse to 8+9+9;
P2 punctured27AntipodalThirteenOrbitsExact — same puncture and involution;
P3 punctured53TwoCopiesPlusSeamBidi — explicit source index maps;
P4 originalReduced53LaplacianToPunctured53SameGeometry — actual matrix and invariant form, not cardinality;
P5 originalPuncturedNineFourierZeroCentreResidualBidi — invertible wave/source lift and centre gauge;
P6 originalPantsEdgeStalkAdmissibleMatch — compatible incidence, orientation and provenance on every gluing boundary;
P7 wavePantsGluingTemporalRefinementCommutationOrResidual — do not assume time/refinement squares commute without consumer proof.

### M — Constructive 196884 C3/S3 carrier, then actual Monster gate

New SOURCE scripts in this SAME Agda PR:
- scripts/check_monster196884_native_c3_d4_intertwiner.py. On the existing PointedTernaryBulkExact one-unmarked-or-nine-marked × 3^9 sheet, increment the selected marker's trit (or unmarked D4-fixed centre). Explicit inverse to an orbit/phase address: **65,610 free C3 three-cycles**. Exhaustive local integer verification over all **196,830 fine states** includes r³=id, zero fine fixed points, inverse/reopen, D4 rotation and reflection transporting the sheet and marker jointly. Add **54 declared C3-fixed coarse states**, producing χ(e)=196884 and χ(r)=χ(r²)=54.
- scripts/check_monster196884_s3_punctured27_fibre.py. Reflect only the SELECTED trit (not the nine-trit global sign), and exchange the oriented copies of the coarse punctured-27 chart, fixing invariant/seam. Exhaustively checked 196884 states for s²=id, srs=r⁻¹, D4 commuting with s and r; χ(reflection)=65612. Explicit S3 irreducible multiplicities: **trivial 65638, sign 26, standard2D 65610**. They sum as 65638+26+2×65610=196884.
- Both source checks are **local finite integer evidence**, not kernel-accepted Agda proof or an FLM identification. The action is a concrete source-marked-sheet group action, not just dimension arithmetic. The coarse 53 identification is a chosen carrier, not a native reduced-Laplacian isometry.

**Exact proposed M lemmas and missing inputs:**
M1 nativeMarkedSheetC3ActionOrderThreeAgda;
M2 nativeMarkedSiteD4CommutationAgda;
M3 nativeFineToRegularC3OrbitPhaseBidiAgda;
M4 nativePairedPunctured27S3CoarseActionAgda;
M5 nativeSelectedS3ActionCharacterAndFormExact;
M6 originalReduced53ToSelectedCoarse53Intertwiner (must provide matrix/geometry);
M7 publishedFLM3BOriginalWeightTwoAction (select actual FLM generator, normalized basis and action);
M8 originalFineCoarseToPublishedFLM3BIntertwiner (actual invertible linear map satisfying Φρ_native(g)=ρ_FLM(g)Φ);
M9 originalGriessProductInvariantFormTransport (actual Griess product, form and conformal unit, not just character);
M10 originalAllMonsterGeneratorsRelatorsAndVOAModes (selected FLM/VOA, beyond restricted subgroup).

Character equality ensures abstract C3 representation equivalence over suitable characteristic-zero fields, but does NOT supply the original-basis M8/M9 maps or full Monster action. Existing Monster PR #1472 owns the selected Griess/FLM/VOA construction; do not invent another implementation of its original source.

### K — What determines each k; exact dimension continuation

The **n=9** coincidence is driven by a declared model, not by tetration: 9 ternary sites, 1+9 marker choices, and a 6×9 coarse sector. If this RULE persists for n sites, then

D(n)=(n+1)3^n+6n; q(n)=(n+1)3^(n−1) free C3 blocks; C3 trace=6n.

A compatible chosen S3 extension has multiplicities **trivial=q+3n+1; sign=3n−1; standard=q**, and **coarse 6n=1+[1+2(3n−1)]**. When n=3^d, 3n−1 is the puncture of a (d+1)-dimensional ternary cube; at n=9 it is 27−1=26. This is one structurally justified extension, NOT a unique next Moonshine coefficient.

Exact checked script scripts/check_monster196884_hyperfabric_k_growth.py:
n=9 => D=196884, q=65610, trace=54;
n=10 => D=649599, q=216513, trace=60;
n=11 => D=2125830, q=708588, trace=66;
n=12 => D=6908805, q=2302911, trace=72;
n=18 => D=7360989399, q=2453663097, trace=108;
n=27 => D=213516729579798, q=71172243193212, trace=162.

Distinguish TWO other prior formal recursions:
- Tensor depth k gives dimension 196884^k and C3 trace 54^k, with irreducible multiplicities [(d+2t)/3,(d−t)/3,(d−t)/3]; this is not the marked-sheet n extension.
- Actual self-indexing in SelfIndexingHyperfabricTetrationExact: A0=1; A_(k+1)=9^A_k because each entire prior carrier indexes a 9-valued field. A1=9; A2=387420489; A3=9^(387420489) has 369693100 digits. A chosen D(A2) has around 184846559 digits. The recurrence follows from **function-space indexing**, not from the special number 196884.

Keep time/event index t, refinement depth k, observer a and optimiser step s separate: W[t,k,a;s]. Source update and projection commute only with a proven chosen-consumer factorization; otherwise carry residual. Reuse existing wave/inverse-limit, time-fibre, MDL/codec, and exact gluing owners.

**Exact proposed K lemmas:** K1 markedSheetGeneralSiteCount; K2 markedC3FreeOrbitCountGeneralN; K3 selectedS3IrrepMultiplicityGeneralN; K4 punctured3NCoarseSeamChartWhenPowerOfThree; K5 functionSpaceSelfIndexingNotTensorRecurrence; K6 temporalRefinementConsumerNonDescentOrResidual.

### L — SensibLaw/SLR spaCy and early-epoch TinyStories learner

SensibLaw src/storage/postgres/spacy_numeric_projection.py already persists source-bound numeric spaCy token offsets, POS, lemma, morphology, dependency heads, named-entity spans and parser execution IDs. Reuse this producer and original Leech SentencePiece tokens with exact character-span overlap and Unicode normalization; do not add another parser owner in Leech.

**Early supervised target:** from input token sequence, predict sparse/multi-hot spaCy POS, morphology, dependency labels and head links. One-hot categorical class indices can be represented by an embedding lookup; unknown/absent capability is a masked target, never the zero class. Compare baseline token-only predictions, prepopulated syntax side input and zero-initialised gated SLR features. Report POS/morph macro/micro F1, dependency UAS/LAS, prediction CE, time-to-quality and memory/energy costs, with a parser-shuffled negative control. Google's SyntaxNet / Parsey McParseface is a genuine dedicated neural POS+dependency parser (2016); Gemma 3 270M is a much later generic small LM, not a POS-only network. No Google-trained result has been replicated locally.

Two **legitimate distinct** visibility contracts: FULL-CONTEXT completed story for infilling/diffusion and PNF hypothesis revision; PREFIX-CAUSAL partial story for autoregressive next-token prediction. Full-story parsed labels are allowed for full-context tasks; for prefix generation they are either unavailable or teacher-only supervision, never an unqualified inference-time input. Train rich-parser teacher then distil a prefix-available structure predictor. Distinguish parser candidate authority from actual observed narrator-world facts.

**Exact proposed L lemmas:** L1 originalTinyStoriesSLRDocumentRevisionReceipt; L2 originalSentencePieceSpacySourceSpanTransport; L3 categoricalSpacyMissingnessNotNeutral; L4 parserCandidatePNFAdmissionAuthority; L5 prefixVsFullContextVisibilityBidi; L6 originalSpacyOneHotMultiHotTargetWeld; L7 observerEventTimeVsObservationTime; L8 falseBeliefSurvivesConsumerRelevantQuotient; L9 LeechZeroGatePreservesSourceLogits; L10 maskedDiffusionPNFRevisionEvidenceBound; L11 KVExpertWorldTimeHistoryReplay.

### G — Grokking continuation, not premature stopping

Existing owners: DASHIg mod-97 reproductions; GrokkingInvariantSubspaceSelectionExact; GrokkingMeasureStrataExact; GrokkingGeometricCrystallisationMemoryRoutingExact; PNF Marchenko–Pastur null classification and consumer non-promotion; MDL/fibre routing source. The 64-sequence one-epoch TinyStories student and 24-step F4 C3 screen do not settle delayed symmetry selection.

**Every optimiser step:** log cheap scalars only (train CE by head, grad/update norms, router balance/entropy, signed-history energy, numerical status, data cursor). **Geometric checkpoints** at steps 128,256,512,1024,2048,... up to a precommitted compute budget save *full* model+AdamW+scheduler+RNG+data identity and selectively measure heldout CE, task-action defect, actual C2/C3 representation and S3 control, Gram spectra, MP nulls, effective rank, causal interventions, MDL rate/distortion, parsed-world counterfactual QA. Dense extra sampling near a phase transition should be triggered by a predeclared criterion, not only after a pretty result. Full SVD every optimiser step is unnecessary. If task-character composition improves while heldout score stalls and training remains stable, continue through a registered longer horizon; proven semantic nonfactorability, malformed source parity or unstable gradients require correction.

**Exact proposed G lemmas:** G1 sameSourceOptimizerRNGScheduleReplay; G2 originalModelSignedHistoryC2C3OrS3ActionEvidence; G3 heldoutGrokkingTaskCharacterHomomorphism; G4 perStepLatentMechanismMassNotTrainingFit; G5 timeIndexedActivationMPNullAndNoiseCalibration; G6 spectralCleanupPreservesEpistemicFutureConsumers; G7 measuredMDLCodecQualityPareto; G8 longerHorizonTinyStoriesWorldParserMinimalPairGeneralization.

### Releases and acceptance

R0: exact-head Agda polynomial kernel with corrected ℤ literals, original 8/8 torus retained; execute the **three** new Python exact finite C3/S3/growth scripts on that checkout and publish outputs as finite-source receipts.

R1: original TinyStories file+revision, SLR parser numeric source receipts, exact span alignment, early-epoch token→one-hot grammar head with matched baseline and explicit completed-text/prefix evaluation modes.

R2: matched longer mod-97/TinyStories runs for dense/C2/C3/structured-side-input controls; every-step low-cost logs, log-spaced full snapshots; mechanism and semantic diagnostic Pareto fronts.

R3: source-bound PNF/world observer-knowledge, false-belief and masked diffusion revision, cache/state replay and actual gluing/refinement, with negative controls.

R4: published Monster 3B original action, explicit basis Φ, Griess product/VOA and original-neural-consumer transport; no automatic promotion of R0 candidate finite actions.


### Review ownership correction 15 November

This continuation is carried on current-master-derived branch `chatgpt/x369-pnf-world-rollup-20261115`; historical #1442 was merged/closed, and newer source commits on its obsolete feature branch did not automatically become part of an active review. Status is SOURCE WRITTEN for Agda six-variable proof, local finite Python tests for C3/S3 arithmetic, and OPEN for original FLM 3B/Griess and neural source physical weld.