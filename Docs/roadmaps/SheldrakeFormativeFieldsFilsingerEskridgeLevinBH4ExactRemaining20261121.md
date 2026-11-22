# Formative fields × source work × Filsinger/Eskridge × Levin/BH4 — exact remaining phase roadmap

**21 November 2026 | PR #1537 | base `master` | stage: source-written, Agda kernel pending.**

This is the **phase/deliverable/remaining-lemma ledger committed with the implementation**, not a description of future work that has already been done. The primary *endpoint-first* scientific chain is **field topology/attractor and control leverage → (a) Filsinger ambient source access and receiver coupling, (b) antigravity/Eskridge static force versus independent gravitational response, and (c) Levin target-form selection**, with BH4 as a biology-specific physical-state instantiation. **Energy, momentum, source identity and causal history are mandatory consistency/promotion tests, not replacements for modeling controllability or accessible reservoirs.** A hypothetical Sheldrake nonlocal mechanism is an *extra rival* rather than a premise. SLR/ITIR are secondary evidence adapters and cannot promote a physical claim. Retain original author/first-implementation credit per `Docs/SourceAttributionPolicy.md`.




## P0 J0–J9 — nonlinear S1/S3 BIDI coupled coil → diode OR → reservoir → spark + explicit donor (22 Nov 2026)

**User's execution instruction: keep THIS exact roadmap committed and current on PR #1537.** Latest local implementation consumes I0–I7 steelman and original source-typed owners; no new video is available or demanded. Filsinger original speech supports capacitor-across-selected-coil, NST midpoint/Earth return, four positive diodes in two narrated groups and spark dump; Smith/Kelly/Darrer historical account independently supplies magnetically coupled tuned L1/L2. The same physical winding identity, original diode pins and actual environmentally sourced power are still OPEN (FM original 0/4 verified physical edges; original empirical archive 0/24). Retain S1 and S3 as **distinct model worlds**, not certified Filsinger netlists.

**Big-bite implementation:** local executable \`/mnt/data/check_smith_filsinger_switched_s1_s3_bidi_20261122.py\` (SHA1 \`5ba414f9fd8bc49d138a148ecdb62e336c905776\`) contains BOTH models, coupled primary/secondary inductance, positive-only rectifier groups with finite forward drop and resistance, nonlinear finite charging of a bank capacitor, bleed, hysteretic spark on/off transitions, an optional independently powered environmental-current port and full signed integrated source/work/storage channels. Under linear passive magnetic coupling require \`M²<L1 L2\`. **64/64** combined exact symbolic SymPy 1.14 conservation checks + numerical event-driven SciPy 1.17 work-window tests **PASS**, maximum absolute work residual \`3.610667320685934e-12\` in **dimensionless synthetic units**. Executed source is **LOCAL ONLY**, not a committed executable and not GitHub CI. All original human/Smith/NST numerical readings and acoustic 7.8kHz are kept separate.

**S1 hard midpoint:** secondary capacitor C across outer winding with an ideal TRUE centre reference M, effective outer voltages ±v/2, four narrated diode packages represented by two positive OR groups. For bank voltage b and diode drop Vd/resistance Rd, conducting group total current is \`j=max((|v|/2-b-Vd)/Rd,0)\`; its backaction on full-tank voltage is \`sign(v)*j/2\` and the bank evolves \`Cb db/dt=j-(Gbleed+Gspark*on)*b\`. This uses an *ideal equal-centre voltage* as a model parameter, not a real source readback.

**S3 independent tuned coil:** secondary U-V is magnetically driven, C is **across U-V**, and TWO explicit source-to-reference capacitances Cu:U→M and Cv:V→M produce an AC/displacement current return. This is NOT the same topology as hard S1; keeping *both* node potentials is necessary. The capacitance matrix \`A=[[C+Cu,-C],[-C,C+Cv]]\` obeys \`A*[du,dv]=[-i2-ju+Ienv,i2-jv]\`; two diode groups \`ju=max((u-b-Vd)/Rd,0)\`, \`jv=max((v-b-Vd)/Rd,0)\`; \`Cb db/dt=ju+jv-(Gbleed+Gspark*on)*b\`. The capacitance matrix is positive for Cu,Cv,C>0; when Cu=Cv=0 the external common mode is singular, so no silent virtual return is granted. This is a more physically explicit reference mechanism than the earlier constant-alpha proxy.

**Exact energy identity** shared by both models (work over same time interval, signed driver and donor):
\[
W_{\mathrm{driver}}+W_{\mathrm{env}}+E_0
=W_{R1}+W_{R2}+W_{\mathrm{diodes}}+W_{\mathrm{bleed}}
+W_{\mathrm{spark}}+E_1.
\]
Magnetic stored energy is \`0.5 L1 i1²+M i1 i2+0.5 L2 i2²\`; S1 electric energy \`0.5 C v²+0.5 Cb b²\`; S3 electric energy \`0.5 C(u−v)²+0.5 Cu u²+0.5 Cv v²+0.5 Cb b²\`. Diode losses \`Vd*sum(j)+Rd*sum(jk²)\` are explicitly paid. Spark useful work is \`∫Gspark*b²dt\` over its **on** windows. Driver \`∫Vs i1 dt\`; environment \`∫vU Ienv dt\`. No leakage/field-power double count and no hidden 'Earth means source' term. The optional donor is an EXPLICIT synthetic active current \`Ienv=0.005*vU\`, a separately powered negative-conductance-like input, NOT evidence of available Earth/atmosphere energy.

**Numerical outcome** for deliberately dimensionless L1=2,L2=1.5,M=.6,R1=.35,R2=.28,C=1,Cb=.65,Cu=.4,Cv=.55,Rd=.12,Vd=.1,Gbleed=.018,Gspark=1.1,Von=.22,Voff=.075,driver \`Vs=2sin t\` and window 12 periods (T=2π):

| Model and source world | Wdriver | Wenv | Wspark | Efinal | Spark on/off transitions |
| --- | ---: | ---: | ---: | ---: | ---: |
| **S1 drive only** | 34.509814 | 0 | 3.359725 | 1.407380 | 45 |
| **S1 drive + explicit donor** | 34.605648 | +0.157415 | 3.421246 | 1.413187 | 45 |
| **S3 drive only** | 31.911332 | 0 | 0.036029 | 1.451629 | 2 |
| **S3 drive + explicit donor** | 31.912929 | +0.086567 | **0.035537** | **1.493798** | 2 |
| **S1 or S3 precharged bank only** | 0 | 0 | 0.257213 | ~0.000030 | 1 |
| **S1 or S3 zero-state zero-source** | 0 | 0 | 0 | 0 | 0 |

For precharged case E0=0.26325. These numbers are **not SI watts, not hardware measurements, not cross-reel values** and do not establish a natural donor. Especially important: **positive Wenv does NOT logically guarantee positive ΔWspark**. In S3 the prescribed donor raises remaining stored energy while the nonlinear spark work falls, proving that peak-output or spark-only response is not a valid environmental-work identifier. Donor also shifts the *driver's* work through backaction. Always use full signed source + storage reset plus load, loss, and measured natural port before interpreting effects.

**Reused proof owners, no reinvention:** \`DASHI/Physics/Motors/SmithFilsingerSwitchedCoupledStorageBidiExact.agda\` imports \`SmithFilsingerTimeIndexedTransferExact\` for \`BoundedWorkWindow\` and its preexisting \`usefulNoGreaterThanAllSources\` theorem; \`SmithFilsingerSourceEdgeAdmissionBidiExact\` and \`Circuit36927ComponentGraphExact\` preserve original/source pin constraints; \`SameObjectConservationLedgerExact\` preserves unresolved channels; the \`OriginalMaxwellMeterIntervalWeldExact\` remains the future SAME physical-source meter certificate owner. The new Agda source defines S1 and S3 as two conditional circuits, proves identical four-phrase speech is not an injective circuit observation, and packages switched finite work + optional donor choice. **Agda source written and imported into focused root, but Agda kernel NOT run**. It does **not** falsely purport to prove the nonlinear ODE in Agda; the continuous symbolic algebra and numerical event simulation belong to the local Python executable. Full results and original source boundaries in \`Artifacts/smith-filsinger/switched_s1_s3_coupled_storage_bidi_20261122.json\`.

| Gate | Closed mathematically this round | Next real mathematical/physical obligation |
| --- | --- | --- |
| **J0 scenario BIDI** | S1 physical midpoint vs S3 independent tuned cap-return model compared under one source/driver family | Same physical-component equivalence NOT source verified |
| **J1 coupled source** | Symmetric L matrix, positive energy condition and reflected primary backaction in time ODE | Real core and measured source-dependent mutual coupling unknown |
| **J2 diode/spark** | Full-wave ideal centre-OR vs floating two-anode positive OR, bank and hysteretic spark events explicit | Real diode direction/count individual sharing, spark stochastic plasma unmodelled |
| **J3 capacitive return** | Cu/Cv explicit original-hypothesis capacitance matrix; common-mode charge retained | Original Earth geometry, Maxwell displacement and return admittance unknown |
| **J4 source work** | Exact differential work equalities, eight integrated interval ledgers, passive heat and bank closure | Full original measured port and time provenance absent |
| **J5 transient** | Source-off charged bank emits finite pulse, source-off empty bank remains inert | Actual bank state/precharge and full repeated-cycle reset unknown |
| **J6 environment** | Positive synthetic donor admitted and separately paid; S3 useful output can decline despite donor work | Independent Earth/atmosphere/chemical/RF active source must be **measured** |
| **J7 local acceptance** | 64/64 SymPy/SciPy PASS; max residual 3.61e-12, local file source hash recorded | No committed full local Python script/byte identity, no Agda kernel |
| **J8 formal reuse** | New Agda source-typed finite S1/S3 conditional carrier and reused time-window bound, root import | Agda kernel and true physical nonlinear ODE proof not yet obtained |
| **J9 next priority** | BIDI identifies driver-work backaction + reservoir reset as decisive metrics | Next: source-conditional diode/gap constitutive uncertainty intervals and true restored-cycle port efficiency; don't request unavailable footage again |

**Roadmap policy:** continue the logical steelman BIDI with source-indexed assumptions, local SymPy (not GitHub CI), and commit roadmap updates in this same PR with each meaningful result. The absence of original Filsinger footage is not a blocker. Do not export simulated voltages or watts as observed source claims. Avoid exposed high-voltage construction or probing.

---

## P0 I0–I7 — steelman BIDI reverse solve without unavailable Filsinger footage (22 Nov 2026)

**User constraint accepted:** no new Filsinger original pin footage is available. **Do not block all scientific progress asking for the same missing item.** Reopen source notes and exploit the original spoken transcript plus Smith/Kelly writings as distinct original/source strata, then perform **logical forward/backward conditional inference** without promoting one guessed netlist to observed hardware. Prior G/H original hardware gates remain OPEN (FM source-index: four narrated, zero verified physical links; original 0/24 physical evidence roles); retain transient charge theorem and original phase/displacement alternatives.

**New strongest source-and-geometry ranking:** [full machine BIDI ledger](../../Artifacts/smith-filsinger/smith_filsinger_coupled_loop_ranked_steelman_20261122.json) and [human research exposition](../research/SmithFilsingerCoupledLoopRankedSteelman20261122.md) distinguish four ranked *conditional completions*:
1. **S1 centre-referenced tuned secondary, cap across chosen winding, positive diode OR from opposite U/V ends, load returns M.** Best literal minimal extra-edge interpretation of two diode groups, combined positives, “half big coil”, “midpoint”, and a resonance-tuned coil. DOES NOT assert actual Filsinger original pin continuity or whether the tuning belongs to NST itself.
2. **S2 single NST half-winding with effectively half-wave positive collection.** Physically compatible, but duplication/group endpoints require explanation; DC bank smoothing can mask half-wave.
3. **S3 separately magnetically driven L2 with a true conductive or capacitive/displacement M return.** Best explanation of “one coil” affecting “other coil” via source-driven reflected impedance, but requires genuine return/coupling edges the words do not identify.
4. **S4 finite-source conventional full bridge with N hard-bonded to M.** Retain only with paid clamp-current source cost and differing diode direction; weakest literal match for “all forward” positive ganging.
This is **ordinal assumption minimization**, NOT sourced statistical probability, authentic pin map, or empirical performance ranking. Kelly 17+17 split L2 / 47 nF optional across historical L2 are HISTORICAL SMITH COMPILATION only; they do not assign Filsinger coil identity.

**Important coupled EM/LC correction:** A capacitor *across* a selected coil is a **parallel terminal** element to an externally impressed two-terminal voltage, but in a **magnetically excited closed secondary coil-capacitor circulation loop** the induced EMF sees `Z2=R2+R_L+i(ωL2−1/(ωC))`. Two excitation ports, so prior 'series vs parallel' need not be contradictory: an external terminal antiresonance and internally source-driven loop resonance can coexist. With primary `Z1=R1+iωL1`, mutual M, equations `Vs=Z1 I1+iω M I2`, `0=iω M I1+Z2 I2` give `I2=−iω M I1/Z2`, `Zin=Z1+ω²M²/Z2`; passivity requires `M²≤L1L2`. At tuned electrical `ω0=1/√(L2 C)`, `I2=−iω0 M I1/(R2+R_L)` and **positive reflected source resistance** `ω0²M²/(R2+R_L)`. A sign reversal of winding polarity M changes phase of I2 but not real power; this is a physically consistent interpretation of a narrated “pole shift”, NOT evidence it happened. Full RMS phasor ledger `Re(Vs conj(I1))=R1|I1|²+(R2+R_L)|I2|²` exactly, no donor work from capacitor or phase.

**Back-solved fixed-voltage driver extraction:** In the additionally explicitly **primary-reactance-compensated**, linear series-equivalent extractor model, `K=(ωM)²` and `Pout=K Vs² R_L/[R1(R2+R_L)+K]²`. Therefore optimum `R_L*=R2+K/R1`; the tempting `R_L=R2` optimum is valid for **fixed primary current**, not fixed finite-voltage drive. `Pmax=K Vs²/[4R1(R1R2+K)]≤Vs²/(4R1)`. The series-equivalent `R_L` describes internal extracted loss, NOT a source-identical Filsinger rectifier/spark actual connection. No original switching electrical frequency is established by ~7.8 kHz audio.

**Local SymPy 1.14** executed exact **39/39 PASS**, `/mnt/data/check_smith_filsinger_coupled_coil_bidi.py`, local Git-compatible blob `a1de794883b0f1b1b34dee403f9c4feaa46c974b`, **not a committed or kernel-verified program**. Includes sign polarity, KVL, magnetic passivity bound, reflected source-load work, source-aware optimum and synthetic energy ledger. Illustrative normalized R1=2,R2=3,K=4,Vs=1 has R_L*=5, Pout=1/20, Pin=2/5, primary heat 8/25, secondary heat 3/100, 1/8 useful fraction; NOT Filsinger numbers.

| Gate | Exact conditional progress | Residual |
| --- | --- | --- |
| **I0 source steelman** | Smith/Kelly original compiled coupled L1-L2 and Filsinger midpoint phrase kept separate and reconciled into candidate family | Actual same-machine correspondence unproven |
| **I1 circuit ranking** | S1–S4 ordinal source fit and extra wiring assumption ledger | Not a statistical posterior or observed original pins |
| **I2 drive/tuned coil** | Induced-EMF closed secondary loop and external parallel port distinguished | Magnetic coupling/core/drive geometry unmeasured |
| **I3 pole phase** | Exact sign M controls I2 phase, reflected source resistance stays paid | Physical original phase polarity not observed |
| **I4 source funding** | Mutual + reactive terms conserve real work, explicitly signed RMS ledger | Environment donor positive work not measured |
| **I5 load inverse** | Fixed-voltage RL*=R2+K/R1 vs fixed-primary-current RL*=R2 | Nonlinear original diodes/spark/storage need their own model |
| **I6 local/Agda** | 39/39 local SymPy, original source-typed owners reused | Agda kernel and original physical coil pin gate open |
| **I7 next iteration** | Logical steelman proceeds in absence of footage | Compose selected candidate with existing nonlinear discharge + finite charge-energy source model; don't duplicate proven owners |

**Operational direction:** prioritize **big-bite BIDI weld** of S1 and S3 into existing diode/spark/capacitor-bank and source-energy contracts, checking both driver-backaction and separate Earth-donor counterworlds. Never request new original footage as a prerequisite; treat its absence as a scoped epistemic boundary, not mathematical research blocker. No exposed high-voltage build or probing instructions.

---

## H0–H5: original-source PIN ADMISSION audit — four narrated edges, zero verified physical links (22 Nov 2026)

**Source, not guessed diagram.** Reopened the exact existing \`Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json\`. Its midpoint/spark \`FM\` original-source owner has precisely **four** partial narrated graph relations: (1) transformer-secondary / accessible midpoint; (2) selected coil / capacitor described across it; (3) ganged rectifier positive branches; (4) rectified return / midpoint *or* Earth. **Each is explicitly marked \`proven_continuity:false\`**. No exact original reel frame or physical pin-to-node photograph was authenticated in this turn; public reel lookup did not supply one. Thus **0/4 FM pin-continuity proofs**, notwithstanding the literal speaker's meaningful words and values. The earlier original raw evidence archive remains **0/24** supplied roles. Original source transcription and mathematical circuit-completion are not physical verification.

**Positive result:** the words permit the same FM speech signature in at least THREE mutually different electrical winding owners (full NST A–B, half NST A–M, separate U–V), provided each unobserved wire identification is modelled as an **explicit conditional hypothesis**. The existing E0 ideal rectifier waveform and F0 capacitor-return models therefore cannot uniquely reconstruct the original diode and load nets. This result cannot be fixed by equating “earth”, “negative”, “middle”, “cap”, and “coil” merely because the speaker uses them in adjacent sentences. The Kelly/Darrer 17+17-turn compiled source and other Filsinger ZVS/Earth reels remain independently indexed.

**Reconcile latest transient-charge correction:** The companion \`G0–G6\` *transient* gate already on this branch takes precedence over any stronger instantaneous stationary no-return language. For an isolated island with four nonnegative outward diode currents and no inbound return, the general law is \`dQ_island/dt+Σi_D=0\`. Finite initial net charge can fund a **transient output pulse**; zero sustained cycle-integrated output follows only when the island's charge is restored at cycle end and there is no incoming return. Our new \`H\` gates address **source original pin evidence**, not that charge conservation theorem. A checked idealized no-return cut remains conditional on stationary/restored charge, and the output-energy ledger still has to include capacitance and spark discharge.

**New exact machine source audit:** \`Artifacts/smith-filsinger/fm_original_pin_admission_20261122.json\` reproduces the *actual four* original FM source-index edges without upgrading them, and lists six physical admission targets; canonical source index has a pointer to the new ledger. \`DASHI/Physics/Motors/SmithFilsingerSourceEdgeAdmissionBidiExact.agda\` is a new finite original-owner module preserving \`NarratedEdge\` and the current \`sourceNarratedNoPinProof\` evidence tier, proving a no-unique-winding inverse for the same speech signature, and naming the actual original 36927 component pins that require same-reel identity before any claim can promote. The new module is imported by \`EverythingSheldrakeFieldLevinFilsinger20261121.agda\`. **Source-written, kernel not checked; an Agda constructor reflecting audited text is NOT physical continuity.**

**Local independent exact audit:** \`/mnt/data/check_filsinger_source_edge_admission_20261122.py\` ran **45/45 PASS** under SymPy 1.14.0, local Git-compatible blob \`be0b14a26fe16cdab32d88b0787d9d1f819440f3\`. It checks the original 4 unverified speech edges, 14 original physical pin labels, three competing CONDITIONAL node quotients, outward-only stationary source cut, and capacitor-divider unloaded-centre ambiguity. This local test file was **not** committed to GitHub, so no GitHub-byte parity is claimed. The separate concurrent updated transient-charge exact regression **28/28 PASS** is preserved as its own source/test owner. Neither proof constitutes original filmed wiring or real power.

| Pin-evidence gate | Exact original evidence needed | Status |
| --- | --- | --- |
| **H0 NST midpoint** | Original time/frame and a physical transformer-secondary midpoint terminal | OPEN |
| **H1 tuned coil identity** | Whether selected capacitor spans NST A–B, NST A–M or independently tuned L U–V | OPEN |
| **H2 capacitor pins** | Individually mapped C1/C2 to selected U/V, beyond the spoken “across” | OPEN |
| **H3 diode ends** | All four physical anodes and cathodes; verification of ganged collector P | OPEN |
| **H4 load return** | P→load/spark/bank→N and physical N–M–Earth connection or intervening impedance | OPEN |
| **H5 same-original real work** | Signed drive/environment/load/loss and initial/final stored energy, source and time matched | OPEN |

**Next source-specific operation:** inspect an *actual original reel frame or native source diagram* with visible capacitor/coil and diode lead endpoints and attach each edge with frame coordinates. Preserve unresolved pins as unknown. Do not commission a synthetic “original diagram” or repeat more abstract RLC simulations while H0–H4 remain open. No exposed high-voltage testing or construction steps.

---

## G0–G6: transient-charge correction to F0 stationary no-return cut (22 November 2026)

The recorded Filsinger midpoint narration includes a capacitor across the selected coil, four forward-facing diodes, an NST/Earth midpoint return, and a spark-gap dump. Therefore a precharged **transient** must not be excluded by a **stationary** no-return theorem. Reopened the source-indexed Agda and exact previous SymPy owners before changing their scope.

For net source-island charge Q and nonnegative diode currents outward from an island through the four package edges, the general law is

\[
\frac{dQ}{dt}+\sum_{k=1}^4 i_{D_k}=i_{\mathrm{return}}.
\]

If there is no return path, then the time-integrated emitted charge is Q(t0)-Q(t1). A finite positive diode pulse can occur while net source-island charge falls; one cannot demand instantaneous diode currents zero without also assuming dQ/dt=0. Over a restored cycle Q(t1)=Q(t0) with zero incoming return and nonnegative diode currents, total emitted diode charge is zero (and currents vanish almost everywhere). Thus F0's stationary no-go survives with its stated premise, but is NOT a ban on an initially charged floating structure's transient.

Source-charge is NOT the same as internal differential U/V LC energy. As an illustrative separate exterior-reference capacitor C discharges through R, v=V0 exp(-t/(RC)), dU/dt=-v²/R, and output work over [0,T] is 0.5*C*V0²*(1-exp(-2*T/(RC))). The capacitor funds a finite pulse, not repeated output without restoration/replenishment. A positive load-voltage bound additionally constrains work to Vmax times transferred charge; no numeric original energy receipt follows from the narrator's rated capacitor examples.

**Formal/code correction:** Existing F0 Agda source now explicitly scopes the old Nat zero-sum KCL proof to stationary/restored-charge conditions; it adds an exact finite precharge discharge witness 1=0+1, without claiming that the original machine did so. New source-indexed JSON artifact: Artifacts/smith-filsinger/midpoint_transient_charge_return_bidi_20261122.json. Independently executed local SymPy 1.14 regression: **28/28 PASS** at /mnt/data/check_filsinger_transient_charge_return_sympy_20261122.py, Git hash of executed local source 30de320edaea8ab5539be0c05c42977c50f48b80 (not committed byte-identically). Existing 55/55 and 33/33 receipts cover the previous stationary/phasor model, not this stronger transient qualification. Agda kernel unverified.

| Gate | Exact result | Still unverified original-world evidence |
| --- | --- | --- |
| G0 | Speaker-described spark-gap discharge retained, not excluded | Actual same-reel spark and capacitor wiring |
| G1 | Isolated-source island net charge tracked separately from internal LC energy | Which capacitor actually couples to Earth or M |
| G2 | Nonzero outward pulse can accompany negative charge derivative | Timed real source island return current |
| G3 | Restored net charge + zero return implies no sustained positive-only diode current | Original circuit return path and state reset |
| G4 | Separate RC source gives finite input-stored work and zero ongoing source | Original capacitor state/energy initial and final |
| G5 | Any replenished Earth/atmosphere/chemical/RF donor remains explicitly measured signed work | Real, same-time driver, output, losses, donor data |
| G6 | 28/28 local exact checks; original Agda conditional clarified | Pinned Agda kernel, original physical evidence 0/24 roles |

**Original forward/backward next cut:** identify which coil owns the narrator's capacitor; determine whether M/Earth is a conductor or displacement/reference path; and identify diode cathodes, output reservoir and spark load. The mathematical finite-pulse counterexample does not identify any actual Filsinger pin. No live high-voltage construction or probing is proposed.

---

## P1 source-selected winding ownership × physical midpoint return (F0–F8) — hard Kirchhoff BIDI cut

**22 November 2026, after E0–E8: priority correction.** The earlier user's Filsinger spoken transcript explicitly describes an **NST/stable transformer with accessible midpoint**, an optional capacitor "across the one coil you want", two diodes "off the cap" and two from another wire/coil, all forward-facing and positive ends ganged, a return to "midpoint, earth, ground", "half the potential of the big coil" and a claimed Tesla "pole shift" altering the other coil's current field. The **NST secondary with midpoint and the selected resonant "one coil" are not thereby proved the same electrical winding**. Reopened original repository audit notes: \`SmithFilsingerSourcePortShuntMaxCut20261115.md\`, \`DonSmithHighPowerDevices147PageOriginalPDFMaxCut20261112.md\`, \`SmithFilsingerNonlinearQuadratureMaxCut20261112.md\`, and the E0 machine ledger. Compiled Smith/Kelly/Darrer **17+17-turn L2 / optional 47nF** belong to a different historical figure family, not direct physical pin proof of Filsinger's midpoint reel. The precise source video and the user's original Darrer PDF could not be re-opened this turn; the public alternate Kelly PDF returned an access/rate-limit error. **Do not equate original source-claims, interpreted winding ownership, and a photographed circuit.**

**Source-owned BIDI: TWO independent missing axes**. The tuned capacitor's "across" phrase only means capacitor and its selected coil share terminal nodes **U and V** (conditional on actually being wired in parallel). It does **NOT** identify whether that tuned coil is (1) original NST full A–B secondary, (2) original NST one A–M half secondary, or (3) a *separate resonant L2* that may or may not be galvanically connected to NST midpoint M. Nor does it identify the physical **return path**, which may be (a) direct copper to M, (b) finite capacitive/displacement (or another explicitly modelled) return, or (c) disconnected under an idealized cut. The old E0 full-wave/h​​alf-wave math prescribes \`U-M=±v\` as a CONDITIONAL source case; the source wording alone never supplied this electrical relation.

**F1 hard no-return cut:** Suppose the chosen resonant U/V source is a complete floating electrical island, with internal coil/capacitor/differential excitation but **the only crossing connections are four ideal forward-only diodes** U/V→common positive collector P feeding a load P→M. Assume no conductor, capacitance, leakage, radiative displacement, switch or other return crosses the island boundary and no change in net island charge. Each diode current \`i1,i2,i3,i4≥0\`; summing KCL across the entire island gives \`i1+i2+i3+i4=0\`, hence **all four currents equal zero**. This is a genuine **conditional impossibility of sustained load funding** by the isolated positive-only source island. It does *not* rule out Filsinger's described hardware because a real NST/M/Earth/plate/coupling circuit may supply a return path that the source transcription did not pin-trace. Electromagnetic differential drive internal to U/V does not automatically add a net external charge-return path.

**F2 strongest reverse counterworld: displacement return can imitate a centre tap.** For a separately driven AC differential source \`V_U−V_V=e\` (RMS phasor, angular frequency \`ω\`), model capacitances \`C_U\` from U→M and \`C_V\` from V→M with a *linear proxy* load conductance \`G\` U→M. Let \`s=iω\`. Supernode KCL and source relation are
\[
(G+sC_U)V_U+sC_VV_V=0,\quad V_U-V_V=e .
\]
Exactly,
\[
V_U=\frac{sC_V e}{G+s(C_U+C_V)},\qquad
V_V=-\frac{(G+sC_U)e}{G+s(C_U+C_V)}.
\]
The differential source current is \`I_s=−sC_V V_V=(G+sC_U)V_U\`; exact signed real work \`Re(e conj(I_s))=G|V_U|²\`. The ideal capacitive return contributes **zero average real source power**, but provides a real AC/displacement return needed for the load to draw power from the differential drive. At G=0 the endpoint voltages are \`V_U=e C_V/(C_U+C_V)\` and \`V_V=−e C_U/(C_U+C_V)\`. If \`C_U=C_V\`, they become **+e/2 and −e/2 versus M**, indistinguishable *in those unloaded voltage observations* from a perfect hard centre tap **despite having no galvanic midpoint conductor**. With load G>0 the capacitive return shifts reference and current; but practical hard taps with finite source impedance can also sag, so a load voltage sweep alone does not uniquely certify original physical continuity. The actual original rectifier, charge reservoir, spark-gap, nonlinear source and field response differ from this linear comparator.

**Source exact local checks:** independent \`/mnt/data/check_filsinger_midpoint_return_cut_bidi_sympy_20261122.py\` **55/55 PASS** in local SymPy 1.14.0. Committed and **byte-identical locally rerun** \`scripts/check_filsinger_midpoint_return_focused_20261122.py\`, **33/33 PASS**, Git blob \`e09b23a229c6643c594ecefd6e37b30fec7346b0\`. In normalized \`C_U=C_V=G=ω=e=1\` the model gives exactly \`P_source=P_useful=1/5\`; no independently replenished Earth/atmospheric power is inferred. New source-indexed \`Artifacts/smith-filsinger/midpoint_winding_owner_return_cut_bidi_20261122.json\` records eight source phrases, the 3×3 model axes, original evidence boundaries, no-return KCL and the finite-capacitive source closure.

**Finite typed Agda reuse:** \`DASHI/Physics/Motors/SmithFilsingerWindingOwnerReturnCutBidiExact.agda\` imports **existing** \`Circuit36927ComponentGraphExact\` for the physically selected component pins and \`SmithFilsingerTranscriptDiagramNumbersSourceIndexExact\` for four narrated diode packages. It distinguishes \`CoilOwner\` × \`ReturnClass\`, proves under a supplied nonnegative-Nat diode KCL hypothesis \`fourOutwardDiodesNoWorkWithoutReturn\`, and provides \`noUniqueCentreTapFromUnloadedVoltage\` (two physical reference mechanisms share the same unloaded symmetric voltage signature). Explicit \`OriginalSameRevisionPinReturnCut\` retains original physical source pin, selected coil, capacitor terminals, positive output, same-reel attestation and signed-source work obligations. Focused root imports the module. **Agda source-written only; no local Agda binary/kernel check; no original-device source-to-pin witness inhabited.**

| Gate | Exact conditioned result | Physical source / next discriminator |
| --- | --- | --- |
| **F0 original words** | NST midpoint and "one coil" preserved as separate phrases | Original clip timed transcript / physically observed source-to-coil designation unavailable |
| **F1 selected resonator** | NST full A–B, NST half A–M, distinct resonator U–V explicitly separate | Determine WHICH coil has the across-coil capacitor and whether it actually has the NST midpoint |
| **F2 no-return KCL** | Floating positive-only diode island ⇒ every nonnegative package current zero | Identify any conductive, displacement, switch, Earth or measured return to the actual source island |
| **F3 capacitive mechanism** | Exact two-stray-cap AC loaded source relation and real power funding | Identify source/reference capacitance, leakage, time-/frequency-domain current, true materials |
| **F4 apparent centre tap** | Symmetric capacitive divider reproduces unloaded ±e/2 without hard M tap | Physical conductor continuity, coupled nonlinear same-source load response (not voltage symmetry alone) |
| **F5 diode/rectifier** | Former E0 waveform results require *independently evidenced U,V relative M* | All four original diode anodes/cathodes plus output capacitor/spark/load pins |
| **F6 natural source** | Neither displacement reference, original ground label nor rectifier current proves natural input | Signed same-original driver, Earth/ambient/chemical/RF, output, loss and reset-energy port records |
| **F7 math/formal** | 55/55 independent + 33/33 committed-byte exact SymPy; typed original-pin Agda module | Pinned Agda 2.9 kernel and source-matched physical pin record still missing |
| **F8 historical/evidence** | Kelly/Smith compiled 17+17 L2 and Filsinger NST reel are separate owners | Original filmed pin map; prior raw empirical evidence archive remains **0/24** roles |

**Next true source-hard cut:** trace a single ORIGINAL video frame/diagram line from capacitor terminals to *which* selected coil, and from the diode's joined positive outputs through the real load back to *which* original winding/return. Only those concrete wire facts can decide whether the no-return cut applies, whether a complete copper midpoint path exists, or whether the receiver relies on displacement/coupling. Do not add generic RLC scans to substitute for this missing source identity; no exposed high-voltage construction/probing instructions are proposed.

---

## P1 original midpoint diode landing × coil-span BIDI — exact full/half-wave discriminator (E0–E8)

**22 Nov 2026; source-first logical continuation of D0–D8.** The original user-supplied midpoint transcript says two diode packages off a capacitor and two off another selected wire/coil, forward-facing, positives ganged, centre-tap/Earth/ground return, and a capacitor across the selected coil. Source-reopened: \`Docs/research/SmithFilsingerSourcePortShuntMaxCut20261115.md\`, \`Docs/research/FilsingerDonSmithGoldenRectangleLissajousMaxCut20261111.md\` and the D0 source-index/Agda owner. The source **does not tell us whether the 'selected coil' is an entire A–B centre-tapped winding, a single A–M half winding, or another coil**. This is a distinct missing variable from D0's fact that capacitor C and coil L share **their own** U,V electrical nodes when physically parallel. DO NOT silently set \`U-M=+v,V-M=-v\` merely because C is across a coil, or elevate the 17+17-turn *Smith/Kelly compilation* to verified Filsinger hardware.

**New four conditional inverse cases for zero-drop forward diodes, unsmoothed resistive P-to-M output and sinusoidal source with fixed half-peak x>0:**

| Source quotient + input diode landing | Prescribed U,V relative to M | Ideal P–M output | Physical status |
| --- | --- | --- | --- |
| **E-T2** full winding, two diode packages on each distinct end U/V | U-M=+x sin θ; V-M=−x sin θ | **full wave** x|sin θ| | requires complementary input terminals and a true centre tap |
| **E-T1** full winding but *all four packages* anodes on U (despite cap/coil physical labels) | U-M=x sin θ | **half wave** x max(0,sin θ) | two differently labelled physical component ends can be same electrical input |
| **E-H2** capacitor across only one half winding U=A,V=M, two packages on each end | U-M=x sin θ; V=M | **half wave** x max(0,sin θ) | distinct electrical input nodes but not complementary positive/negative wrt return |
| **E-H1** half winding and all diodes from U | U-M=x sin θ; V=M unused | **half wave** x max(0,sin θ) | same waveform as E-H2 even though package-node assignments differ |

For the **same ideal source peak x**, each has the **same observed peak x**. The full-wave case has mean DC voltage \`2x/π\`, RMS \`x/√2\`, average resistive load work \`x²/(2R)\`; all three half-wave cases have mean \`x/π\`, RMS \`x/2\`, power \`x²/(4R)\`. Thus simple peak output **cannot** distinguish the selected original wiring. In this constrained sine/unfiltered model, positive conduction during both half-cycle polarities forces **both** a full secondary span and opposite electrical diode anode landing; negative-half positive current is the exact finite reverse discriminator. Measured DC or RMS alone with unknown x also lacks unique source map. Ordinary whole-secondary bridge measured between P–N has a **different voltage reference** (ideal peak 2x) and must not be compared to P–M indicators without the original meter probes.

**Original spark/rectified storage caution:** Any capacitor bank on the P–M load, nonlinear spark-gap pulses, shunt, different driver phases, winding coupling and external field backaction can alter those waveforms. Specifically, in a diode-off interval with output reservoir capacitance C_o and load R, \`C_o dv_o/dt=−v_o/R\`, \`v_o(t)=V_0 exp(−t/(R C_o))\`, \`dU_o/dt=−v_o²/R\`: a half-wave rectifier can retain positive DC output through the non-conducting input half-cycle. Neither original physical smoothing network nor actual waveform is verified. The earlier **parallel LC antiresonance** \`Y=G+i(ωC−1/(ωL))\` uses an ideal linear conductance: switched rectifiers/spark outputs can replace G by a nonlinear time-dependent loading operator. Do not apply linear antiresonant voltage peak/current dip to original device without that qualification.

**Package current non-identifiability:** The ideal identical diode groups from U/U,V/V have group incidence \`[[1,1,0,0],[0,0,1,1]]\`, rank 2/nullity 2; one-node four-package grouping \`[[1,1,1,1]]\`, rank 1/nullity 3. Real diode forward drops, lead impedance, thermal conditions and recovery decide parallel package current sharing; visual package count and group output current cannot identify individual diode currents or independently replenished energy-source count.

**New precise source owner** \`DASHI/Physics/Motors/SmithFilsingerDiodeLandingWaveformBidiExact.agda\` reuses \`SmithFilsingerCapCoilParallelNodeQuotientBidiExact\` and the source-indexed four-diode number; defines \`CoilSpan\` × \`InputLanding\` × two half-cycle \`LoadConduction\` and proves exact conditional forward cases plus converse \`negativeHalfConductionForcesFullSpan\` and \`negativeHalfConductionForcesOppositeInputs\`. Imported into the focused \`DASHI/EverythingSheldrakeFieldLevinFilsinger20261121.agda\`. This is **source-written Agda, not kernel-checked**. Companion machine-readable \`Artifacts/smith-filsinger/diode_landing_full_half_winding_bidi_20261122.json\` preserves all hypotheses and source limits.

**Exact local and committed-byte acceptance:** \`scripts/check_filsinger_diode_node_landing_half_full_sympy_20261122.py\` **64/64 PASS** under local SymPy 1.14.0, with Git blob \`099c4c4f9b006ed85affd8e8b002f573250a7dca\` **identical to the executed local** \`/mnt/data/check_filsinger_diode_node_landing_half_full_sympy_20261122.py\`. Checks cover four topology/landing combinations and both half-cycle signs, exact sinusoidal mean and RMS integrals, R-load work, current-group incidence rank, capacitive bank source-off storage budget and two opposite donor hypotheses with identical useful output. These tests do not verify physical Filsinger diode direction or original V/I source.

| Gate | Proved conditional result | Remaining physical original burden |
| --- | --- | --- |
| **E0 source wording** | Two cap/coil-labelled diode groups, forward orientation and midpoint return preserved | Original diode anode/cathode and video-to-word alignment not reverified |
| **E1 selected coil span** | Full A–B and half A–M are **different** BIDI cases even when C across coil | Identify exactly which transformer winding section has capacitor across it |
| **E2 landing quotient** | Four packages may resolve into U/V or U-only anode nodes | Source photographed pin-to-net identity on the selected unit |
| **E3 full/half waveform** | Full sine both signs iff full span AND opposite landing in simplified model | Exact load-return M and actual signed electrical waveform with zero/positive branch intervals |
| **E4 diode package work** | Parallel-diode total-current inverses rank 2 or rank 1, individual sharing unidentifiable | Actual lead/diode drops, current, temperature and switching |
| **E5 output storage** | Diode-off RC reservoir can preserve positive DC output; signed work paid | Identify actual output cap bank, spark path and full-cycle storage reset |
| **E6 natural source** | No waveform, peaks or diode count identify Earth/atmosphere/chemical/RF donor | Original independently measured environment/driver/return signed energy ports |
| **E7 local tests/Agda** | **64/64** byte-identical committed local exact SymPy; finite BIDI owner source-written | Agda 2.9 exact-head kernel check and source physics gate open |
| **E8 attribution/reel** | Smith/Kelly 17+17 separate from Filsinger midpoint reel and three-Earth/ZVS reels | Original source-identity and recorded same-time machine acceptance, **0/24** raw evidence roles |

**Next hard reverse cut:** focus on one selected physical coil, the exact endpoints of its parallel capacitor, the four diode **anode** landing nodes after the U/V quotient, and the true output return **M versus N**. Do not assume full-wave merely because a capacitor is across a coil or because four diodes were named. Reuse original source work owners only after a same-time electrically measured source and output netlist is validated. No exposed high-voltage build guidance.

---

## P1 literal capacitor-across-coil reverse solve — electrical node quotient, parallel LC and source identifiability (D0–D8)

**22 Nov 2026, continuation from C0–C8.** Reopened the actual archived source reports `Docs/research/SmithFilsingerSourcePortVirtualCircuitMaxCut20261112.md` and `Docs/research/FilsingerDonSmithGoldenRectangleLissajousMaxCut20261111.md`, and the literal speech inventory in `Artifacts/smith-filsinger/midpoint_return_clamp_capcoil_bidi_20261122.json`. The speaker describes **two diodes off the cap, two off the other (coil/wire)**, with all forward-facing, positives ganged and a return 'to midpoint, earth, ground'; and says the capacitor is **across the selected coil** and produces a 'pole shift'. The reel association remains provisional; no current original video frame or real pin continuity has been authenticated. **The logical inverse must collapse component terminal labels to ELECTRICAL nodes when an across-coil capacitor is assumed.**

**Original BIDI source-geometry correction:** Under the conditional literal **parallel** C/L wiring, physical terminal equivalence is **C.first=L.first=U** and **C.second=L.second=V**. Four diode packages physically described as two 'off cap' and two 'off coil' can originate from **U and V** (two distinct electrical input nodes), or **all originate from U** (one distinct input node), depending on which cap/coil terminals the packages touch. Physical labels do not entail independent electrical sources or even distinct nodes. Strict all-forward diode cathodes ganged at P support a *positive diode-OR* completion; a conventional bridge would require separately directed N-to-winding return diodes. A centre-tapped U-M=v, V-M=-v conditional source with U/V diode-OR yields **P-M=|v|** in the zero-drop, no-storage idealization, so that output alone cannot distinguish whether the narrating hand pointed to the capacitor terminal or coil terminal on the same net. The negative return M/N still follows the separate C0–C8 finite-clamp versus R/C/LC mediated conditions.

**New finite Agda owner** `DASHI/Physics/Motors/SmithFilsingerCapCoilParallelNodeQuotientBidiExact.agda`: preserves source labels and proves the two cap/coil terminal-node identifications conditional on 'across', `noUniqueComponentTerminalFromObservedNode` (no inverse from electrical node to physical source component label), explicit two-diode-per-component landing cases and `noUniqueLandingCaseFromFourPackages`; reuses the original source number and C0–C8 BIDI owners. Imported into the focused root. **SOURCE-WRITTEN ONLY; Agda kernel absent, NOT verified.**

**The decisive parallel-vs-series electrical correction:** A capacitor physically **across** the coil has **parallel** admittance Y=G+i(ωC−1/(ωL)), rather than the earlier C0–C8 **series**-return impedance Z=Rs+i(ωL−1/(ωC)). These are two physically DIFFERENT candidate graphs, not equivalent descriptions of the speaker's 'across' statement. At ω₀=1/√(LC), the capacitor and coil have **equal/opposite reactive currents**, and the total terminal admittance equals G. With ideal G=0, the parallel branch presents **zero terminal admittance / formally infinite impedance**, not the near-zero impedance of a series LC. This is parallel **antiresonance** and may change phase or produce stored/reactive branch current, but is not evidence for new real work. For RMS phasor voltage V, source-funded real power at the parallel port is G|V|².

**Finite-source weld:** With source RMS phasor Vs and a positive series source resistance Rs, Vtank=Vs/(1+RsY), Isrc=VsY/(1+RsY), and Re[Vs conjugate(Isrc)]=G|Vtank|²+Rs|Isrc|². Within this *linear passive fixed-parameter* model, when ImY=0, terminal-voltage magnitude is maximal while input-current magnitude is minimal as a function of detuning. Strong internal LC current can cancel at the source. This is an admissible **forward prediction** of a source-controller response, not a tested observation of Filsinger apparatus or a claim of donor energy.

**Reverse frequency identifiability:** Let K=1/L. At any single actual electrical angular frequency ω, only B(ω)=ωC−K/ω is available from terminal susceptance: row rank **one** for the two unknowns C and K. Many positive C,L pairs produce the same result, including zero B. For TWO distinct, synchronous, calibrated **electrical** frequencies w1≠w2 measured on the SAME physical unit with the same parameters and separately known conductive loading, the matrix [[w1,-1/w1],[w2,-1/w2]] has determinant (w2²−w1²)/(w1 w2)≠0; C and K are algebraically identifiable *within this selected passive model*. This does not identify Earth/chemical/RF input or a nonlinear source's coefficients, and does NOT promote the ~7.8kHz ±5Hz **ACOUSTIC** observation to an electrical frequency measurement.

**Conditional numerical example only:** At the reported nominal WHITE C=3.33µF, **if** 7800Hz acoustic were independently shown to be electrical and on that same C/L branch (not established), the ideal parallel resonance would require about **125.02787µH**. Kelly's separately sourced optional 47nF is NOT that 3.33µF Filsinger capacitor. Likewise ~1500V and ~6–7.3W from older occasion and Earth reel 0.4W/48V must not be merged into this hypothetical operating point. No source work or efficiency estimate follows.

**Local acceptance:** `/mnt/data/check_filsinger_parallel_lc_node_bidi_sympy_20261122.py` **78/78 local exact SymPy 1.14 PASS**, verified directly from the current executable bytes, covering two physical-diodes-per-component vs 1/2 electrical input-node cases; centre-return conditional OR; parallel-LC current opposition; full reactive-state derivative and cycle work; fixed-series-source power identity and antiresonant voltage-peak/current-dip; 1-vs-2 frequency inverse rank; distinct reel clock and source-funding counterworlds. The committed 37-case focused regression `scripts/check_filsinger_cap_coil_parallel_node_bidi_sympy_20261122.py` was **executed locally, 37/37 PASS** and **byte-matched** to Git blob `95173b7443770f83c58ed4e7bd9220f4f6d0b399`. The independent larger `/mnt/data/check_filsinger_parallel_lc_node_bidi_sympy_20261122.py` remains **78/78 PASS**. A first source-written 37-case companion failed solely on structural symbolic matrix equality; this was corrected to entrywise simplified equality and the final committed bytes passed. Do not conflate this mathematical check with original physical measurements or an Agda kernel receipt. New JSON ledger `Artifacts/smith-filsinger/cap_coil_parallel_node_quotient_bidi_20261122.json` contains exact conditional graph options, mathematical signatures and provenance gates.

| Gate | Mathematically paid | Original-world / verification remainder |
| --- | --- | --- |
| **D0 component labels** | Two transcribed diode groups can be cap/coil or winding wires | Source original terminal-by-terminal visual pin correspondence |
| **D1 electrical node quotient** | If cap across coil, C.first=L.first and C.second=L.second | Original literal 'across' physical continuity needs confirmation |
| **D2 diode landing** | Both U/V and one-node U/U source-group cases survive four package count | Which capacitor and coil *ends* touch each diode's anode |
| **D3 parallel topology** | Parallel LC admittance, sign crossing, antiresonance; series LC correction | Physical capacitor/coil are really in parallel, actual f/L/C/G and dynamic losses |
| **D4 finite-source work** | Exact series-source real-power closure and passive terminal peak/current dip | Selected nonideal transformer/driver plus returned current and signed source power |
| **D5 numerical inverse** | Single-frequency rank1 / two distinct actual electrical-frequency rank2 | Measured synchronized **electrical** frequency/complex V/I, same unit/parameters, known shunts |
| **D6 natural Earth donor** | Net donor still independent signed source term and original two-sided meter owners reusable | Actual Earth/chemical/RF source work, full storage, matched drive/no-drive control |
| **D7 code/proofs** | 78/78 independent local SymPy + 37/37 exact byte-matched committed regression, source-indexed Agda typed node quotient | Agda kernel not executed; no physical original wiring receipt |
| **D8 source attribution** | Filsinger midpoint vs ZVS vs three-Earth reel vs Kelly/Smith kept separate | Original physical evidence archive remains **0/24** real roles |

**Next BIDI hard cut:** Original diode-anode endpoints **and** the capacitor's exact two terminals must be resolved together: the strongest source-consistent working graph is a positive diode-OR against an **across-coil** parallel C/L with midpoint load return. But both cap-labelled and coil-labelled diode pairs may be the **same electrical net**. The earlier hard N=M bridge-clamp and R/C-mediated return remain alternate graphs—not automatically disproved. Only source-selected actual terminal continuity plus calibrated signed power can promote one physical apparatus.

---

## P1 BIDI source-phrase correction — midpoint return, two diode input groups, finite-source clamp (C0–C8)

**22 November 2026, user-sourced reverse correction.** Reopen the prior user's literal spoken transcript, not only the B0–B8 paraphrase. Alongside “two off of this wire, two off of that wire”, “all forward facing”, “ganging together positives”, “half the potential of the big coil”, “return to midpoint, earth, ground” and the capacitor/coil “pole shift”, the user transcript explicitly also says **“two diodes come off the cap, two diodes come off here.”** This is evidence for **two input-group descriptions**, NOT evidence that four diodes necessarily implement one conventional full bridge across the two outer transformer ends. The exact original reel/media-to-word linkage is still provisional; no original image was re-attested. Preserve Filsinger filmed three-Earth Dfi1D7CPzyM, earlier ZVS DfiqPnkPnP5, provisional midpoint/spark Dfu9Jseviz9 and compiled Smith/Kelly diagrams as separate source instances.

**Correction to previous exclusion:** the earlier B0–B8 conditional \`bridgeNegativeIsNotSourceMidpoint\` applies only to an ideal *unperturbed, nonzero, symmetric centre-tapped voltage source* with a conventional bridge whose DC-negative bus N is hard-bonded to winding midpoint M. It is **not a proof the actual physical design cannot operate**. In a real winding with finite source impedance, that bond changes the circuit: when A is positive and B negative relative to M, the bridge return diode **N→B** conducts, clamping the negative half-winding; on the other half-cycle **N→A** conducts. Thus the same nominal secondary cannot sustain both its unloaded negative voltage and a direct bridge N=M constraint without source-current backaction. The current is paid by the source, not an unexplained Earth donor. Similarly **H_SPLIT4** and **H_BRIDGE4** use *the same four oriented bridge diodes*; they are distinct midpoint/load-reference assignments, not independent diode orientation graphs. The prior “three survivors” were a nonexhaustive hypothesis list.

**New finite Agda original-BIDI owner** \`DASHI/Physics/Motors/SmithFilsingerMidpointReturnClampBacksolveExact.agda\` consumes the existing original transcript-number and prior midpoint-bidi owners, explicitly separates \`DiodePairGrouping\` (winding A/B vs capacitor/coil X/Y) from \`ReturnConnection\` (centre load return, isolated N, hard N=M, finite R, finite C or reactive L/C). Its \`noUniqueDiodeInputGroupingFromFourPackages\` is a finite theorem showing that diode package count cannot choose these distinct source groupings; the two-cycle \`conditionalClampingRoute\` encodes the negative-end return path under the conventional bridge/hard M bond. It reexports the **ideal** no-go under exactly its former assumptions. **Agda source-written, kernel NOT executed.** The focused root imports the module.

**New [source-worded machine BIDI ledger](../../Artifacts/smith-filsinger/midpoint_return_clamp_capcoil_bidi_20261122.json)** supplies the original phrases, five conditional circuit/return mechanisms, exact equations and seven forward/reverse discriminators. Old ledger \`midpoint_four_diode_bidi_reverse_cuts_20261122.json\` receives an explicit nonexhaustive/nonideal correction rather than deleting prior result.

**Executed independent local SymPy 1.14.0:** \`/mnt/data/check_filsinger_midpoint_return_backsolve_sympy.py\` **65/65 exact checks PASS**, including both source polarities, finite winding source resistance, hard-bonded bridge loop, resistive M↔N return, capacitive and LC reactive returns, diode OR input-group ambiguity and unchanged source-funding counterworlds. The committed companion \`scripts/check_filsinger_midpoint_return_backsolve_sympy.py\` contains the same selected model equations, but the original executed 65-case local file has **Git blob 8e08fde225a577df68036b618b064aa0b70786e8**; do not claim committed-byte identity unless its separate blob is verified and executed.

For source half-voltage amplitude \(|v|>0\), model half-winding series resistance \(R_s>0\) and positive output load \(R_L>0\):

\[
I_{\rm clamp}=\frac{|v|}{R_s},\quad
P_{\rm copper,clamp}=\frac{v^2}{R_s},\quad
V_{\rm load}=\frac{|v|R_L}{R_s+R_L},\quad
P_{\rm load}=\frac{v^2R_L}{(R_s+R_L)^2}.
\]

This assumes independent ideal half-winding Thevenin sources, zero-drop diode and an otherwise standard bridge with hard N=M, **not actual measured coils**. Exact source funding is \(P_{\rm source}=P_{\rm load}+P_{\rm copper,positive}+P_{\rm copper,clamp}\). The normalized example \(|v|=1,R_s=1,R_L=2\) gives output \(2/9\), negative winding heat 1, positive winding heat \(1/9\), source power \(4/3\), useful fraction **1/6**: direct clamping can be costly, not amplifying. When the return includes positive series resistance \(R_b\) instead, \(I_{\rm return}=|v|/(R_s+R_b)\) with \(V_N-V_M=-|v|R_b/(R_s+R_b)\). With a **capacitor** in that return, in an RMS phasor model \(I=V/[R_s+1/(i\omega C)]\) and \(\overline P_{\rm source}=R_s|I|^2\) while ideal capacitor mean real work is zero; an **LC path** \(Z=R_s+i(\omega L-1/(\omega C))\) can rotate phase or resonate but must pay all resistive/controller/source work.

**Separate literal-diode input grouping:** a *hypothetical* positive diode-OR pair from a capacitor-coupled node X and coil node Y can use four packages arranged two each with ganged cathode/output P. This directly respects “two off the cap, two off here” and literal “all forward facing” better than assuming a full conventional bridge. It still requires genuine separate electrical X/Y nodes and a defined return M/N; the capacitor is not an independently replenished natural source. Two equally named wires may actually be the same node after tracing. Source count, source voltages, rectified currents and natural inflow are not established by the phrase “harvest amperage.”

| Gate | Paid source/math progress | Physical or formal payment still missing |
| --- | --- | --- |
| **C0 exact words** | Restored direct “two diodes off cap, two off here”, return “midpoint, earth, ground” | Original filmed diode cathode/anode and exact clip provenance |
| **C1 connectivity** | Separate diode input-group pairing from count, ordinary bridge skeleton from split-rail load choice | Whether cap/coil X/Y, winding A/B and positive P actually coincide |
| **C2 finite bridge return** | Both half-cycle clamp routes, source finite impedance/heat, original ideal exclusion scoped | Actual transformer resistance/inductance and whether N=M really hard-wired |
| **C3 mediated return** | Exact resistor and capacitor/LC phase-dependent work, no free source energy | Original intervening impedance/component between N, M and Earth |
| **C4 half voltage** | CT and bridge distinct expected P-M/P-N voltage reference | Original measurement terminals, waveform, peak vs RMS, phase |
| **C5 Earth steelman** | Receiver may couple external donor via driver; output-only funding rank underdetermined | Original signed Earth/chemical/RF and controller/drive/load work, storage return |
| **C6 Agda and math** | New finite source-owner module, 65/65 local exact arithmetic | Agda kernel receipt; committed companion execution separately required |
| **C7 historical identity** | No automatic Kelly/Filsinger circuit collapse; no automatic coil-cap donor | Exact original reel/source to pin correspondence |
| **C8 safety** | Source text/ideal reverse solve only | No hazardous live HV test or construction recommendation |

**Next logical step:** classify physical node **N↔M** as hard, finite-capacitive, finite-resistive, switch/diode-mediated or separated, and classify **X/Y** as distinct capacitor/coil versus the two winding ends. Those two independent decisions now dominate the source-constrained inverse problem. Original empirical raw evidence archive remains **0/24** roles; the mathematical result does not establish actual atmospheric or Earth energy extraction.

---

## P1 same-source steelman BIDI reverse solve — midpoint, four diodes and Earth return (B0–B8)

**22 November 2026: user-requested logical inverse cut after V0–V7 audit.** Do not ask for arbitrary new hardware drawings before exhausting source-constrained candidate completions. The prior user's literal midpoint/NST transcript states **two diodes off each secondary wire, four total, all forward facing, positive outputs ganged, centre tap accessible, return described as midpoint/Earth/ground, half the big-coil potential, capacitor across a selected coil causing a claimed pole shift, spark-gap dump and coil claimed to receive amperage**. The exact reel association to \`Dfu9Jseviz9\` is provisional; these words do not turn the separate three-Earth-contact \`Dfi1D7CPzyM\` or shunt \`DfiqPnkPnP5\` into the same physical build. Do not collapse Kelly/Smith Fig10/11/40 or the earlier user-observed blue/green part candidates into a single authoritative wire diagram.

**Original source-owned machine contract:** \`Artifacts/smith-filsinger/midpoint_four_diode_bidi_reverse_cuts_20261122.json\` records six transcript constraints, four literal circuit completions, forward predicted voltages and reverse pin discriminators. \`DASHI/Physics/Motors/SmithFilsingerMidpointDiodeBidiReverseSolveExact.agda\` reuses the original source-indexed number and reel/Smith distinction owners, then enumerates the four completions as hypotheses, exact diode endpoint roles and a two-world theorem \`noUniqueTopologyFromDiodeCount\`. It proves a distinct ideal-source conditional no-go \`bridgeNegativeIsNotSourceMidpoint\` for an active symmetric centre-tapped secondary. No Agda binary available, **kernel unverified**, and no source-to-diagram proof of original connections constructed.

**Executed and exact source-matched local comparator:** \`scripts/check_filsinger_midpoint_bidi_reverse_sympy.py\`, **75/75 exact local SymPy 1.14.0 PASS** with identical executed/committed Git blob \`645294205eaade3f1799d4c921cce903db7bc13c\`. Model \`V_A-V_M=v(t)\`, \`V_B-V_M=-v(t)\`; ideal rectifier zero forward drop, finite active half-winding voltage \`|v|>0\`. Four mutually distinguishable hypotheses:

| Completion | Forward prediction (under the ideal active model) | Reverse classification |
| --- | --- | --- |
| **H_CT4**: centre-tapped full-wave with two forward diode packages from A and two from B, ganged positive P; midpoint return | \`V(P)-V(M)=|v|\`, four packages but only **two distinct positive-rectifying electrical paths**; parallel device sharing remains unknown | Supports strict “all outward / all forward facing”, “half big-coil potential”, midpoint return; demands source proof why diode packages are duplicated or separately connected |
| **H_BRIDGE4**: conventional four-diode bridge across outer winding A-B, negative DC bus N independent of midpoint | \`V(P)-V(N)=2|v|\`, \`V(N)-V(M)=-|v|\`; two conducting diodes per polarity | Four diodes/two off each secondary, positive outputs ganged compatible; strict centre tap is DC-negative, “all outward”, or half-winding receiver output require further interpretation |
| **H_SPLIT4**: same four-diode bridge skeleton but separate upper/lower rectified loads referenced to centre midpoint | \`V(P)-V(M)=|v|\`, \`V(M)-V(N)=|v|\`, \`V(P)-V(N)=2|v|\` | Four diodes + centre mid-rail + half-potential claim compatible; “all forward facing” is not literal winding-end-to-positive orientation for return diodes; negative-rail/capacitor endpoint unobserved |
| **H_BRIDGE_N=M**: ordinary bridge DC-negative **hard bonded to centre tap** | Implies \`V_N-V_M=-|v|\` and \`V_N-V_M=0\` for \`|v|>0\` | **NO-GO under ideal nonzero symmetric transformer model**; in nonideal hardware source/diode impedance would determine high circulating/clamp currents, not a free energy path. Actual physical wiring is NOT asserted to be this |

**Forward/reverse inference:** the spoken “half potential of the big coil” favors \`P-M\` half-winding/mid-rail output **IF** the measured voltage is referenced to centre; it does not identify a specific diode diagram without the output terminal pair and polarities. Under the strictly conditional 4000V output description, \`H_CT4\` interpreted as P-M demands 4000V peak on each half-winding (8000V outer-to-outer), while \`H_BRIDGE4\` interpreted as P-N demands 2000V per half (4000V outer-to-outer). Both produce the **same stated output** with different unknown transformer source amplitudes; this is explicit non-identifiability. The original 20kV/1µF vs 10kV/2µF capacitor alternatives both have **20mC nominal charge** at their respective illustrative voltages but **200J vs 100J** potential stored energy. At 4000V, if those parts happened to have that across their terminals, stored energies would be 8J vs 16J. **Ratings are not operation; neither output voltage, power nor source is inferred by a capacitor label.**

The “capacitor across selected coil causes a pole shift” is an empirical *speaker hypothesis*; an ideal periodic capacitor has \`i_C=C dv/dt\`, \`dU_C/dt=v i_C\`, \`∮v i_C dt=0\`. It may alter resonant phase/loading or switching behavior, but it is not its own net positive energy source. A spark-gap dump can transfer stored energy into another port/dissipation; it does not establish independently replenished work. The user's steelman remains **source-access control**: a driver could increase coupling to a separate natural reservoir, but the environment's net work and replenishment must enter through a physically sourced signed port, not by phase or naming a third Earth electrode.

**BIDI source-sink counterworld:** two *illustrative* constant-power ledgers have the same **0.4W useful load** and 0.1W loss. World A: 0.5W drive, 0W natural. World B: 0.2W drive, 0.3W separately admitted natural. Both conserve power, so useful-load display alone has rank **1** over four unknown signed terms \`(W_drive,W_environment,W_loss,ΔU)\`, nullity **3**. This is NOT a claim that 0.4W was experimentally calibrated real output or that natural work was present. The separate Earth reel's three contacts yield only two independent relative potentials; they do not select which contact is environmental source, return, chemical cell or meter reference. Controller on/off alone may not identify upstream work when it changes the source.

| Gate | Conditional mathematical result | Actual original evidence demand |
| --- | --- | --- |
| **B0 literal transcription** | User midpoint phrases recovered, six source constraints; reel attribution qualified | Original exact video occasion/time and source-authenticated clip |
| **B1 four diode forward images** | Four candidate graphs; 4 packages, 2 per outer wire, positive bus not a unique full netlist | Anode/cathode for each package and all shared positive/negative nodes |
| **B2 centre-tap / Earth relation** | Active bridge DC-negative-to-M bond conditional no-go; CT/split/isolated bridge otherwise compatible | Actual M, N, P, three Earth contacts and rectified returns must be node traced |
| **B3 half-voltage reverse** | CT \`P-M=|v|\`; bridge \`P-N=2|v|\`, split rails both outputs | Original measured voltage probe terminal pair and peak/RMS/time convention |
| **B4 capacitor/phase** | 20mC equal charge vs 200/100J distinct storage; periodic capacitor signed work zero | Original capacitor two pins, voltage waveforms, true discharge/dissipation and material dynamics |
| **B5 source-access** | Two worlds with same 0.4W readout but drive-only vs external donor; output rank one | Independent signed Earth, electrochemical, ambient RF, driver, load, thermal and stored work |
| **B6 Smith/BIDI provenance** | Kelly 17+17, 1:4 **wire length**, optional 47nF and different Fig10/11/40 not automatically Filsinger circuit | Explicit mapping from one original Smith figure to each *verified* Filsinger component/pin |
| **B7 original physical meter** | Reuse existing OriginalMaxwellMeterIntervalWeldExact (two-sided) and OriginalMaxwellRestoredMeterFundingExact | Same original time-indexed physically calibrated v(t)i(t), source, return and restored cycle |
| **B8 formal and empirical** | 75/75 local exact SymPy, new finite Agda source; draft PR | No Agda kernel receipt; original audited source evidence archive still 0/24 roles |

**Next logical action:** discriminate \`H_CT4\`, \`H_BRIDGE4\` and \`H_SPLIT4\` by original **diode direction, positive-output, centre-tap, DC-negative and capacitor node labels**, and only then integrate physical source work. Further ideal RLC tuning scans are lower priority than resolving those **three exact graph differences**. No hazardous real HV experimentation or construction advice is entailed.

---

## P1 transcription/diagram source-reconciliation — measured vs reported vs nominal (V0–V7)

**22 November 2026 corrective audit, user-requested.** The prior U0–U8 phrasing "missing all the numbers" was materially too broad. The repository already contains a significant amount of source-specific **transcribed values** and a user-uploaded 147-page Kelly/Darrer Smith figure audit. Re-read `Docs/research/FilsingerLydenEarthPortMaxCut20261110.md`, `Docs/research/FilsingerEarthThreeElectrodesZVSFrequencyPull20261110.md`, `Docs/research/SmithFilsingerSourcePortShuntMaxCut20261115.md`, `Docs/research/DonSmithHighPowerDevices147PageOriginalPDFMaxCut20261112.md`, `Docs/research/SmithFilsingerNonlinearQuadratureMaxCut20261112.md`, and the original partial graph JSON `Artifacts/smith-filsinger/source_bound_circuit_transformations_20261115.json`. Recovered the prior user-spoken commercial midpoint/NST transcript: 4 diodes, midpoint/Earth return proposal, positives joined, 20 kV/1µF or 10 kV/2µF alternative capacitor examples and approximate 4kV output wording. Its **exact clip/occasion attribution to Dfu9Jseviz9 is not independently verified**; DO NOT place these parts on the three-ground reel by assumption.

**Direct visual PDF corroboration:** separately inspected the accessible Patrick J. Kelly chapter [KellySmith.pdf](https://www.rexresearch.com/SmithOUDevices/KellySmith.pdf), printed pp3-44 to 3-46. This is a source edition of the Kelly material, **not a replacement for the originally uploaded Darrer 147-page edition or a Filsinger circuit photo**. It confirms L2 two 17-turn sections, 160-inch wire for a selected L2 section vs 40-inch L1 wire **in its worked example**, 2.25-inch effective primary diameter and approximately 5.65 or 5⅔ L1 turns, leaving a nominal 240° winding endpoint offset. These are **mechanical winding/length statements, not secondary electrical phase, fourfold voltage gain or observed harmonic field**. The same Kelly circuit illustration describes an optional 47 nF capacitor across L2, two high-voltage rectifiers into an output capacitor bank, a four-diode battery-charging arrangement and a **claimed** 2,000 V / 6,000 W output. Those are *Smith/Kelly source* claims/figures, not hardware components or observed powers on the Filsinger Earth reel. The original compilation distinguishes its own Fig.10 p28, Fig.11 p29 and later editorial Fig.40 p65.

**New source-indexed machine-readable ledger:** `Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json`: **6 source/occasion owners, 43 numeric/descriptive entries, 8 partially narrated/compiled electrical connections**, each with source and evidentiary status. Owners: (FZVS) shunt reel DfiqPnkPnP5 (approx 3.3µF and 1/2/4MΩ); (FO) earlier observations (~15V, 6–7.3W, 1500V, 7.8kHz *audio*, not one verified interval); (FE) three-ground reel Dfi1D7CPzyM (~3.8V, 0.4W, 48V across two caps); (FW) white 3.33µF cap narrator's hot→Earth-negative partial edge with reel occasion unconfirmed; (FM) prior commercial midpoint/NST spoken transcript, with **candidate** Dfu9Jseviz9 attribution; and (SPDF) Kelly/Darrer source diagrams. **No original complete pin netlist is constructed** and the partial edges say `proven_continuity:false`. Source-specific values are now OWNED, not generically "missing."

**New typed Agda scope firewall:** `DASHI/Physics/Motors/SmithFilsingerTranscriptDiagramNumbersSourceIndexExact.agda`. `SourceOccasion` and indexed `SourceNumber` explicitly separate the six source groups; `numberMagnitude`, `numberUnit`, and `sourceStatus` preserve scales, nominal component claims and *unpaired* older readings. It imports the original Smith diagram and Filsinger source identity/prohibition modules and demonstrates original Earth reel != ZVS or midpoint source, and Smith PDF Figure 10 != Figure 11. **This is source-written, Agda kernel NOT executed.** Its purpose is not to invent current, voltage, field or extra energy by assigning a recorded number to the wrong source.

**Local exact SymPy** `scripts/check_smith_filsinger_transcribed_diagram_inventory_sympy.py` **44/44 PASS**, exact Git blob **`0b827315c2dcc8e82cdc8a3d6fca807b894fd7d7`** matches locally executed bytes. Additional independent local `check_filsinger_transcript_diagram_numbers_sympy.py` **52/52 PASS** (source-equivalent, not the committed script). Useful *conditional* numbers:
- White nominal C=3.33µF at **hypothetical** 1500V contains **3.74625J**; a *separately assumed* 1MΩ shunt at 1500V **DC/RMS** dissipates **2.25W**, 2MΩ 1.125W, 4MΩ 0.5625W. Three independent shunts would dissipate 6.75W only *if all at 1500V DC simultaneously*, never assumed as the original circuit.
- The **narrated alternatives** 20kV/1µF and 10kV/2µF would store respectively **200J** and **100J if actually charged to those example voltage figures**; a **rated voltage does not establish an operating voltage**.
- The unrelated Earth-reel displays ~3.8V and ~0.4W would imply ~0.1053A, ~36.1Ω only under **same-time/same-port real resistive-load conditions**. The 48V pair-voltage lacks capacitance, terminal-reference and waveform identity.
- Kelly 40in/160in yields **1:4 selected wire length**, while its separate 17+17 turn count is **not** a 1:4 turns ratio. Approx 5.659 turns at 40in/2.25in corresponds to the source's about 5.65-turn geometric example, not a phase meter. The optional 47nF capacitor is not Filsinger's 3.33µF cap. Kelly's 2000V×3A=6000VA only becomes real watts if separately verified.
- Earlier ~15V input and 6–7.3W, other ~1500V indication and ~7800Hz **acoustic** must not be silently multiplied with the Earth-reel 0.4W or interpreted as measured ZVS frequency.

| Gate | Updated owner and actual paid evidence | Remaining |
| --- | --- | --- |
| **V0 recover numbers** | 43 claims with per-reel and Smith figure source references in JSON | **PAID for archived transcribed labels; reinspection of unmounted original reel still OPEN** |
| **V1 source identity** | Six source occasions typed; original Smith Fig10/11/40 and Earth/ZVS/midpoint explicitly distinct | **PAID at source label level**, midpoint clip association provisional |
| **V2 physical parts** | 3.33µF white, ~3.3µF shunt components, 1/2/4MΩ, midpoint 4 diodes, alternative capacitors, Smith wire sizes and 47nF | **Nominals/source narrations known**; actual installed part/pin mapping remains OPEN |
| **V3 circuit edges** | Eight narrated/editorial partial edges, including white hot→Earth-negative and proposed midpoint rectification | **Source-specific graph is partial**, real Earth three-electrode loop/ground current still OPEN |
| **V4 math** | 44-case exact same-source-per-occasion model arithmetic and 52 independent local cases PASS | **No actual-vs-nominal voltage measurement**, no Agda kernel |
| **V5 original same-time terminal** | Original `SmithFilsingerOriginalMaxwellMeterIntervalWeldExact` already has two-sided signed intervals | **OPEN simultaneous original V/I**, source clock, meter COM and uncertainty |
| **V6 physical/source discriminant** | Original `SmithFilsingerOriginalMaxwellRestoredMeterFundingExact` already couples original Maxwell port and source-cycle funding | **OPEN independent Earth/chemical/RF/driver source**, complete source return and storage closure |
| **V7 original diagrams** | Kelly chapter visual and source-derived example numbers verified; historical Smith F10/F11/F40 must remain separate | **No demonstrated electrical equivalence** to Filsinger filmed Earth/portable circuitry |

**Corrected controlling requirement:** not "find missing component values" as a blanket task. It is to **complete the pin-to-node mapping with per-connection provenance**, resolve which transcribed midpoint pieces match which actual reel, and obtain independently calibrated simultaneous signed work for that selected physical circuit. The rigorous original 24-role evidence inventory stays at **0/24 real attached roles** despite this better archival recovery. No high-voltage build instructions or experimental natural-power claim.

---

## P1 original Earth-reel three-electrode maximum cut — topology, return, metering (U0–U8)

**22 November 2026, primary-source correction.** The original source inventory in [FilsingerEarthThreeElectrodesZVSFrequencyPull20261110.md](../research/FilsingerEarthThreeElectrodesZVSFrequencyPull20261110.md) records the user's supplied reel `Dfi1D7CPzyM`: **three electrodes called Earth grounds**; speaker-reported approximately **3.8 V, 0.4 W and 48 V across two capacitors**. Source identity of the actual contact pins, material/spacing, return-current topology, meter polarity, and whether these are simultaneous measurements is NOT established. The original speaker's ground-energy attribution is a **hypothesis**, not validated harvesting. The filmed Earth configuration is not the separately proposed portable two-plate receiver.

**Previously existing original physical authority is stronger than earlier crosswalks credited.** The source-owned `SmithFilsingerSelectedSpaceTimePortWeldExact`, `SmithFilsingerOriginalMaxwellMeterIntervalWeldExact` and `SmithFilsingerOriginalMaxwellRestoredMeterFundingExact` ALREADY supply conditional original-source Maxwell/selected-meter identification, **two-sided signed work uncertainty** and restored-cycle source-paid work transport. They need actual original data, not another source-agnostic meter theorem. The source-first evidence contract ([JSON](../../Artifacts/smith-filsinger/source_first_original_evidence_contract_20261117.json)) has original pin graph, geometry, V/I, return work, source replenishment and kernel still NULL. The latest source-first inventory [SmithFilsingerFiveGateEvidenceAcceptance20261117.md](../research/SmithFilsingerFiveGateEvidenceAcceptance20261117.md) reports **0/24 original-world measurement/evidence roles attached to its archive**, not a physical impossibility result.

**New source-grounded finite no-go.** `DASHI/Physics/Motors/SmithFilsingerThreeEarthElectrodeReturnIdentifiabilityExact.agda` preserves the actual reel versus portable original identity, then defines an independent, illustrative **three-node reciprocal passive conductor** and source-written rational KCL/work identities. Its finite `noUniqueWorkMapFromSinglePairDisplay` explicitly blocks inferring total three-contact work from one displayed pair voltage. No historical electrode spacing, wiring, soil conductivity or current is invented; no Agda kernel receipt is available.

**Exact locally executed SymPy:** `scripts/check_filsinger_three_electrode_original_sympy.py` **44/44 PASS** on SymPy 1.14.0, Git blob **`6d0b969ce537ed9b67c844e8fef1b3da901437ef`** identical to the executed local bytes. The finite reference graph has

\[
\mathbf I=L\mathbf V,\qquad
L=\begin{pmatrix}
g_{12}+g_{13}&-g_{12}&-g_{13}\\
-g_{12}&g_{12}+g_{23}&-g_{23}\\
-g_{13}&-g_{23}&g_{13}+g_{23}
\end{pmatrix},
\qquad L\mathbf 1=0,\quad \mathbf 1^\top\mathbf I=0.
\]

Its passive work is \(P=\mathbf V^\top L\mathbf V=\sum_{i<j}g_{ij}(V_i-V_j)^2\). This is gauge/common-mode invariant and needs **two independent relative voltages** rather than three independently defined voltage origins. With \(V_1-V_2=1\), all unit \(g_{ij}\), and unobserved \(V_3=0\) versus \(V_3=\tfrac12\), the model produces *the same pair display* while its **total network power differs (2 vs 3/2)**. Hence total work is not identifiable from that voltage alone, independent of any conjecture about harvesting.

For a chosen gauge \(V_3=0\), the reduced two-port is \(Y=\begin{pmatrix}g_{12}+g_{13}&-g_{12}\\-g_{12}&g_{12}+g_{23}\end{pmatrix}\). In this **exact linear passive three-edge model**, a single independently measured excitation with both currents has rank 2 for three unknown conductances; two linearly independent voltage/current excitation patterns make the conductance-observation matrix **rank 3**. That does NOT identify natural generation, electrode chemistry or the original unknown topology.

The reel's two separately reported values, 3.8 V and 0.4 W, would **conditionally** imply \(I=\frac{2}{19}\,\mathrm A\approx0.1053\,\mathrm A\) and \(R=36.1\,\Omega\) *only if* they were simultaneous real power and voltage at the same resistive load. Similarly 48 V does not identify capacitor stored joules: the same two capacitors each individually at 48 V store **four times** as much as two identical capacitors in series with 48 V *across the complete pair*, assuming equal capacitance. Neither conditional calculation fills the actual original measurement.

| Gate | Actual source and mathematical contribution | Remaining |
| --- | --- | --- |
| **U0 original identity** | Exact separate filmed Earth and proposed portable `Bidi.Configuration` | Still no physical pin netlist |
| **U1 real pin/return** | Three electrodes, geometry, chemistry, actual meter terminals, signed third return | **OPEN evidence** |
| **U2 mathematical triad** | Passive conductance Laplacian, KCL, complete signed 3-port work, common-mode | **44/44 symbolic PASS**; Agda source written, kernel unverified; reference model only |
| **U3 readout obstruction** | Same two-terminal voltage, different full network work | Finite Agda no-go and symbolic counterexample; **not hardware result** |
| **U4 experimental identifiability** | Matched full \(v,i\) observations on two independent model excitations, topology/return fixed | Synthetic matrix rank 2→3; original readout still missing |
| **U5 existing full meter** | Source's selected spacetime Maxwell port, two-sided meter and funding theorem | Already source-written; original synchronized and traceable V/I absent |
| **U6 source provenance** | Separate Earth/chemical/RF/driver/capacitor ports including outgoing return and all losses | **OPEN**, no inference from total current |
| **U7 reported numbers** | Conditional 3.8 V/0.4 W and 48 V capacitor branches | Same-port and same-time basis not established |
| **U8 empirical/kernel** | Source-first 24-role audit, physical original data, Agda 2.9 kernel | Original archive **0/24**, Agda not locally installed |

**Next maximum physical cut:** the original pin/return geometry and signed meter provenance; then instantiate the *already existing* original two-sided meter and source-restored cycle on those data. The acoustic 7.8 kHz is not yet an observed electrical frequency. No high-voltage or atmospheric intervention is prescribed.

---

## P1 actual field-to-port mathematical cut — TEM exact source-access donor and independently instrumented inertial response (T0–T8)

**21 November 2026.** The last Z0–Z7 source weld exposed a genuine missing lemma: sharing an original Filsinger boundary \`b\`, field-to-port record \`f\` and source-cycle \`s\` is NOT sufficient to identify the full-vector Maxwell energy work with the finite mesh's work. We therefore strengthen the existing Agda source, not construct a replacement field ontology.

### New typed identification of the SAME selected work

\`YMEMForceGravityFilsingerSameOriginalPhysicalCutExact.MeasuredSameFieldMeshWorkIdentity w\` requires three **actual equalities on the exact source-selected mesh and full-vector physical admission**: (1) mesh load = integrated full-vector load, (2) mesh initial stored = vector field+material initial stored, and (3) mesh final stored = vector field+material final stored. These are *independent real physical input requirements*, not derived by merely matching b/f/s names. From (1) and the already-owned \`Poynting.SameOriginalPhysicalFieldBoundary.originalUsefulPortIdentity\`, the new \`originalMeasuredMeshLoadIsActualSelectedReceiver\` uses equality transitivity to derive the selected terminal useful-work identity. The new \`originalFullVectorMeshSourceCapWithMaterialModulation\` consumes the pre-existing \`Poynting.selectedFullVectorPhysicalAdmissionCap\`; unlike the earlier Filsinger cap it retains explicit **paid material modulation**. The original \`Anti.requiredDiscriminator alteredInertialResponse = inertialComparisonDiscriminator\` is now reexported.

This is a stronger **source-written conditional composition**, NOT an Agda kernel receipt. Even the three work/storage equalities are NOT a measured \`E/H\` face/quadrature identity. The exact per-face field, physical normal, surface/line integral, conductor return, original source time/history, measured terminal \`V(t),I(t)\`, material ADE/plasma work and original actual natural-source data **remain OPEN**. The earlier \`OriginalFiniteVolumeAdmission.selectedFullVectorMaxwellFieldToFaces : Set\` is not sufficient evidence if filled with an arbitrary inhabitant; a future physical adapter must replace/justify it with contentful same-field measurements and coordinates.

### Exact local Maxwell PDE → original-form field-to-power reference (not Filsinger hardware)

New committed \`scripts/check_filsinger_maxwell_tem_inertia_original_sympy.py\` was **executed locally: 74/74 PASS**, SymPy 1.14.0, with the **exact executed Git blob** \`c12f5cf44a3ab760dc1e83bc37ddd00e7f0eeb6a\`. It models an *ideal lossless concentric two-conductor TEM line*, not the source-unknown historical Filsinger receiver. A genuinely variable causal waveform \(A(u)\), \(u=t-z/c\), in homogeneous material with \(c=1/\sqrt{\mu\epsilon}\), \(\eta=\sqrt{\mu/\epsilon}\), has

\[
E_r=A(u)/r,\qquad H_\phi=A(u)/(\eta r),\qquad
V=A(u)\log(b/a),\qquad I=2\pi A(u)/\eta.
\]

The explicit vacuum-dielectric Maxwell Gauss, Faraday and displacement-current Ampère equations hold, and a real **oriented annular cross-section** gives

\[
\boxed{ \int_{a<r<b}(\mathbf E\times\mathbf H)\cdot d\mathbf A
       = \frac{2\pi A(u)^2}{\eta}\log(b/a)
       =V I. }
\]

Five exact radial annular finite-volume partitions (N=1,2,3,5,9) each return that identical work. For a nonstationary waveform and a finite axial/time slab, the **signed Poynting storage identity** holds with unequal start/end storage (normalized demonstration: \(W_\mathrm{in}=1184\pi/45\), \(W_\mathrm{out}=704\pi/45\), \(U_\mathrm{final}-U_\mathrm{initial}=32\pi/3\)). Field energy is thus not automatically useful load output. Forward and backward Maxwell solutions individually satisfy the curl equations; their superposition's integrated signed transfer is proportional to \(A_+^2-A_-^2\): **equal forward and reflected waves mean zero net power in spite of nonzero instantaneous field magnitude**. For a passive real terminal \(R_L\) and line impedance \(Z_0\), \(\Gamma=(R_L-Z_0)/(R_L+Z_0)\) and \(P_\mathrm{load}=P_\mathrm{incident}(1-\Gamma^2)\), maximized at matching. With a fixed useful load, the script checks **series-access versus parasitic shunt**, including an example where an externally powered transfer gain is smaller than the model's controller cost.

**Research significance:** this is the correct mathematical kind of **field → actual geometric flux → \(VI\) terminal** proof absent from the original Filsinger application. But the coax is an independent reference. To promote anything about a Filsinger source, obtain a **source-labelled map** from his actual electrodes, returns, field faces, dielectric/plasma properties and time-varying ports to a comparable solved Maxwell/ADE configuration. Neither \(P=VI\) in this example nor a 369 gauge orientation is proof of his experimental machine's performance.

### Original antigravity five-channel collision — exact independent inertial discriminator

The original \`Four.signature ordinaryForceConfounder\` equals \`Four.signature inertiaOnlyCandidate\`. The new local exact physical *toy* model separates **independent controlled mechanical force pulses** \(F_d\) and **measured magnetic-gradient source modulation** \(G_s\), with selected acceleration

\[
a(F_d,G_s) =
\frac{F_d+\beta G_s-m_g g}{m_i},
\qquad
a_{\rm inertia\,rival} =
\frac{F_d+\beta G_s-m_g g}{\kappa m_i}.
\]

The static support load \(m_gg-\beta G_s\) contains **no \(m_i\)**, so it cannot identify inertial mass. With normalized identical weight/equilibrium and one unit calibrated force pulse the two toy predictions are \(1/2\) versus \(1/4\) acceleration; this is a **rival-model conditional prediction**, not a reported antigravity signal. The observation design \(a=pF_d+qG_s-r\) has rank **1** with only one static measurement and rank **3** with independent field-off, force-on and gradient-on comparisons. It is sensitive to calibration of the real force and field, non-EM backgrounds, specimen mass, phase, temperature, force-pulse reaction path, measurement latency and independent replication. It does not close all possible alternative hypotheses or infer a nonstandard inertial mechanism.

| Gate | New exact source target | Status and what remains |
| --- | --- | --- |
| **T0** | Selected original Filsinger full-vector jet **and** finite mesh | Existing Z0 source record; no actual Filsinger Maxwell field or original physical ports inhabited |
| **T1** | \`MeasuredSameFieldMeshWorkIdentity\` loads and initial/final stores | New contentful *conditional Agda record*; **independent same-field measured identity OPEN** |
| **T2** | \`originalMeasuredMeshLoadIsActualSelectedReceiver\` | Source-written transitivity from actual mesh/vector work to the original selected terminal, kernel pending |
| **T3** | \`originalFullVectorMeshSourceCapWithMaterialModulation\` | Source-written reuse of the actual full-vector **paid-material** bound; physical integration, source cap admission and source replenishment OPEN |
| **T4** | Ideal causal coax TEM geometry → exact \(E\times H\) cross-section → \(VI\), five radial face cuts and finite stored-work history | 74/74 exact local SymPy full suite; **reference mathematical example, not original Filsinger geometry** |
| **T5** | Forward/backward fields, reflection/matching, source-connected series versus dissipative shunt | Exact independent passive reference; useful load ≠ field magnitude or gross incident work; net-after-pump positive extraction NOT inferred |
| **T6** | \`Anti.alteredInertialResponse\` → original \`inertialComparisonDiscriminator\`; source force pulse + magnetic-gradient controls | Existing antigravity typed demand re-exported; exact illustrative rank 1→3 identifiability; actual instrumented responses OPEN |
| **T7** | Original Filsinger source actual E/H faces, conductor return, Maxwell–ADE, same physical energy and terminal SI data | **OPEN**; do not substitute coax or symbolic source cap for actual source work |
| **T8** | Real antigravity claim-specific GR/freefall/clock/inertia/TT source and ordinary EM/thermal/torque confounder closure | **OPEN**; original Podkletnov, NASA, Hathaway, Tajmar, Amy evidence statuses unaffected |

**Kernel status:** no Agda binary locally. Source-written code is not certified by SymPy. **Independent physical evidence status:** none newly admitted. Preserve original source credit, real historical nulls and no assumption that Filsinger and antigravity refer to one apparatus.

---

## P1 strongest original-source weld — 3D EM support × antigravity experiments × Filsinger (Z0–Z7)

**21 November 2026 correction.** The actual source of the next mathematics was already on master. SmithFilsingerFullVectorPoyntingPortWeldExact has the KSW668 **full three-component Maxwell jet** and a separate, conditional field-to-terminal spacetime integration implication; SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact has the **original oriented finite-volume faces** and an exact selected-source terminal balance. The exact gravity owners AntigravitySameStateFourChannelDiscriminatorExact, AntigravityLaboratoryOrdinaryModelClosureWeldExact and SuperconductingGravityCouplingResidualBidiExact already provide the force-versus-gravity signatures, actual conditional laboratory GR/background closure and the first missing source observable. OrientedBracketEMYMNS369Regression and RightHandRule369Exact already connect EM/YM through the original signed 369 orientation, without identifying E×H, qv×B, Iℓ×B and μ×B as one measured physical observable.

**New source-written Agda:** DASHI/Physics/Foundations/YMEMForceGravityFilsingerSameOriginalPhysicalCutExact.agda. Its dependent SameOriginalFilsingerFullVectorAndFiniteMesh jet b f s requires BOTH the original SameOriginalPhysicalFieldBoundary jet b f s and OriginalFiniteVolumeAdmission b f, with exactly one selected original Filsinger source/field/port/cycle. Derived projections selectedRealMeshToOriginalPort, selectedRealMeshClosesOriginalSignedPort and selectedRealMeshStillPaysOriginalNaturalCap reuse existing master theorems; no independently asserted physical source is added. It additionally reuses the actual five-channel ordinary-force comparator, source-only/constitutive observational collision, original GR/background dependent closure, U1⊂SU2 Lie bracket, and original 369 EM/YM signed orientation. All sources are **conditional input records**, with NO constructed original apparatus measurement receipt and no local Agda typechecking.

**Fresh local exact SymPy 29/29 PASS, byte-identical to committed Git blob 142624d1030a187b7d733ec0779239358c5015c8:** scripts/check_ym_em_filsinger_gravity_3d_comparator_sympy.py. An illustrative static vacuum-compatible B=(Gx,Gy,B0−2Gz), div B=curl B=0, and a linear diamagnetic potential U=−α B²/2+mgz with normalized G=B0=1, α=−1, mg=2 produce equilibrium at the origin with upward material magnetic force equal to weight and **positive-definite 3D Hessian diag(1,1,4)**. Surrounding vacuum Maxwell stress has zero divergence; the modeled force is from material response and interfaces, not a vacuum body-force density or changed gravity. Nonzero holding force requires no instantaneous *mechanical* work at rest, but apparatus source/cryogenic/control costs remain independent. No real Filsinger device or exotic gravity measurement was involved. The experiment signatures show weight-only aliases EM support and a selected scalar metric candidate, while ordinary-force and inertia-only classes themselves remain identical under the model's five Boolean channels; an independent inertial response test is therefore not discharged.

| Gate | Existing original owner | Result or OPEN source |
| --- | --- | --- |
| Z0 same full-vector + mesh source | KSW668 Maxwell jet, Filsinger physical jet-to-work and oriented mesh | New dependent record on exact b/f/s; actual field integration, device mesh and measured natural source OPEN |
| Z1 terminal conservation | SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact.finiteVolumeClosesSameOriginalSignedPorts | New source-written forwarding theorem; original terminal admission OPEN |
| Z2 bounded replenishment | SmithFilsingerSourceMaxwellBoundaryWeldExact.sourceCapTransfersToSameOriginalPort | Same selected independent natural cap; source data, replenishment, full storage return and positive net extraction OPEN |
| Z3 ordinary support vs metric response | AntigravitySameStateFourChannelDiscriminatorExact.signature | Existing 5-channel ordinary-force false metric responses; cannot infer altered free fall or metric from lifting |
| Z4 actual ordinary GR/background closure | AntigravityLaboratoryOrdinaryModelClosureWeldExact.TypedOrdinaryModelClosureWeld | Dependent original lab receipt; calibrated EM, RF, mechanical, thermal, source stress, test mass and GR prediction OPEN |
| Z5 superconducting coupling leaf | SuperconductingGravityCouplingResidualBidiExact.currentFirstOpenAlphaLeaf | Source observable is first evidence gap; no superconducting-to-gravity coupling coefficient inferred |
| Z6 EM/YM 369 orientation | OrientedBracketEMYMNS369Regression, RightHandRule369Exact | Original same signed orientation for force/torque/Poynting, not identical physical sources or observables; YM C3 seam remains gated |
| Z7 independent physical acceptance | Four-channel + TT experimental portfolio, Filsinger F10–F15, Amy consumer-bound lab source | Actual measured EM support vs true gravity discriminator and original source work/return, independent matched controls and replication OPEN |

**Status distinction:** 29/29 is a new exact local script and its Git blob is verified; previous 37/37 is an independent earlier synthetic source-shaped check. Both are not Agda kernel receipts, a Yang–Mills Clay gap, Filsinger environmental energy harvesting, superconducting gravity, or a new nonlocal field. Source attribution and Podkletnov/NASA/Hathaway/Tajmar original reports/nulls retained separately. The key experimental separation is Maxwell force/stability and energy transfer on the selected apparatus versus remote gravitational free-fall, metric-clock, inertial and TT signals; no one output is promoted as all others.

---

## NEW P0→P1 source-maxcut — YM/EM photon, formalised antigravity experiment portfolio and Filsinger (Y0–Y9)

**Critical correction:** The earlier P0/P1 division was lost. P0 is the **non-Abelian 4D Yang–Mills original Wilson/OS spectral-gap research**, while P1 is **physical antigravity/Eskridge and Filsinger receiver experiments**. The original **Abelian electromagnetic gauge restriction is an exact mathematical bridge**, *not* a Clay mass-gap proof, a massive Maxwell photon, a new gravity mechanism, or a calibration of any one apparatus. Source audit anchored on the actual master code, not on the phrase "mass gap is EM" alone. The E6/Higgs source's unbroken photon is particularly valuable precisely because it is a **null**, rather than a positive-mass, mode.

### Original source inventory — already formalised, do not redo

| Actual canonical owner | Established code-level content | Missing physical promotion |
| --- | --- | --- |
| `DASHI/Physics/Electromagnetism/U1AsSU2AbelianRestrictionExact.agda` and `U1ElectromagneticApplicationExact.agda` | **Constructive `embedU1Lie`, `u1EmbeddedLieBracketZero`**, canonical subgroup/torus; SI-typed potential, E, B, charge/current, constitutive-medium application socket | Abelian restriction does **not** prove the 4D non-Abelian OS gap or Maxwell observation; `maxwellLawReference`, `constitutiveMediumReference`, source current, real E/H calibration remain application-specific |
| `DASHI/Physics/Gravity/KKE6TrinificationDiagonalZThreeQuotientExact.agda` and `Docs/physics/KKE6GlobalHiggsChainZ6U3Original27Pareto20261027.md` | Source-conditional original first-Tits 27 / Chi33+E32+E21 Higgs stabilizer, **residual `(SU(3)×U(1)_EM)/Z3 ≅ U(3)`**; original E6 neutral Cartan mass-Gram rank **3/4**, surviving photon null direction and exact 27 charges | The E21 VEV, full anomaly-safe 5D quantum source, gauge action and physical spectrum are open. **A photon null is NOT a mass gap in the Maxwell sector** |
| `DASHI/Physics/YangMills/YMClayDirectSourceOSMassGapFrontierExact.agda` (P0), current YM PR [#1536](https://github.com/chboishabba/dashi_agda/pull/1536) | `DirectSourceOSMassGapInputs` and `directSourceOSBuildsPhysicalMassGap`: conditional same-reconstructed-Hamiltonian OS certificate from original Wilson family; currently advanced original R445/OS welds | Source real interacting continuum `E1`, uniform cutoff physical `D1`, positive spectral gap `D2`, nontriviality `N1` and group scope `G1` remain **OPEN**. A finite cavity/plasma/superconductor EM spectral threshold does not pay these |
| `AntigravityExperimentPortfolioExact.agda` | **FOUR original formal experiment-design alternatives** `weightOnlyExperiment`, `freeFallClockExperiment`, `matchedFourChannelExperiment`, `matchedFourChannelTTExperiment`; exact refinement proofs including metric vs nonmetric, cross-channel and TT distinctions | Designs/coverage do not produce measurements or a gravitational mechanism |
| `SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact.agda` | **FIVE** hypothesis worlds: source-only, constitutive-excess, geometry artifact, background artifact, null; original `sourceConstitutiveCollision` and `sourceVsConstitutiveSeparated` for joint source-normalised designed observation | Hypothesis-class separation by an abstract observer is NOT an actual result; must supply matched phase/source/geometry/external-probe data |
| `SuperconductingGravityExperimentalConstraintRegistryExact.agda` | Source-specific **Podkletnov–Nieminen 1992 reported** YBCO apparent-weight signal; NASA 1997–99 null and RF artifact; Hathaway–Cleveland–Bao 2003 null; Tajmar 2007–08 temperature-transition mismatch and theory upper bound. Each historical claim is independently typed and attributed | Reported claims are not independent replications. Null tests constrain their measured geometry rather than logically proving all proposed fields impossible |
| `AmyEskridgeAntigravityExperimentBindingExact.agda`, `AmyEskridgeAntigravityMeasurementObservationWeldExact.agda` | Separate consumer-bound **free-fall** and **remote test-mass** discriminators with explicit observation channels, attribution, calibration and analysis result requirements | Two distinct channels cannot be replaced by the same magnetic force or the same video demonstration |
| Draft Amy source aggregation [PR #1528](https://github.com/chboishabba/dashi_agda/pull/1528) | **86** video claim bindings; full **35-page HAL5** source/ **37-title DIA** inventory; original sources and corresponding evidence gaps, per owning PR audit | Author claims/document descriptions are not calibration, independent replication or direct gravitational field measurements |
| `AntigravityMaterialBidiCrossPollinationExact.agda`, `AntigravityClaimScopedExperimentalCutExact.agda`, `AntigravityFullyDerivedExperimentalCutExact.agda` | Six **different** gravity/weight/inertia/thrust/metric claims with distinct required discrimination; fully-derived/certified selected-apparatus receipts and source provenance conditions | The selected real calibrated `ClaimScopedCalibratedExperimentalCut` and physically observed positive effect are **not automatically inhabited** |
| `CMP119AntigravityTraceVsActiveStressFirewallExact.agda` and `CMP119AntigravitySameTOVStressGeodesicIndependenceExact.agda` | Exact (\mathrm{active}(T)=\mathrm{tr}(T)+2\rho), plus sourced rational fixtures **negative active stress with inward acceleration** and **positive active stress with outward acceleration** | Neither a negative stress trace nor a chosen EM stress label proves repulsive gravity; actual geometric solution/source tensor, geodesic and junction are distinct obligations |
| `SmithFilsingerSourceMaxwellBoundaryWeldExact.agda` + `SmithFilsingerMaxwellMaterialEnergyCutExact.agda` + F01–F16 roadmap | Original separate configuration/source family, causal flight, material source work and **two independent same-object field/material energy balances** whose shared port cancels; actual complete-cycle bound conditional on source inputs | The real device's Maxwell E/H/P, original mesh-to-field/terminal measurement, material dispersion, source-receiver return and sustained natural input **remain OPEN** |

**Cross-programme reuse committed, not speculative replacement:** `DASHI/Physics/Foundations/YMPhotonAntigravityFilsingerOriginalWeldExact.agda` is a new source-only **method comparison** consuming the original (U(1)\subset SU(2)) bracket-zero producer, four antigravity experiment portfolio and five-world discrimination, Amy distinct consumer channels, claim-scoped nonpromotion, and the **existing** Filsinger `fieldMaterialCombinedWork` proof on *one selected port and boundary*. It **does not** turn the experiment comparison into same apparatus, does not create Set-valued dummy empirical witnesses, and never upgrades a conditional original physical Maxwell or OS certificate to a measurement.

### Precise P0→P1 observables

**Electromagnetic (ordinary comparator):** (F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu) after Cartan commutators vanish, Maxwell/MHD/PNP material response, field stress, boundary momentum flow, flux and source currents, plus the very real possibility of **ordinary magnetic/diamagnetic/electrostatic lifting**. A static force can support a load with (\mathbf F\cdot\mathbf v=0) at zero velocity while energy is still consumed in apparatus maintenance, levitation stability, cryogenics, losses or changing the state. Do not label this antigravity.

**Spectral:** ordinary free Maxwell (\omega=c|k|) has a massless long-wavelength photon; a finite cavity lowest (\omega\sim c\pi/L) approaches zero as (L\to\infty). A screened material/plasma response may have an **effective medium excitation scale** without establishing the 4D pure interacting non-Abelian vacuum spectral gap of (H_{OS}). E6 rank-3/4 selected photon **null** leaves an unbroken EM direction; it does not imply a positive physical photon mass.

**Gravitational:** source-derived EM stress may gravitate conventionally in GR. But a gravity modification claim needs an **independent external free-fall / remote test-mass / metric-clock / TT** discriminator whose same-apparatus ordinary EM, thermal, force-reaction, vibration, geometry and source variation are calibrated. The original CMP119 same-TOV source/acceleration counterexamples prevent a false inference from sign of trace or active stress.

**Filsinger:** use the original model of **source-dependent coupling and external replenishment** with real E/H port mapping, retarded dispersive material and separate work on modulation. Source-only and constitutive-excess can be phase-correlated alike; test calibrated natural source voltage/current/admittance under loaded matched controls. A high load/control ratio is not proof of ambient replenishment; repeat the complete cycle with all stores restored.

### New Y0–Y9 source-first executable maxcut

| Gate | Theorem or experiment target | Status |
| --- | --- | --- |
| **Y0** | `selectedU1EmbeddedYangMillsBracketIsZero`, `ordinaryMaxwellApplicationNeedsSourceValidation` | Reuses existing exact Agda owner; **source-written**, kernel open |
| **Y1** | E6 original27 Chi33/E32/E21 photon null / charge test as *distinct original source* | Existing source-conditional source math; no new E6 source on #1537; physical VEV/effective fields open |
| **Y2** | P0 `DirectSourceOSMassGapInputs` from YM #1536 on same original interacting Wilson E1 and physical H | **OPEN** for Clay proof; don't treat finite Maxwell/material gap as proof |
| **Y3** | `originalAntigravityPortfolioCoverage`, `fourChannelExperimentDiscriminatesMetricVsNonmetric`, `weightOnlyDoesNotDiscriminateMetric` | Four original designs **welded**; source-written Agda, no new experimental execution |
| **Y4** | `sameCoarseSignalInTwoExistingGravityWorlds`, `originalJointDiscriminatorSeparatesModelWorlds` | Reuses existing abstract source-only/constitutive distinction, **not physical evidence** |
| **Y5** | `amyFreeFallAndRemoteMassDemandDifferentChannels`, `claimRequiresOriginalChannel`, `claimScopedCalibrationDoesNotPromoteByNaming` | Existing consumer scoped exact experimental binding **welded** |
| **Y6** | `OriginalFilsingerU1FieldMethodComparison`, `originalFilsingerConditionalSameSourceWork` | Reuses ORIGINAL same-boundary source/material work equation, no fabricated new physical ports; need Maxwell E/H/mesh-to-port and measured natural source |
| **Y7** | `CrossExperimentYMFieldMethodComparison` | Cross-project **methods only**, not same model/hardware; require source provenance for any new physical identification |
| **Y8** | Original same-state EM-force/non-gravity and CMP119 source-normalized gravity residual discriminators under matched interventions | **OPEN empirical**, original owner experiments already designed. Determine whether force is fully ordinary EM, source/stress altered without gravity change, or independently gravitational |
| **Y9** | Real P0/P1 integrated mass-gap/EM-response/antigravity/Filsinger claim cut | **OPEN**: P0 original analytic theorem, P1 Filsinger original field/work and claim-scoped gravity observation need their independent evidence; no shortcut by sharing names, 27/54 or gauge symbols |

**Independent local exact symbolic fixture:** the local SymPy 1.14 audit of **37/37** cases checked U1 Cartan commuting versus SU2 noncommutativity; massless Maxwell vs finite-cavity mode and massive mode; four antigravity design coverages; five abstract world signatures; source-free nonuniform B with a calibrated *illustrative* diamagnetic force; combined Filsinger field/material energy conservation with internal-port cancellation, and fixed-source Thevenin matching. The associated **committed** `scripts/check_ym_em_antigravity_filsinger_original_sympy.py` follows the same source-shaped tests; **do not claim the exact committed Python bytes were executed** unless a separate local exact-head replay succeeds. Neither this check nor a conditional Agda source is a positive experimental/gravity/YM-OS certificate.

### Recommended order after this weld

1. Inspect exact-head source and Agda typecheck of the focused #1537 root; **no CI**, local SymPy or pinned local Agda only. Fix actual owner projections before claiming compiler acceptance.
2. Advance original **Filsinger F10–F15** using the existing retarded Maxwell/ADE face/field machinery: construct the measured *same-apparatus* signed E/H field→port Poynting identification and source-connected controller counterfactual.
3. Feed that field/stress prediction into the ALREADY FORMALISED **four antigravity experiments**, plus Amy free-fall and remote channels, as an **ordinary-EM rival**; preserve the original Podkletnov/NASA/Hathaway/Tajmar evidence statuses.
4. P0 YM remains **original Wilson/OS continuum gap** with its own E1/D2/N1/G1 analytic proof track, potentially informative for field operators but **not an inferred gravity effect or material photon mass**. Close P0 and P1 independently rather than conditioning either physical experiment on a completed Clay theorem.

---

## Corrected TOP PRIORITY — physical endpoints first, organizational field/attractor control (R0–R8)

**21 Nov 2026 source-based reframing.** The previous Monster/BH4 weld-forward is useful infrastructure, but **it must not displace the two decisive physical programmes: Filsinger source-access and antigravity/levitation**. Sheldrake's transcript contrasts the energy of a falling meteor/Galton ball with a static organizing gravitational/magnetic field and says seventeenth-century efficient/material causation displaced formal/final explanations (00:01–01:40, 02:44–03:43, 05:17–06:29). Treat this as *Sheldrake's attributed philosophical/causal thesis*, not evidence of an extra nonlocal force. The rigorous physical question is: **can the control pattern change basins, constraints, boundary access or coupling to an independently available reservoir at a cost small relative to the resulting response?**

**This changes the order of investigation**: field topology / control authority / accessible reservoir / endpoint discriminator FIRST, and full energy+momentum conservation as the **required final admissibility constraint and counterexample filter**, not the only optimization target. Conservation is necessary and not sufficient to predict which effect can be engineered. Nor does an organizing field become a source of unconstrained new energy.

### Three endpoints which should no longer be flattened into a single watt ratio

| Endpoint | Existing original Agda producers | Mathematically distinguishable phenomenon | Decisive source requirement |
| --- | --- | --- | --- |
| **Levin: target-form attractor selection** | `GoalErrorDescentControllerExact`, `FiniteMorphogeneticBasinControlExact`, `BiologicalAllNeighbourTissueDynamicsExact`, `CellStateAttractor`, `Levin.TravelingFieldControl` | Change attractor basin, future-safe phenotype and local control geometry; then biological processes consume **existing cellular/metabolic resources** after the pulse. Static input energy is not a sufficient descriptor of the eventual form. | Original tissue Vmem/junction/assay/history mapping, intervention time/course, altered basin and recovery after pulse, independent phenotype target. BH4 is a potential downstream state readout, **not a prerequisite for Filsinger or gravity**. |
| **Filsinger: externally powered source access** | `SmithFilsingerHybridRegimeStudyBidiExact`, `SmithFilsingerSourceMaxwellBoundaryWeldExact`, `SmithFilsingerMaxwellMaterialEnergyCutExact`, `SmithFilsingerSpatialPortChainExact`, `SmithFilsingerSunEarthCoupledSourceExact` and 16 Nov F01–F16 roadmap | Controller alters admittance, phase/timing, field boundary, nonlinearity and source-connected path. Natural/solar/ionosphere/atmosphere **gradient or flux** can be much larger than control; the resulting output is **reallocated source work**, not work arising from geometry alone. The existing distributed-source series-vs-shunt comparison is key: +110.31% *load work* for the selected series path, -2.25% for the selected shunt, both still **negative net after modeled pump costs and no state return**. | Real original apparatus wiring; full Maxwell/memory operator; selected *source-connected* path vs shunt; retarded phase measured at receiver; same external forcing and time-aligned source/load/control work, positive useful output under sustained replenishment. Existing F10–F16 remain OPEN. |
| **Antigravity/Eskridge: actual force versus gravity response** | `AntigravityMaterialBidiCrossPollinationExact` six typed claims, `AntigravityClaimScopedExperimentalCutExact`, `AntigravityMatchedControlExperimentDonorMaxCutExact`, `CMP119AntigravityTraceVsActiveStressFirewallExact` | A strong **static force** can balance weight with **zero mechanical power at zero velocity**. Stable levitation, changed apparent weight, altered free-fall acceleration, independent repulsion on distant test masses and genuine metric/clock response are **different observables**. A field may hold a load without performing continuous mechanical work; it does not imply a modified gravitational law or zero costs for maintaining the apparatus. | For levitation/weight reduction: calibrated force, magnetic/EM/electrostatic/thermal/acoustic/vibration/reaction-force control and stability. For **gravity-channel** claim: shielded independent free-fall/test-mass or metric-clock comparison, full tensor `T_mu nu`, gravitational residual, external source and replication. Negative trace is NOT negative active stress. |

### Explicit three-layer mathematical model (no new ontology)

Use source-specific existing carriers, but keep three different observables:

1. **Organizing map / coupling:** `x_{t+1}=F_{u_t,eta_t}(x_t)` or `dot x = F(x;u,eta)`, `A(u)` (admissible adjacency), `B_u` (basin), `O(x)` (measured output), target `T`. `u` can select response or reconfigure a constraint, **without itself being the reservoir**.
2. **Accessible reservoir and transduction:** `J_source(x,eta,u)`, causal boundary propagator and directional load `P_load(x,eta,u)`. Source response/backaction is allowed to change with `u`; compare with **identical exogenous forcing**, not an artificially identical realized current. A small control signal can yield a larger **load response** by using a much larger source, in classical externally powered amplification. Use source-owner `SunEarth`, `FieldToPort`, dynamic `MaxwellADE` and Filsinger exact signed source/return.
3. **Conservation / physical scope:** after identifying the physical object and boundary, require `Delta storage + load + heat + outgoing = natural in + drive in + modulation in` with no double-counting of nested reservoirs, and appropriate reaction momentum/force/metric tests. This law rules out energy creation but **does not** solve `F`, identify `A(u)`, locate an attractor, or infer the direction of `J_source`.

The exact illustrative potential `U(x;u)=((x²-1)²)/4-u*x` has two stable `±1` attractors at `u=0` and an unstable separator at `x=0`. A sufficiently large positive control `u=1/2` eliminates the left well, but the force/pulse duration and actual switching still need a specified trajectory. Under fixed `u`, `dU/dt=-(partial_x U)²`; under `u(t)`, `dU/dt=-(partial_x U)² - x dot u`. **The topology/basin change and the modulation work are separate quantities.**

In the source-connected Thevenin comparison `P(G)=V_oc² G/(1+R_s G)²`, the same source `V_oc=R_s=1` yields `P(1/8)=8/81` versus `P(1)=1/4`: a **81/32-fold delivery increase**, bounded by the already-present source's matching ceiling; no controller energy budget can be inferred from `G` alone. This is not Filsinger measurement. For a conservative gravitational `U=m g h`, force is `-m g` but `P_mechanical=F v=0` when stationary; energy changes on motion, changing field/material and maintenance have their own costs. This is not an antigravity mechanism.

**Committed exact local preflight** `scripts/check_formative_ambient_reservoir_attractor_gravity_sympy.py` at Git blob `270a45a3e7dadc421e9bb4a48a2e698568787e6f`: **22/22 PASS** in local SymPy, matched to exact committed blob. These are *new synthetic algebraic fixtures*, not evidence of Filsinger external power, Levin regeneration in an organism, a gravity anomaly or a new Sheldrake mechanism. The original Filsinger 16 Nov series-vs-shunt result cited above is from existing repository research, not rerun in this cut.

### Reverse-solving gates and named remaining lemmas (the new active priorities)

| Gate | Dependency-ordered deliverable | Status / source-paid remainder |
| --- | --- | --- |
| **R0 `fieldOrganisesWithoutFuelConflation`** | Static force / holding power, standing field and Galton distribution vs field work; distinguish stored potential, environmental flux, field source and constraint | Finite force/attractor examples PASS locally; original Galton magnetic force/material path not calibrated |
| **R1 `controlChangesBasinOrAdmissibleOperator`** | In native geometry, show a **source-owned** control changes `A(u)`, basin partition or target reachability under a physically meaningful field update; use Levin `GoalErrorDescent`, original tissue 54-bond transport and field perturbation | Finite proof owners exist; an actual measured `Vmem`/current/phenotype source-to-operator map remains OPEN |
| **R2 `originalFilsingerSourceConnectedSwitching`** | One source-identified physical apparatus distinguishes **series-connected receiving conduit vs dissipative shunt**, with causal delay, nonlinear memory, boundary phase and matched control | Existing synthetic contrast supports topology importance; original real source/receiver/return Maxwell geometry F10/F13/physical S0–R3 OPEN |
| **R3 `ambientReservoirExergyAndAccess`** | Identify separately solar photon, solar wind / ionosphere, storm-atmosphere and natural Thevenin source; quantify **accessible load power**, conductance limits, replenishment and response to controller **without counting the same upstream energy twice** | `SmithFilsingerSunEarthCoupledSource` already provides bookkeeping skeleton and distinct source regimes; physical matched source-access operator and original measured source still OPEN |
| **R4 `fieldControlCanHoldWithoutMechanicalPower`** | Direct static-force vs stationary-work split for the exact apparatus with stability and loss; compare magnetic/diamagnetic/superconducting support to true gravity change | Algebraic example PASS, six original gravity claims already separated; real apparatus calibrated force and independent EM/motion controls OPEN |
| **R5 `independentGravityChannelAfterOrdinaryForceCut`** | If user specifically claims gravity-channel alteration: independent test mass/free fall/clock/tensor and metric readout, same-source stress energy plus force/momentum closure | Existing claim-scoped strong calibration and CMP119 active-stress firewall; no independent anomalous gravitational field receipt |
| **R6 `sameReservoirLargeResponseSmallControl`** | Measure `delta load` and `delta ambient access` *versus* controller work and resulting basin/coupling, under identical exogenous forcing; compare source-connected, shunt, pump-off and nulls | Needed to demonstrate actual controller leverage. Energy bookkeeping **last admissibility step**; not a premise that controller must itself supply output |
| **R7 `nonlocalSimilarityBeyondLocalField`** | Only after local field/ordinary reservoir/geometry mechanisms are tested: independent Sheldrake cross-population, time-lagged similar-history intervention with no ordinary information/energy path | Unverified hypothesis; no existing Monster order27, 54 count or Levin bioelectric result promotes this |
| **R8 `exactKernelAndOriginalEvidence`** | Pin original producer/import head, local Agda/solver acceptance and real measurements; unresolved `Set` inhabitants are not empirical proof | Agda kernel OPEN; R1–R7 original physical sources OPEN |

**Avoid a new catchall formal field type.** The already existing 3D ternary / 54 native bonds / residual cube / Monster nonisometry / BH4 reaction-PNP / Sun-Earth Maxwell / source-qualified Filsinger / antigravity six-claim owners have the relevant mathematical interfaces. Change the consumer and the experiment design, not the source ontology.

**Interpretation priority:** a device can be a *gate*, a *boundary-condition programmer*, a *phase/mode matcher*, a *force-support system*, a *basin shifter* or a *source harvester*. These are related by control and geometry, but are NOT interchangeable physical claims. The source of useful output remains physical; the controller need not itself be that source.

---

## Weld-forward correction — geometry is the already-existing organizer

**Priority correction 21 November:** the original 369 geometry is **not** a visualization added after the physical programme. It is a first-class source geometry with exact adjacency, boundaries, shared observations and spatial futures; the correct route is **source-native geometry → permitted local field interactions → future-safe organization/attractors → same-original PNP physical work → any cross-domain device/force consumer**. A new abstract "formative field" constructor would DUPLICATE these producers, so PR #1537 now commits only an adapter over them.

### Actual owners audited on master (not nominal equivalents)

- `Base369Ternary27HypervoxelFabricGeometryExact`: signed balanced-trit `Ternary27Point`, 27 locations, `HypervoxelAdjacent` witness (no -1 to +1 jump), **six outer boundary faces**, three coordinate axes; 9-coordinate triple-cube hyperfabric retains separate 27 factors rather than treating them as one physical 3D point.
- `BiologicalFullCubeIncidenceExact`: **54** canonical positive nearest-neighbour bonds, **36** elementary squares, **two equal square endpoints**, `bondIsNearestNeighbour`, `allBondJunctionReadingsSurviveProjection`. A positive bond is a native oriented edge, not a second reverse edge or an electromagnetic Cayley face by definition.
- `BiologicalAllNeighbourTissueDynamicsExact`: `fullFineStep` and `fullCoarseStep` read **all 54 original bonds from the previous field**; `fullAgreementPreserved`, `canonicalAllNeighboursFutureSafe`, `allNeighbourSignalIdempotentAt`, `responseAgreement`. Its selected Boolean signal update and one-step basin are **finite fixtures**.
- `BiologicalSourcePhysicalTissueSimulationExact`: already owns `SourcePhysicalTissueSimulation`, `physicalPNPStepCommutes`, `physicalOneStep`, `physicalPNPAndTissueSameHistory`, `physicalHistoryProjectsToAll54Bonds`. The physical source must supply this record; it has **not** been instantiated for source-paid BH4 or Filsinger hardware.
- `SmithFilsingerIndexedCayleyFaceWeldExact`: `IndexedCayleyFace`, `MeshSelectedCayleyFace`, source- and target-ID preservation, actual original indexed-mesh face-membership and conditional source-cone equations. Numeric same-face ID is NOT a proven electromagnetic field-to-face projection. The endpoint map from biology's `PositiveBond` is an explicit unfilled witness in the new adapter, never an automatic physical identification.
- `FiniteElectrodiffusiveMovingBoundaryExact`: separate `transportConservesAmount` plus `ActiveEnergyStep` bookkeeping; conservation in a two-cell surrogate is **not** an original BH4 29x12 reaction/PNP or an actual magnetic-field work measurement.
- [Indexed cube H05 PR #1291](https://github.com/chboishabba/dashi_agda/pull/1291) is an **open, independently indexed** eight-vertex / 12-edge / six-square-face **commuting-cube** programme; its *six square faces* are distinct from the native 3x3x3 carrier's *six exterior boundary faces* and its 36 *unit* square plaquettes. H05 and its h/t/k/j/v indices are optional proof donors, NOT evidence that six physically different faces are interchangeable; no branch-only module is imported.
- [OCT369 PR #1534](https://github.com/chboishabba/dashi_agda/pull/1534) includes explicit magnetic-octupole/levitation/Schumann and Filsinger hypothesis discrimination; **open** methods donor, not source-certified gravity or energy transfer.

### Committed W0–W9 maximum-cut deliverable/lemma ledger

| Weld | Concrete result / exact remaining lemma | Source and implementation status | What is still missing |
| --- | --- | --- | --- |
| **W0** native geometry | `originalTernarySites`, `originalPositiveBonds`, `originalElementarySquares`, `originalSixOuterFaces`, `nativeBondReallyAdjacent`, `nativePlaquetteClosesAtOriginalCorner` | **Source-written in #1537**, direct re-exports of `Cube`/`Grid` master theorems; 27/54/36/6 verified in local exact regression | Agda focused kernel check, any continuum geometric interpretation |
| **W1** full organizing neighbourhood | `everyNativeBondFeedsSelectedResponse` | **Source-written**, definitional identity with original 54-bond `fineListIncoming` | A measured constitutive mechanism translating currents/voltages to Boolean signal |
| **W2** same physical history | `samePhysicalPNPAndTissueHistory` | **Source-written**, reuses `physicalPNPAndTissueSameHistory` (not a new existence proof) | **Instantiate** `SourcePhysicalTissueSimulation.physicalOneStep` and `physicalPNPStepCommutes` on one source-paid physical model |
| **W3** all-bond BIDI readout | `allOriginalBondPatternsCommuteAfterPhysicalHistory` | **New composition**, applies existing pointwise tissue agreement to both endpoints of **every original** `PositiveBond` after **any intervention history** | W2 original physical model and kernel check; absolute field/port calibration |
| **W4** organizing response BIDI | `originalOrganizingResponseCommutesAfterPhysicalHistory` | **New composition**, uses source-owned `responseAgreement` for every original voxel/time history | Identifying phenotype/assay readouts with actual measured physical states |
| **W5** selected basin | `selectedNativeSignalBasinAfterPhysicalHistory` | **Source-written**, reuses `allNeighbourSignalIdempotentAt` for a Boolean tissue readout of an arbitrary physical history | Do **not** infer physical PNP step itself is idempotent, or that a real organism has such an attractor |
| **W6** Filsinger mesh ID guard | `NativeBondToSelectedNumericalFace`, `nativeBondCayleyPrimitiveSourceID`, `nativeBondCayleyPrimitiveTargetID` | **Source-written conditional adapter**; must provide actual original `MeshSelectedCayleyFace`, nodeID map and two matching proofs | **W6a [OPEN]** `nativeBondToPhysicalEHFaceProjection`: actual E/H/polarization/normal, units and measured same-device face/edge physics; identity of numerical IDs alone insufficient |
| **W7** conservation boundary | `originalConservativeTransportStillRequiresItsOwnCarrier` | Direct reuse of `transportConservesAmount`; no work inferred from organization | **W7a [OPEN]** `samePhysicalGeometryAndSignedEnergyLedger`: source, controller, storage, boundary flux, radiation, return, chemical/electrical work on the SAME original physical state |
| **W8** BH4 source payment | Reuse #1454 `sameSourcePhysicalReactionTransportStep`, `physicalBH4StepCommutes`, `physicalTissueOneStepRefinement` | **OPEN**, do not restate them as a synthetic implementation. Source-paid QDPR/TH/PCD/DBH plus 29x12 chemistry and 54-bond PNP are separate real producer obligations | Actual 29x12 Rhea identity, kinetics, electrode/exchange, original compartment and selected observed tissue history |
| **W9** proof/index transport | Optional #1291 `GovernedIndexedResidualCubeExact` six-face coherence and time/frame/consumer residual, #1534 octupole/Schumann discriminator | **OPEN branches**, no new imports in this PR | Source-identified map from H05 h/t/k/j/v fibers to specific 54-bond organism/device histories; tested noncommuting or nonlocal counterexample |

**Accepted local source-equivalent regression:** `scripts/check_formative_native_geometry_weld_forward_sympy.py` ran on the **exact committed Python Git blob** `a7b4bf42dcc97fe28f842e5eb085c8a76e351faf`, which matches the locally executed file's Git blob. **22/22 PASS** using SymPy 1.14.0: 27/54/36 topology, six 9-point exterior faces, chain identity `∂1∂2=0`, incidence rank 26/nullity 28, plaquette span rank 28, 216 trace prefixes across 27 selected 8-action traces with all 27 and 54 comparisons, finite signal idempotence, memory counterexample, orientation guard and rational internal-flux conservation. These are **finite/synthetic** checks, not an Agda proof run and not measurements of natural physical sources. Existing two earlier scripts previously recorded **37/37** separately; the current new local run adds 22, **without re-running the older scripts in this turn**. Never call this 59/59 a single exact-head aggregate acceptance.

**Kernel still OPEN** (`agda` is not installed in the available local environment). Review qualified Cayley record projections and complete focused root imports on an Agda-enabled host before marking any W0–W7 theorem checked.

**Shortest remaining physical cut:** W2 actual `physicalOneStep` and `physicalPNPStepCommutes` on the same source → W3/W4 actual observed tissue/BH4 current response → W7 signed real work → W6a actual E/H face projection for Filsinger if the same-system crosswalk is warranted. Do not invert that dependency, create an independent geometry, or turn an illustrative field/energy analogy into physical proof.

---


## 21 November continuation — Monster original 27/54 and BH4 same-state paid-energy weld (W10–W16)

**This update supersedes the earlier suggestion to write a new generic "form" or "field" ontology.** Source-weld forward instead: original cube incidence → original physical PNP/tissue source → original BH4 same-source energy owner → accurately scoped Monster representation/locality comparison → Filsinger actual E/H face, as separately certified. A matching **integer is neither the same object nor an intertwiner**.

### Monster source audit (actual master owners, no unmerged import)

| Native owner | Exact source result | Interpretation, without laundering |
| --- | --- | --- |
| `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`, `DASHI/Biology/Physical/BiologicalFullCubeIncidenceExact.agda` | `Ternary27Point = {-1,0,+1}³`; **27** sites, **54** nearest-neighbour positive bonds, **36** elementary square plaquettes, six external cube faces | Actual physical-style *combinatorial* adjacency. Not a 27-cycle, modular `Z/27` translation or automatically an electromagnetic device |
| `DASHI/Moonshine/Monster27VOAOnsiteCube369BridgeExact.agda` | `Monster27VOAOnCubeSource` conditionally supplies a literal Monster element `g27`, selected same-source 3B element with `g27^9 = 3B`, the actual grade-two `196883` action at each cube site, and a `54` source trace; onsite action commutes with pointwise site relabelling | An **uninhabited source contract here**, not constructed Monster 27-action on the biological bonds. Site relabelling commutation does **not** prove preservation of the 54-bond Hamiltonian |
| `DASHI/Moonshine/Monster3BCyclicFourierDyadicBridgeExact.agda`, `Monster3BRegularC3BulkResidualFiftyThreeBidiExact.agda` | `W|C3 = 53*1 + 65610*Reg(C3)`; exact **196830 + 53 = 196883**, regular character split, selected residual 53 | Character arithmetic/phase multiplicities, **literal same-action submodule and Albert recognition remain open** |
| `DASHI/Moonshine/Monster196884FibreInterferenceExact.agda` | Exact **196830 + 54 = 196884**; coarse term **54** matches selected weight-two 3B trace numerically | Numerical compatibility; *does not construct* representation isomorphism or identify 54 trace with 54 spatial bond basis |
| `DASHI/Moonshine/MonsterReducedNonaryBoundaryExact.agda`, `Base369MonsterFiftyFourFiveModeResidualActionBidiExact.agda` | **54=6×9=5×9+9**, reduced **53=5×9+8**, distinguished pointed sector | Candidate 54/53 *mode-state carrier*, NOT the 54 native bonds or a built Monster module |
| `DASHI/Foundations/Base369Completion54SituatedTriadBridgeExact.agda` | Another **54=(2×3)×9** local completion fibre | Distinct semantics again. Finite count equality does not identify it with graph edges or Monster subrepresentation |
| `DASHI/Moonshine/JInvariant369Cube27CuspCodecNonIsometryExact.agda` and `JInvariant369Cube27ModularLocalityObstructionExact.agda` | Cube digits ↔ cyclic residue chart bijective but not adjacency preserving; `+1` wraps +++ to ---; selected modular `M(x,y,z)=(x+y,x−y,z) mod3` does **not** preserve all native edges | Existing formal obstruction is stronger than a chart/cardinality comparison. Real organization depends on what *local operator* the intervention actually preserves |

### New exact W10–W16 deliverables and remaining proofs

| Gate | Exact code target / source owner | State and remaining payment |
| --- | --- | --- |
| **W10** distinct 54 roles | New `Monster27Native54OrganizingFieldWeldExact.nativePositiveBondCountIs54`, `monsterWeightTwoCoarseSectorIs54`, `monsterReducedCandidateResidualIs53`, `monsterExact3BBulkIs196830`, `monsterFullWeightTwo196884`, plus typed `FiftyFourRole` discriminator | **Source-written** as reuses of actual master theorems; no identification of carrier objects |
| **W11** actual selected 3B trace matches COUNT | `sameCountUnderActuallySelected3BSource` conditionally proves source-certified grade-two trace equals `countList allPositiveBonds` | **Source-written**; `Monster27VOAOnCubeSource` must supply the actual `g27`, 3B source action and trace. NO canonical inhabitant in this PR; mere numeric coincidence does not produce a bond intertwiner |
| **W12** modular site-to-edge no-go | `selectedModularMapCannotPreserveAll54PositiveBonds` takes a purported map of *every actual positive bond* to another native positive bond with both transformed endpoints and derives contradiction via the original `+x` edge; `cyclicCarryNotNearestNeighbour` reuses residue-corner obstruction | **New theorem source-written**, Agda kernel OPEN. **Do not** conflate this selected modular map with the actual Monster `g27` action: the two must be linked by a separately supplied source/action identification |
| **W13** onsite Monster vs biological field | `JointOriginalTissueAndMonsterWave`, `originalBondPatternUnaffectedByPureMonsterOnsite` | **Source-written product/canonical action**. Pure onsite action changes the wave coordinate only; identical tissue readout by construction. *Actual cross-system interaction or morphogenetic influence is not derived*. **W13a [OPEN]:** `actualMonsterSourceIntertwinesOriginalBondTransfer` requires real 27-site Monster action, native edge-support preservation (or separately priced nonlocal edges), observable/energy transport and source-data |
| **W14** BH4 energy already present | Existing `BH4PNPSamePhysicalHistoryBridgeExact.SameSourceBH4PNPModel`, `BH4PNPSameSourcePaidEnergyExact.SameSourcePaidEnergyModel`, `allSameSourceBH4PNPRouteAndPaidEnergy` | Existing **conditional** same-state chemistry/PNP/route/**ordered-energy** proof. Its `exactPhysicalEnergyStep` and `physicalResidualAndExteriorWorkPaid` are genuine source inputs, not constructed measured kinetics; **do not create another independent energy ledger** |
| **W15** strongest BH4 → native 54-bond state weld | New `BH4NativeTissueSamePaidHistoryWeldExact.BH4NativeTissueReadoutWeld`, `toExistingTissuePhysicalSimulation`, `theTwoPhysicalRunsAreTheSame`, `allOriginalBH4PNPTissueGeometryAndPaidEnergy`, `everyOriginalBondReadoutAtSameBH4History`. One original `BH4.PhysicalState (Paid.source M)`; one original PNP receipt, specimen and energy preorder; native bond readout after *same* selected history | **Source-written composition**; Agda kernel OPEN. **W15a [OPEN]** original 29×12 Rhea/kinetic certificate and `SameSourcePaidEnergyModel` actual physical inhabitant; **W15b [OPEN]** source-specific `originalTissueReadout` and `physicalTissueOneStep`; **W15c [OPEN]** justified mapping from the five `Bio.Intervention` actions to BH4's two Bool challenges. Mapping is NOT injective and cannot silently assert five experimentally distinct controls; empirical original readout/protocol still missing |
| **W16** full physical/Monster geometry weld | `Monster3B54TraceToNative54EdgeActionBidi` / `sourcePaidBH4TissueEHHistoricalIntertwining` **PROPOSED ONLY** | Need an actual same-object Monster representation-to-spatial-bond action intertwiner (unlikely from current data), a measured physical field/permitted local transport and a source-specific analogue; no Sheldrake nonlocality or antigravity promotion. When W12 no-go applies, report impossibility for that map rather than adding 36 fictional edges to force equality |

### Locally executed exact negative controls — no Agda or CI

Committed `scripts/check_monster_native_27_54_organizing_sympy.py` **Git blob `65b40e70a0fdf788ad41d92890f2e4c970f8c05e` is byte-for-byte the executed local script**. **27/27 PASS** with SymPy 1.14: literal 27-site/54-bond degree stratification 8/12/6/1; original 3B W/V arithmetic 53/54 residual versus trace; candidate 6×9 completion; exact modular bond image intersection **18**, union **90**, symmetric difference **72**; original native Laplacian `tr(L)=108`, `rank([L,P_M])=24`, squared commutator Frobenius norm **168**; 48 signed coordinate permutation automorphisms; explicitly cyclic +++/--- nonadjacency.

**This finite test does not establish the whole cube automorphism group is exactly 48 merely by constructing 48 actions**; the separate older source disambiguation document gives the upper-bound argument by unique graph signatures. Nor does the 27/54 count mean the Monster 54 trace acts on the 54 native bonds. **Kernel receipt remains OPEN** because the available local environment does not have Agda. Existing 19 + 18 + 22 test receipts come from earlier work; only 27 new exact-head tests executed freshly for this extension. No compounded same-head aggregate is claimed.

### Critical ordering, amended

1. **Do not start with a new physical field or Monster basis.** Finish exact-head Agda typechecking of W0–W15, repair direct old-owner imports as required. Inspect any existing source-specific original 29×12 evidence before inventing one.
2. Use W15 with real `SameSourcePaidEnergyModel` (including original paid energy and source rates) plus `BH4NativeTissueReadoutWeld.physicalTissueOneStep` on the same actual organism/device, with a genuine action-protocol mapping. Then W3/W4 native 54-bond readouts are automatically transportable for selected histories.
3. Use W12 as a **locality discriminator**: if the selected Monster/modular action doesn't preserve native edges, either it acts only on an internal fibre, or new nonlocal physical interactions require separate original evidence, energy and timing. Never conflate `C3` regular representation with the finite spatial graph.
4. Only when an original Maxwell/geometry source supplies E/H face projection into Filsinger and signed energy/momentum work may those source-receiver claims be compared. Antigravity/Eskridge remains a claim-scoped independent gravitational residual gate.
5. Last, Sheldrake similarity-history nonlocal candidate only if independent controlled populations supply distinguishing interventions, original data, no communication/local field confounds and replication.

---

## 0. Exact Sheldrake reading: the 17th-century challenge

**Direct transcript, not an independently verified scientific source** (`Rupert Sheldrake Explains Morphic Resonance (With a Galton Board).txt` supplied by the user):

| Timestamp | Original speaker's claim | Typed research interpretation / limit |
| --- | --- | --- |
| 00:01–00:56 | Faraday's fields; a meteor falls in Earth's field; a fridge magnet holds paper while the field is not repeatedly consumed | Distinguish passive/static configuration from potential-energy change, force and energy transfer; neither establishes a novel field |
| 00:56–01:40 | Mechanistic 17th-century causation emphasizes energetic pushing/pulling; fields are **formative** rather than an energetic fuel | Source-attributed philosophical position. Modern Maxwell/GR/continuum field theories include energetic fields; “form” and work are not mutually exclusive |
| 01:50–02:43 | Aristotle's **material / efficient / formal / final** causes, illustrated with sculptor, marble, chisel, design and purpose | Four *audit questions*; do not pretend that philosophical formal/final causes have been measured as independent force sectors |
| 02:44–03:43 | 17th-century mechanistic revolution allegedly discarded formal/final causation; the morphogenesis puzzle motivates Sheldrake and specifically **Michael Levin** | The claimed inadequacy of mechanistic accounts is Sheldrake's argument, not an established no-go theorem. Bioelectric morphogenetic constraints can be modeled by physical PDEs, control policies, attractors and energy-consuming tissue dynamics |
| 05:17–06:29 | Magnets skew the steel Galton-board outcomes without visibly losing their magnetization | Local magnetism changes forces and impact paths. A static conservative component can be nondepleting over a cycle while the whole rig still pays gravity, boundary manipulation, impact/friction and stored-field energy |
| 06:31–08:45 | Stronger speculation: hidden fields bias quantum/classical probabilities and choice, instead of merely pushing | A **different physical hypothesis** from Maxwell or Levin. A changed histogram is not a causal mechanism identifier |
| 19:55–20:49 | Similarity-mediated transmission **directly across time/space**, not a central memory server | Separate unverified source-history coordinate; don't identify local developmental memory or Schumann coupling with this |
| 21:39–22:51 | Sheldrake emphasizes need for convincing empirical evidence and compares Faraday's initial observational field framing with later theories | Mathematical permissibility is not detection. Independent evidence, calibration, negative controls and replication remain required |

**Four non-identical research questions:** (1) *material carrier* — what physically holds charge, voltage, magnetic or chemical state? (2) *efficient causal work* — what force/flux/source/entropy exchanges occur? (3) *formal pattern* — what spatial constraint, boundary, attractor, kernel or probability law shapes possible futures? (4) *target/goal* — what intervention endpoint is specified by the observer or adaptive biological control? Neither a target nor a pattern creates an independent physical power port.

## 1. Source owners, no branch-only theorem laundering

| Priority | Canonical on `master`, already inspected | Unmerged donor and import rule |
| --- | --- | --- |
| Field conservation | `SameObjectConservationLedgerExact`, `FieldGeometryMatterConsumersExact` | [#1163](https://github.com/chboishabba/dashi_agda/pull/1163) OPEN: compare methods, don't require its branch state |
| Filsinger | `SmithFilsingerTimeIndexedTransferExact`, `SmithFilsingerSunEarthCoupledSourceExact`, `SmithFilsingerTimedSpatialPortChainExact` | [#1521](https://github.com/chboishabba/dashi_agda/pull/1521), [#1524](https://github.com/chboishabba/dashi_agda/pull/1524) OPEN: source-qualified method donors only; already merged #1507/#1514/#1515/#1516 remain separate claims |
| Antigravity | `AntigravityClaimScopedExperimentalCutExact`, `AntigravityResearchPromotionCutExact`, `AntigravityStrongestConditionalTheoremExact` | Claim-specific source/phase/ordinary model/replication still open |
| Eskridge | `AmyEskridgeLiTorrMechanismBridgeExact` and `AmyEskridgeVideoClaimAttributionLedgerExact` | [#1528](https://github.com/chboishabba/dashi_agda/pull/1528) OPEN: 35 HAL5 pages / video rows are source research, not measured gravity. #872 closed unmerged |
| Levin | `PatternMemoryCore`, `TravelingFieldControl`, `FungalCollectiveIntelligenceCore`, `FungalMemoryInterventionBoundary`; #99/#132 merged | Sheldrake style flag **already** in fungal core; no physical morphic effect inferred |
| Biology & BH4 | `BiologicalParametricStochasticLumpingExact`, `KitzerowBH4NeuralContextDiscriminatorExact`, `BH4NOSCouplingEvidenceExact`, `BH4RheaChEBIReactionExact` | [#1454](https://github.com/chboishabba/dashi_agda/pull/1454) OPEN **stacked on #1226**, not directly on master: original reactive-PNP and stimulant S1–S5 owners must be separately reconciled |
| Statistical controls | `ExperimentalCoordinateDesignExact`, `HistoryConditionedChoiceExact`, `LawlikeRegularityCounterfactualExact` | Statistical inference, SLR/ITIR are support tools, not experimental force/field owners |

**Existing detailed ledgers not to be replaced:** `Docs/research/SmithFilsingerPhaseDeliverablesExactRemaining20261116.md` contains F01–F16; `Docs/research/SmithFilsingerFiveGateEvidenceAcceptance20261117.md` contains F10/METER/F15/F16/D1 actual original evidence role inventory (**0/24 at its last local audit; do not treat as a fresh universal count**); BH4 #1454 `docs/biology/BH4ReactivePNPExactRemainingMaxCut.md` contains G0.01–04, S0.01–04, P0.01–08, P1.01–03, P2.01–02, P3.01–03; `BH4DifferentialStimulantObservationMaxCut.md` contains stimulant S1–S5. These branch-specific ledgers are documentary donors, not included in `master` by reference.

## 2. Phase gate sequence — deliverable, exact lemmas, closing receipts

Statuses: **[R]** previously source-written on `master` (not necessarily kernel-checked on this PR); **[N]** added in #1537 and source-written (not kernel-checked); **[O]** an exact unfilled obligation / proposed named lemma; **[E]** original empirical input that mathematics cannot manufacture.

### Phase Q0 — baseline / original-owner exact-head acceptance

**Deliverable:** one selected compiled PR root, source hashes, original speaker timestamps, reference and branch receipts; run locally, no GitHub CI authority.

- **Q0.1 [N]** `canonicalFieldNeedsPerturbation`, `canonicalFieldCorrelationNotCausalProof`, `sheldrakeQuestionAlreadyOwnedByLevin`: projections of **real** `TravelingFieldControl` and fungal owner. No proof of nonlocal influence.
- **Q0.2 [N]** `bh4CurrentTotalPoolNotSoleSufficientCause`, `bh4DevelopmentalHistoryMatters`, `nos3SourceEvidenceNotWholeAllocator`: existing BH4 **context/isoform** non-promotion projected at the cross-programme boundary.
- **Q0.3 [N]** `eskridgeLiTorrHistoryDoesNotEstablishEnhancement`, `antigravityTypedCutDoesNotProveClaim`, `unresolvedBoundaryChannelIsNotZero`: existing antigravity and source-work negative authority projected, not fabricated evidence.
- **Q0.4 [O]** `formativeFieldFocusedGoldenKernel`: **Agda 2.9** exact-head typecheck of `DASHI/EverythingSheldrakeFieldLevinFilsinger20261121.agda`, both new bridge modules and imported `master` files; record toolchain/version, commit hash, full output and source compilation failure if any.
- **Q0.5 [O]** `sourceOwnerVersionAndAttributionBidi`: for each imported source, correct first implementation, current source sha, original bibliography, and status; no alias by similar filename. **[E]** original Sheldrake transcript is an interview, not an experiment; Eskridge's HAL5 pages are historical presentation, not gravity data.

**Exit:** compiler succeeds on exact branch head, both synthetic scripts independently replay at exact head, no numerical acceptance misrepresented as kernel proof. Q0.4 remains OPEN until actually executed.

### Phase Q1 — static field vs geometry of form vs energetic work

**Deliverable:** a source-indexed controlled Galton-board/field model separating histogram, trajectory, local conservative field work, magnet placement/repositioning work, gravitational potential, impact heat and any active coil/controller.

- **Q1.1 [R/N]** existing `arrivalNoEarlier` / `loadWorkBound` and new `sameStipulatedBudget`, `differentOutcomesAtSameStipulatedBudget`: purely logical counterexample to the **inference** that a stipulated identical energy budget determines a unique finite outcome shape. Does NOT assert measured magnetic work is zero.
- **Q1.2 [O]** `originalSteelGaltonFieldForceTrajectoryWeld`: from measured `B(x,t)`, local magnetization/contact, geometry, ball mass, gravity and collision restitution, compute next-bin readout with uncertainty on the **same apparatus**. Do not equate an arbitrary branch probability with magnetic flux.
- **Q1.3 [O]** `magnetPlacementPotentialAndExternalWorkLedger`: signed `W_g=-ΔU_g`, `W_{mag}=-ΔU_{mag}` under stated conservative assumptions, explicit repositioning work and storage/temperature changes. Static magnet nondepletion is distinct from source-free repeated work.
- **Q1.4 [O]** `sameOriginalFieldMomentumAndPoyntingBalance`: all field/matter/boundary momentum and energy ports reconciled (or explicitly unresolved); no exclusion of fringing, demagnetization, conductive heating or impact work by assumption.
- **Q1.5 [O]** `galtonDistributionDoesNotIdentifyForceMechanism`: two distinct causal models matching the selected histogram, plus an independent field-position/field-off intervention that distinguishes them.

**Acceptance:** original per-trial trajectories, geometry, field/current/magnet provenance, calibrated ball statistics and work ledger. **No finite histogram proof can replace this measurement.**

### Phase Q2 — Filsinger dynamic field / retarded source and receiver

**Deliverable:** one common source-identified apparatus, time-indexed Maxwell–ADE material/field state, phase/impedance/geometry control, driver and ambient-source ports, signed work with source response and load.

**Existing Filsinger lemma IDs remain canonical:**
- **Q2.1 [R/O]** F01 `phaseCommonDriverRatioInvariant`, F02 `receiverPhaseIncludesRetardedPath`, F03 `detunedFreePhaseCannotRemainFixed`, F04 `independentUniformPhaseCancelsQuadraticCrossTerm`: retarded phases and coherence; their model/numeric results are *not* general physical-source proofs.
- **Q2.2 [R/O]** F05 `fixedSourceMatchGapSquare`, F06 `complementaryConductanceFlatAtPi`, F07 `phaseOptimumDependsOnSourceImpedance`, F08 `naturalPortWorkMustBeSigned`, F09 `phaseReadoutCannotIdentifyNaturalSource`: exact finite source limits and nonidentifiability. **Do not falsely mark source-work physical gate closed.**
- **Q2.3 [O]** F10 `retardedNonlinearMaterialEnergyIdentity`, F11 `wholeSystemMatchedTrajectoryDifference`, F12 `replenishedCycleVsTransientDiscriminator`: actual causal ADE dispersive polarization, modulator work, source backaction and all storage.
- **Q2.4 [O]** F13 `fullColumnSoilIonosphereAccessWeld`, F14 `allRegimesOnePhysicalParameters`: real ground/atmospheric conductivity tensor and measured source boundary, **one** actual original operating point.
- **Q2.5 [O/E]** F15 `sourceEnvironmentLoadSameCycle` and F16 `electricControlRainColdPoolCausalGain`: repeatable net independently replenished natural real work and controlled atmospheric causality. **These are the physical terminal gates.**
- **Q2.6 [O]** `sameControllerChangeOfFormVsSignedWork`: new cross-programme weld from actuator phase/geometry into receiver readout paired with the original signed `F10/F11/F15` ledger. A changed mode shape alone is not a natural-source joule.

**Exit:** original F10/METER/F15 receipts; compare pump-on/off, natural source on/off, tuned/sham controls at matched initial state and exogenous forcing, account for outgoing and stored energy. Synthetic field shape is not extra power.

### Phase Q3 — antigravity / Amy Eskridge: force-field channel discrimination

**Deliverable:** pair Eskridge's original historical/candidate mechanism family with a *selected* ordinary EM/mechanical/GR countermodel and independent gravity-channel measurements; never treat a video or patent as a working apparatus.

- **Q3.1 [R/N]** `eskridgeLiTorrHistoryDoesNotEstablishEnhancement` and `antigravityTypedCutDoesNotProveClaim`; existing `AntigravityClaimScopedExperimentalCutExact` requires source/phase/ordinary-model/replication scope to match one claim.
- **Q3.2 [O]** `eskridgeOriginalHAL5ClaimToSourceBidi`: each HAL5 slide/edited-video assertion maps back to original page and claim speaker, and to its *separate* technical lead. #1528 branch-only audit may be consumed as source data, never as proof of gravity.
- **Q3.3 [O]** `sameRigElectromagneticRecoilAndStressClosure`: ordinary charged/current body force `ρE+J×B`, currents, acoustic/thermal forces, fixture load, vacuum/ground and field momentum compared to an independent force/acceleration readout.
- **Q3.4 [O]** `LiTorrPhaseAndConstitutiveCoefficientResidual`: historical Li/Torr source coefficient, permeability/magnitude dispute, independently measured phase crossing, source scaling and independent gravity probe in one apparatus; existing `AmyEskridgeLiTorrMechanismBridgeExact` already defines the specific reopening target.
- **Q3.5 [O]** `gravityChannelResidualAfterOrdinaryFieldClosure`: calibrated residual surviving ordinary field/matter/boundary model, source scope and uncertainty; residual is *not yet* an identified modified-gravity mechanism.
- **Q3.6 [E]** source instrument raw traces, gravity sensor, phase, source scaling, independent replication; same original object. The suppression/deaths narrative receives **zero** evidentiary authority as physics.

**Exit:** independent claim-scoped physical comparative-anomaly receipt and separate mechanism attribution, never conflating field-induced lift, altered inertial response, modified local `G`, universal negative `G`, and energy harvesting.

### Phase Q4 — Michael Levin: morphology and material field memory

**Deliverable:** same-organism bioelectric state with external/current sources, spatial voltage/ion/pH and junction topology, target morphology, perturbation/removal, regeneration and history-indexed future readout.

- **Q4.1 [R/N]** `sheldrakeQuestionAlreadyOwnedByLevin`, `canonicalFieldNeedsPerturbation`, `canonicalFieldCorrelationNotCausalProof` and existing `PatternMemorySystem`, `LatentPatternWitness`, `TriggeredReadoutWitness`.
- **Q4.2 [O]** `sameTissueVoltageFieldIonWorkAndGoalBidi`: material electrical source work and chemistry are paid, while decoded morphology/goal belongs to a separately defined observational/control map.
- **Q4.3 [O]** `morphogeneticTargetSurvivesMatchedPerturbation`: same lineage and matched physical perturbation, delayed repair to measured target state, with target distinguished from visible morphology.
- **Q4.4 [O]** `exposureRemovalPersistentFungalMemoryCarrierDiscriminator`: matched exposed/unexposed colonies, source removed, quiescent interval, persistent state, later response and morphology/physiology/epigenetic/external-trace alternatives; use original `FungalMemoryInterventionBoundary` fields.
- **Q4.5 [O]** `historyFutureQuotientPhysicallyCommutes`: existing #1471 finite stochastic future phenotype quotient instantiated on the **same measured** tissue and appropriate interventions; keep projection residual.
- **Q4.6 [O]** `localPatternMemoryNotRemoteMorphicTransfer`: construct distinct observational mechanisms and explicit negative controls; endogenous local pattern control is insufficient to imply cross-population similarity influence.

**Exit:** source-labelled tissue/cell/colony experiment and physical field interventions, independently repeated outcomes and calibrated control/energy carriers. Bioelectricity is not a sole universal morphogenetic mechanism.

### Phase Q5 — BH4: specific electrodiffusive/biochemical memory, not a magical field

**Deliverable:** same physical 27-site/54-bond reaction–transport–electrical state, compartment/time-indexed enzyme/recycling/BH4/BH2/NAD(P)H and catecholamine flux; link measured physiology to morphological/field-state observations only where a true physical map is sourced.

- **Q5.1 [R/N]** `bh4CurrentTotalPoolNotSoleSufficientCause`, `bh4DevelopmentalHistoryMatters`, `nos3SourceEvidenceNotWholeAllocator`: hph-1 / Gch1 context and NOS3 evidence already delimit total-pool sufficiency and isoform generalization. They do **not** establish Kitzerow's whole allocator, a neural morphic field or causal ADHD subtype.
- **Q5.2 [O]** original #1454 **G0.01–04** exact-head kernel, **S0.01** `sourceOriginalRhea29x12ByteExact`, **S0.02** `sourcePaidKineticAndCompartmentParameters`, **S0.03** `originalStoichiometricElectroneutralityOrReservoirAccount`, **S0.04** `originalMassActionDetailedBalanceCompatible`. The original Rhea/ChEBI 29×12 source and separate residual columns cannot be replaced by the selected 15×5 TH/PCD/QDPR/DDC/DBH subset.
- **Q5.3 [O]** original **P0.01–08** `original369PNPPoissonBoundaryWellPosed`, `original54BondScharfetterGummelFluxExact`, `original54BondFluxAntisymmetryAndDivergence`, `original29x12MassActionReactionVectorExact`, `original369PNPImplicitStepExistsAndPositive`, `original369PNPDiscreteFreeEnergyDissipation`, `original369PNPBoundaryWorkAndChargeFluxExact`, `sameSourcePhysicalReactionTransportStep`. Existing local implicit solver trajectories are not full original-parameter existence or energy theorems.
- **Q5.4 [O]** original **P1.01–03** `physicalBH4StepCommutes`, `physicalPNPStepCommutesOriginal`, `physicalTissueOneStepRefinement`: this is the critical **Levin-field/BH4 same-state bridge**, not a superficial joint import.
- **Q5.5 [O]** original **P2.01–02** `physicalKernelLumpsUnderInterventions`, `physicalFutureQuotientIsMinimal`, and **P3.01–03** `sourceCalibratedParametersAdmissible`, `heldoutFuturePredictionsDiscriminate`, `originalBH4PNPGoldenITIRReconciled` (last is secondary interface work).
- **Q5.6 [O]** stimulant S2–S5 from #1454: source-qualified TH→DOPA→DA/DBH→NE stoichiometry and QDPR/redox; cytosol/vesicle/extracellular physical transport, uptake and loss; independent measured enzyme state and timing; matched drug-challenge/washout observer and held-out physiological predictions. Existing **rank 11/17, six invisible directions** is a restricted synthetic reaction/transfer observation calculation, not a full physiological mechanism.
- **Q5.7 [O]** `BH4ReactionTransportFieldEnergySourceBidi`: signed chemical/electrical potential and source flux on one compartment/boundary + real local physiological form/goal readout. Prevent double-counting NAD(P)H/chemical and electrical/electrostatic contributions, without silently zeroing exchange.

**Exit:** primary source byte/release, source-paid kinetic coefficients, local Agda kernel, correct Rhea species/directions, calibrated same-object assay and independent holdout; **no clinical treatment claims**.

### Phase Q6 — Sheldrake rival: causal transfer beyond traced material channels

**Deliverable:** an ethically and scientifically reviewable *preregistered* comparison of `H0` ordinary field/biology/learning, `H1` local latent pattern, `H2` retarded source/wave, `H3` selected anomalous gravity hypothesis, and `H4` additional cross-population similarity-history dependence.

- **Q6.1 [R/N]** `CrossPopulationRivalKernel` is only a typed **hypothetical** extra input; existing finite Galton histogram and new SymPy 2×2 design have an observational collision and full *formal* rank with independent knobs. No experimental `R` knob or fitted coefficient exists.
- **Q6.2 [O]** `matchedSourceHistoryAndCommunicationAudit`: independently tagged sites/populations, genetics, protocols, environment, direct/indirect information exchange, temporal order and apparatus drift.
- **Q6.3 [O]** `similarityExposureCounterfactualIdentifiable`: specify an operational historical exposure/intervention that cannot be predicted by source leakage, heredity, local field change or common external drive; establish positivity and adequate independent variation. **May be impossible to identify with available interventions**; document no-go rather than asserting.
- **Q6.4 [O]** `historyPermutedHeldoutPredictionSeparator`: preregistered time-shuffled, category-shuffled, negative-control and site-held-out null comparisons with multiplicity control.
- **Q6.5 [O]** `crossPopulationMechanismNonpromotionUntilReplication`: fail closed for non-replication and unresolved measurement or information transfer, with independent repeated source data.
- **Q6.6 [E]** original rat/distant-cohort or other fully documented raw primary data and independent replication with negative controls. No claim that the historical anecdotes already pass Q6.

**Exit:** distinguishability after ordinary source audit and genuine independent replication; inference remains model- and measurement-scoped, no universal law claim.

### Phase Q7 — integration, adversarial rerun and publication boundary

**Deliverable:** one PR-source-head matrix with each formal, numeric and empirical gate and its provenance. Open source-only PRs remain separate; no forced merge, no silent main/master alias.

- **Q7.1 [O]** `fullFormSourceGravityBiologyPromotionMatrix`: each result tagged synthetic, source-written, kernel-checked, source-calibrated, independently replicated, physically identified.
- **Q7.2 [O]** `oppositeMechanismNegativeControls`: each proposed positive test has one negative, null and provenance-conflict case.
- **Q7.3 [O]** `exactHeadLocalAcceptanceAndDiff`: exact script SHA, Agda full log and PR diff; reproducing an earlier source-equivalent script does not prove a modified head passed.
- **Q7.4 [O]** `publicationClaimBoundary`: avoid promoting mathematical identifiability to real-world nonlocal or antigravity detection.

## 3. Implemented in #1537 as of this roadmap commit

| File | Output | Acceptance ceiling |
| --- | --- | --- |
| `DASHI/Physics/Foundations/SheldrakeFieldLevinFilsingerConsolidationExact.agda` | Native owner imports, 4-path exact count, distinct mechanism families, retarded/work re-exports | Source-written; **no Agda kernel** |
| `DASHI/Physics/Foundations/FormativeFieldWorkLevinBH4EskridgeBidiExact.agda` | Direct source-owner Levin, fungal, BH4/NOS3, Eskridge and antigravity non-promotion projections, 4-question audit and equal-budget/different-form counterexample | Source-written; **no Agda kernel** |
| `DASHI/EverythingSheldrakeFieldLevinFilsinger20261121.agda` | Focused imports; no global ESD mutation | Source-written; Agda kernel pending |
| `scripts/check_sheldrake_field_filsinger_levin_sympy.py` | Galton distributions / normalized kernels / rank / timing / toy work ledger / hidden developmental history | **19/19 local PASS** on synthetic exact rational fixtures |
| `scripts/check_formative_field_work_levin_bh4_eskridge_sympy.py` | Gravity and magnetic conservative potential algebra, finite form/work separation, BH4 hidden branch allocation, source signed work, Eskridge kinematic non-identifiability, delay | **18/18 local PASS** on synthetic exact rational fixtures |
| This exact-remaining roadmap | Source/owner/gate dependency ledger | Written, not independently reviewed or kernel-certified |

Local SymPy acceptance totals **37/37** across **two** separate scripts, not 37 physical observations. The source/head replay of uploaded GitHub bytes is a separate remaining Q0 verification, not claimed.

## 4. Priority by shortest real-source cut, not speculative breadth

**First:** Q0 local Agda and exact-head replay. **Second:** Q1 conservative field/force rig and Q2 F10–F15 original signed source-work experiment, because the central dispute is whether a field **organizes energy** versus **supplies energy**. **Third:** Q3 independently measured gravity-channel residual (Eskridge) and Q4 same-tissue regenerative field-memory intervention (Levin). **Fourth:** Q5 BH4 source-paid 29×12 reactive-PNP and compartment-resolved chemistry; this is a concrete test of field/constraint plus material energetic flux. **Last:** Q6 nonlocal similarity-history hypothesis, only after standard channels and timing are bounded. No staged completion is inferred from a source description or from local symbolic identities.

### Runbook (local, never GitHub CI required)

```bash
python scripts/check_sheldrake_field_filsinger_levin_sympy.py
python scripts/check_formative_field_work_levin_bh4_eskridge_sympy.py
agda -i . DASHI/EverythingSheldrakeFieldLevinFilsinger20261121.agda
```

The current authoring environment has local SymPy but **no Agda binary**. A missing compiler is an explicit OPEN kernel gate, not a reason to label source-written definitions as verified.


## Q1/Q2/Q6/Q7 — OCT369 P0.35 cross-PR source/backaction (2026-11-22)
Original owner graph retained, not duplicated or merged: **PR #1537** owns Sheldrake's transcript-source hypothesis, the existing Galton/form vs paid-work source-written Agda, 19/19 + 18/18 local synthetic checks, Filsinger rectifier/midpoint alternatives and 65/65 finite source impedance BIDI; **PR #1534** owns PtMn3/OCT369 P0.33/P0.34 external Field Loom coil, Lorentz source reaction and gravity/fifth discriminators. PR #1534 now adds **P0.35**, commit `c625fae601c8304f8c6acf0cf8ce98cab2bae5f0`, whose source and exact attribution live in `Docs/research/OCT369P035SheldrakeFieldFormFilsingerLevinSourceBidi20261122.md`. The compact 39/39 local SymPy script `scripts/check_oct369_p035_field_form_momentum_source_bridge.py` has exact Git blob `35c4e629d0171c0f80a1f156505e396e53767f7c`. Its separate expanded 77/77 local fixture is a conversation artifact **not in git**. These are exact *synthetic checks*, not independent measurements.
**Original interview 00:43–01:24, 05:17–08:25**: stationary force does not require continuous mechanical work `P=F·v=0`; magnetic field can bias the path distribution of gravity-driven Galton balls. It does NOT imply a static magnet field stores no energy or that a motion-producing force has zero energetic source. **19:28–20:45** direct across-space/time resemblance is Sheldrake's *hypothesis*, not established from Galton magnetism. **20:58–21:58** speaker explicitly calls for conclusive empirical evidence, acknowledges insufficient existing broad acceptance. The transcript's discussion of "pushing and pulling" does not by itself claim measured violation of Newton or Maxwell.
**Important opposing-actions upgrade for Q1 and F10–F15:** P0.34 mechanically verified `F_body≈-F_coil` in a *magnetostatic* source. A time-varying circuit/coil with phase-shifted fields must use source+body+other-matter momentum and electromagnetic field momentum/stress boundary, not demand instantaneous equal-and-opposite **mechanical** forces. In a closed idealized boundary, `F_body+F_source+F_other + dP_EM/dt=0`; for an open boundary, record signed stress flux. P0.35's exact synthetic sinusoidal lag illustrates closure; NOT an exact measurement of the Filsinger waveform. Q1 must record synchronized `E,B,J,V,I`, mechanical reaction and field flux with source location and sign. A capacitor may rotate phase and store/return reactive energy, but the finite winding's `Rs |I|²` and any clamp source heat persist. Source-experimental topology (two cap/coil diode pairs vs winding groups, bridge N-to-M return and Earth identity) remains OPEN.
**Q6 morphology control:** local `B`, circuit condition `C`, independent hypothetical historical-similarity condition `H` need orthogonal interventions, not a single "field ON" switch; ideal 2×2×2 polynomial design rank 8, observational all-off/all-on rank 2. Blinded real/shuffled histories, source isolation, measured local B/E, source timing and held-out replication are required before calling any residual morphic/nonlocal. The 27-cell ternary chart is an INDEX and measurement carrier, not an actual historical resonance mechanism.
**Q7 claim boundary:** "form changes despite no continuous mechanical output power at rest" does not establish self-lift, new gravity, or extra electrical work. OCT369's six typed targets still require calibrations of 3D stability, supply/support stresses and independent remote freefall/clock; source energy/reaction are not accidentally erased by moving them outside the chosen experimental boundary. Michael Levin, Rupert Sheldrake, Kang et al, Sato/Hayami, Ōiké/Peters/Shinada, classic Maxwell/Newton/Poynting, original Filsinger source narrations and existing DASHI proof modules retain their separate prior ownership. **No Agda kernel or experimental receipt** comes from adding this roadmap reference.
