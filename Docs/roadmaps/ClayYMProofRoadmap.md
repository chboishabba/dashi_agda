## 21 November 2026 — controlling YM P0 theorem-first directive



**The main mathematical goal is the original four-dimensional interacting
Yang–Mills existence and mass gap, for each compact simple gauge group.**
R445, F19, R320, CMP116/119, R5xx, source-owner symbols and PR numbers
denote **iterative attempts and reusable intermediate lemmas**. They
are neither distinct prize-problem milestones nor a physical time
coordinate or RG iteration by default. Counting their accepted finite
identities is NOT a measure of progress toward the continuum proof.

**Physical endpoint theorem, with source obligations:**
- **E1:** construct a nontrivial interacting 4D original Wilson/Schwinger
  continuum at a→0 and V→∞, with projective compatibility, Euclidean
  symmetries, full reflection positivity and the required OS axioms.
  An abstract `originalWilsonConverges` field or a finite E1 cylinder
  identity is NOT a source proof of this.
- **D1 (if using the covariance-decay route):** prove genuinely
  original full Wilson connected-covariance small+large-field bounds
  in fixed physical units, uniform in lattice spacing and volume:
  `|Cov_a(W_x,W_y)| <= C_G exp(-m_G d_phys(x,y))`
  for original physically dense gauge-invariant word tests, with
  source constants C_G<∞ and m_G>0, independent of a,V.
  The direct reconstructed-spectrum route MAY bypass CMP116/D1,
  but never E1 or D2.
- **D2:** use ONE `H_OS` reconstructed from that SAME E1
  reflection-positive Schwinger family. Prove the full nonvacuum
  spectral projection `1_(0,m_G)(H_OS)|_(Omega^perp)=0`, not just
  finitely many selected Wilson correlations. Positivity and
  dense cyclic coverage are physical hypotheses to be paid.
- **N1/G1:** certify a surviving nontrivial local continuum
  observable and the original argument for every compact simple G,
  not just a finite SU2 subgroup or fixed SU(N) sample.

**What #1536 contributes without claiming closure:** finite original
F19/R445 128+896 source labels, exact weighted finite pushforward,
finite Wilson marked/covariance algebra, time/reflection commuting
squares and source interface compilers. These can be used only to
show that the physical source employed in the ultimate E1/D2 proof
is the *same* one. They supply neither the missing uniform small/large
field inequality nor a physical spectral lower bound. Their Agda
proof candidates remain kernel-pending.

**Immediate P0 maximum cut:** (1) supply actual original Wilson
physical convergence/cutoff-uniform clustering or an alternative
spectral-gapped reconstruction with matching density; (2) certify
continuum RP/OS on the genuine physical word domain; (3) pay the
same-H full-sector gap and N1; (4) extend group scope G1.
Do not insert new finite codecs or OS/H wrappers unless a specific
required original source identification fails. Finish kernel
acceptance of already-written code without promoting it into a
physical theorem.

**Source attribution:** Wilson/Balaban, published OS/RP and existing
DASHI exact source owners retain their original ownership. No
new Clay YM proof or pinned Agda 2.9 kernel result is claimed here.

### 21 Nov P0 source archaeology — the existing CMP116/W1/W3 theorem is NOT the E1/F19 physical record

**New inspected source audit on #1536:** [original CMP116/W1/W3→D1→E1/F19 physical source boundary](https://github.com/chboishabba/dashi_agda/blob/agent/ym-p0-cmp119-r445-master-weld-20261121/Docs/physics/YMClayCMP116W1W3D1E1F19PhysicalSourceAudit20261121.md); audit commit `e7833e2b`. The canonical `OriginalSmallLargePhysicalSource` and `OriginalRealCMP116PhysicalSelection` records are already present and the actual Wilson cutoff-`n=3` BIDI adapter already reuses the full-Wilson estimate. A source-written conditional compiler is **not** evidence that the selected record is inhabited.

**Preferred existing original W1/W3 payment:** `BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact.SourceFirstLiteralWilsonJetLocalization` already owns the normalized cluster jet. Its `pointwiseLiteralWilsonJetLocalization` and `localizedLiteralShellChargeSum` explicitly remain conditional; equivalently the existing `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` must be proved on original source-supported spanning clusters. Fill the **already-existing** full-Gibbs D1 `originalFullCovarianceBelowSmallPlusLarge`, `largeFieldErrorCalibration` and both common-physical-distance rate fields, with original cutoff-independent constants and one `0 ≤ commonQ < 1`. Finite one-site plaquette-deficit/one-link-tail suppression is not spatial connected-cluster suppression; an exact Bernoulli counterexample was checked locally with SymPy. #1444-only `naturalPrefactorR342` improves prefactor bookkeeping but still takes selected localization and distance/time calibration as inputs.

**No promotion:** cutoff-3 F19 weighted covariance is not an all-cutoff E1 continuum limit; C₂ time is not arbitrary Euclidean time. Agda kernel unrun. D2 same-`H_OS` dense nonvacuum spectrum, E1 interacting continuum/RP, N1 and G1 remain OPEN. Reuse estimates, do not reconstruct them.

### 21 Nov P0 local SymPy original Wilson action-fibre counterexample and finite Haar distinction

**NEW exact local SymPy 1.14.0 result** (source-shaped original 4D side-four Wilson geometry): enumerated all **1536 original positive-oriented plaquettes**; all **1024 fine positive links** appear in exactly **6** plaquette boundaries, hence the 128 selected links contribute 768 incidences and the **896 retained spectators contribute 5376 original fine-action incidences**. This was executed locally (not Agda or CI) and committed to `scripts/check_ym_f19_r445_sympy_purehaar_weld.py` on #1536 [commit e3dd8f5a](https://github.com/chboishabba/dashi_agda/commit/e3dd8f5ab40702199ef6951a2a3e734bd41e2890); exact committed checkout not independently run in local container.

**Exact counterexample on actual original Wilson plaquettes:** configuration U assigns every original 1024 SU2 link the 2×2 identity; configuration V flips ONE unselected spectator to `-I₂`. They induce **exactly the same 64 original native R445 blocked link matrices** (the changed bond is outside all 128 selected links). Yet exactly **six** original fine plaquette traces switch from `+2` to `-2`, making the original sum of positive-oriented fine plaquette traces differ by **24**. For nonzero Wilson coupling their original fine Boltzmann weights are different. Therefore the fine Wilson **action/weight is NOT a function of these 64 coarse link values alone**. This does not forbid an effective coarse density: it PROVES why the existing F19/R445 weighted fibre integration of the full original 128+896 source is necessary and why pure-Haar coarse invariance is not interacting-Wilson RG closure. All 896 residual links must be retained during fibre integration. No physical continuum claim.

**Finite convolution check**: exact SymPy Q8 ⊂ SU(2) matrix enumeration of all `8×8=64` ordered pair products: each of the eight outputs occurs eight times. This supports the finite-group analogue of the original `YMClayR445OriginalPureHaarBlockWeldExact` unweighted two-link Haar assertion, not the existence of continuous Haar integration or the four-dimensional interacting quantum continuum.

**Remaining native receiver obligations**: #1536's new `YMClayOriginalF19R445PureHaarReceiverCandidateExact.agda` (commit `350273ec`) names the ACTUAL receiver with source-count transport and the exact F19 `Torus.Product` vs R445 pure-Haar `Data.Product` flat pair decoder alignment. It uses `refl` as a **candidate** for this pair decoder normalization, **Agda kernel NOT RUN**. No new axiom, but it must not be reported as an accepted theorem. A kernel failure here should be repaired using the already-original `YMClayOriginalWilsonPairSpectatorDecoderExact` split/join, `YMClaySUNWeightedDisjointPairFibreReparamExact` pair multiplication, and original R445 finite Haar flat-pair lemma, NOT by inventing a new physical measure. The physical maximum-cut remains original W1/W3 interaction/large-field uniformity, E1 genuine changing-cutoff continuum/RP and D2 one actual reconstructed H_OS.



### 21 November 2026 — source-native original Wilson 12/8 periodic conflict colors, coherent tail improvement

New original 4D periodic Wilson combinatorial source derivation: [YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md](../physics/YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md) in master-based PR #1536 (not yet merged into this stacked branch). The true plaquette-conflict graph has an explicit 12-color proper coloring for every side L>=3, 8 colors when L even. For any marked original links S, one plaquette-independent class T has |T|>=ceil(|S|/12), or ceil(|S|/8) on even L; conditional original SU(2) Wilson Haar on T factorizes exactly. Thus the EXISTING coherent-bad bound strengthens from q^ceil(|S|/19) to q^ceil(|S|/12), or q^ceil(|S|/8) even L. The 14-degree root animal count 196 remains unchanged. n=3 R445 selected fine bond geometry: 128 selected = four direction classes of 32; 896 original spectators are not discarded. The companion #1536 script checks all plaquettes L=3,...,11 with local SymPy exact rational controls.

**New two-channel adaptive mixed-contour bound:** for any fixed original marked link set S of n distinct links and 0<=h<=n, with N_fru(S) its frustrated-staple count, the existing original one-link SU(2) Wilson conditional and the explicit K-color classes give
`P_mu(all B_l on S) <= P_mu(N_fru(S)>h) + K*q^(ceil((n-h)/K))`, K=12 uniformly or 8 when L even. Proof: N_fru<=h implies some fixed color class contains >=ceil((n-h)/K) coherent marks; the count/coherence of that class is measurable in the complement, so condition on the true original Wilson Gibbs exterior, multiply its one-link probabilities, and union over **K classes only** (not choose(n,h) coherent subsets). Full explanation/source proof is in PR #1536 `Docs/physics/YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md`. This reduces the hard D1-FRU-01b target to a **source-derived fixed-contour frustrated-count large deviation** strong enough to beat rooted-animal entropy. No such physical fixed-contour tail or W1/W3 source identification is claimed, so D1 full covariance and E1/D2/N1/G1 remain open; no Agda kernel receipt.

**Correction — reuse pre-existing microscopic chessboard donor before asking for D1-FRU-01b from scratch:** #1444 already has `Docs/physics/YMClayOriginalWilsonSparseChessboardBidi20261119.md` and `Docs/physics/YMClayOriginalWilsonSparseChessboard20261120.md`. The former uses original Wilson site-plane RP + closed-cube chessboard + original pressure lower bound to derive, on reflection-compatible EVEN periodic tori, a **conditional analytic fixed-contour all-bad link bound** `P(all bad on S) <= u_cb^|S|` with `u_cb=6 exp(C(beta)/4-beta*epsilon/96)`, `C(beta)=8+(2/3)log24+log(beta)`, `epsilon=(6-r)/6`; the latter's conservative plaquette-moment donor has `u_plaq=6 exp(C(beta)/16-beta*epsilon/384)`. Local SymPy source-rate comparison at r=3 finds the respective `196*u<1` thresholds beta≈2212.81 and beta≈6335.55. These authors/owners PRECEDE the new 12/8-color coherent-channel improvement; the latter and the K-class adaptive mixed inequality are complementary, not first-ever full bad-contour suppression. The actual remaining D1 payment is: certify native **original gauge Wilson site-reflection/closed-cube chessboard applicability** and physical-scale extension, connect that full-bad event source to true marked CMP119/122/CMP116 small+large interacting covariance/absolute W3 activities and cutoff/volume uniform physical support calibration. A finite microscopic bad-link probability does not equal connected Wilson loop covariance, cannot prove E1 continuum or D2 same-H gap. In #1536 consult `Docs/physics/YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md` for attribution and comparison. Native Agda kernel receipt remains open.

**Boundary:** a geometrically spanning mixed/frustrated contour can avoid any all-coherent chain; D1-FRU-01b/02, true large-field activity, common fixed-physical-scale q<1, full original CMP116 same-J small+large record, E1/D2/N1/G1 remain OPEN. This finite combinatorial proof does not instantiate `OriginalSmallLargePhysicalSource` or the actual physical W3 rooted-shell charge bound. No Agda kernel acceptance claimed.



### 22 November 2026 — original R445 × Base-2/369 EIGHT-SHEET actual bond codec (P0)

**New original full-label BIDI on master-based PR #1536:** DASHI/Physics/YangMills/YMClayR445Base2ThreeAxis369FibreBIDIExact.agda, regression-attached in DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda, full source note Docs/physics/YMClayR445Binary369EightSheetBIDI20261122.md, checker scripts/check_ym_r445_base2_369_eight_sheet_bidi_20261122.py. Reuse ORIGINAL R445 side-four PositiveBond, its side-two coarse bond, its axial two-link phase and original R445 parity codec, not a new F19 sort or synthetic Wilson measure. Each native fine bond has exactly one reversible (mu,c,p,s) address: mu=2 bits, c=4, axial p=1, THREE transverse parity bits s=3. Thus 1024=2^10=2^7×2^3=128×8: selected R445 s=000 is 128 bonds; other seven actual binary sheets preserve all 896 spectators. Original 8-class conflict color is (mu, parity(s)); selected s=000 occupies four orientation-specific independent subclasses of 32. All 1536 original plaquettes have four distinct colors. **Negative control:** 384 original plaquettes contain TWO selected bonds of different orientation, so **the 128 selected Wilson conditional links do NOT factorize** by conditioning only on the 896 spectators. A 32-link same-orientation class factors conditioned on the other 992 original links.

Existing signed 369 owners Base369BinaryTernaryRefinement (2^a 3^b), BinaryBalancedTernarySubcarrierExact and BalancedTritBitFibre preserve semantics: binary 000 embeds as (-1,-1,-1), a CORNER in T^3; not the balanced ternary centre (0,0,0). Eight corners are a proper subcarrier of the 27-state ternary cube (8+12+6+1); **not** the 9=T×T nonary carrier and not an invented 9DOF. The 3-bit cube has 8 vertices, 12 edges, SIX commuting faces and matches #1291's finite cube *interface*, not its indexed history/time/higher-coherence proof. Fresh local SymPy 1.14 and exhaustive Python 1024/1024 source roundtrip, 1536/1536 original plaquette test, 384 selected-pair negative control PASS; committed checker Git blob matched actual executed local script byte-for-byte. **Agda 2.9 kernel NOT run.** Full Wilson marked W1/W3 large-field source, fixed physical scale q<1, E1/D2/N1/G1 remain OPEN. Do not promote this finite same-label cube to a covariance theorem or alter the theorem-first directive.


## 21 November 2026 — CORRECTED original Wilson ESTIMATE audit: reuse original D1/CMP116 and marked W1/W3, connect SAME E1/F19 physical source

**Correction requested by user:** the repository DOES have substantial **Wilson estimate theorems**, including the complete small-plus-large-field route, the native real CMP116 cutoff-uniform bound, and source-owned marked two-Wilson connecting shell. They must **not** be represented as unbuilt constructs. Direct blob hashes `master` == #1444 for all three:
- `YMClayD1OriginalFullWilsonSmallLargeFieldExact.agda`: `OriginalSmallLargePhysicalSource`, `originalFullRealCovarianceBelowSmallLargeEnvelopes`, `originalFullWilsonUniformGeometricClustering`. This already **proves** on the literal full interacting original SU(N) Wilson changing-cutoff measure the conditional estimate
  ```
  |Cov_originalWilson(n; F_n,G_n)|
    <= (smallAmplitude + largeAmplitude) * commonQ ^ physicalBlockDistance(F,G),
     all n, 0 <= commonQ < 1, amplitudes independent of cutoff and volume.
  ```
  **Precisely proof-bearing record fields**, not invented missing theorems: `originalFullCovarianceBelowSmallPlusLarge` (TRUE interacting full Wilson vs localized small field + residual), `smallFieldEnvelopeCalibration` on CMP116 admissible pair, `largeFieldErrorCalibration` for true Wilson large fields, and `smallFieldGeometricRate` / `largeFieldGeometricRate` on the SAME selected physical distance and fixed cube length. No verified inhabitant of the complete record for the selected original full Wilson source was found in the searched source owners. Do not infer physical D1 from the existence of a Set-valued record/theorem.
- `YMClayD1OriginalRealCMP116VariableCutoffExact.agda`: `OriginalRealCMP116PhysicalSelection`, `sourceMagnitudeIsOriginalRealCovariance`, `originalWilsonRealCovarianceUniformBound`, `originalWilsonRealCovarianceGeometricBound` already translate original Wilson literal mixed-log jet and selected CMP116 source into a REAL same-family uniform bound with fixed physical rate, when its selected common-domain `sourceResponseIsActualOriginalWilsonJet`, `uniformSourceEnvelope`, `upperHasUniformGeometricRate` are provided. It is a genuine theorem compiler, not a free analytic estimate.
- `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.agda` owns the source-first W1/W3 two-support differentiated cluster sum, finite absolute triangle/monotone summation, and `twoWilsonMixedLogBelowPhysicalRootedShell`; `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` is the selected physical bridge. `BalabanLiteralWilsonMarkedLocalizationSourceExact`, `BalabanWilsonTwoInsertionConnectedShellRound491Exact`, `YangMillsWilsonContinuumClusteringRound551Exact`, `YangMillsSourceFirstWilsonCovarianceRound556Exact` ALREADY provide W1/W3→rooted-shell→finite geometric→continuum clustering with the **same CMP119/T5 covariance** chosen by R556. Not a printed Balaban bond-valued J = Wilson loop assumption. The physical W1/W3 marked cluster-charge source, actual localization and bounded-test/convergence/physical time inputs must be instantiated, not rebuilt as new abstract lemmas.
- #1444 `BalabanCMP116SharedMarkedDirectCalibrationRound344Exact.agda` has a head-only `naturalPrefactorR342` not identical on master, retaining natural selected source prefactor `C_H`. Avoid restricting this branch unnecessarily to the older canonical `C_H <= 1` presentation; this improves source calibration but does not on its own prove literal original Wilson W1/W3 full large-field control.

**NEW source-first WELD on #1536**: `DASHI/Physics/YangMills/YMClayOriginalD1FullWilsonE1F19EstimateBIDIExact.agda`, source-written [commit `f3207243`](https://github.com/chboishabba/dashi_agda/commit/f320724388161ced673363891f63760a1e087e39), NOT Agda kernel accepted. `originalNativeWilsonMark` is actual original n=3 `nativeSUNBlockLinks` → `Codec.encodeOriginalBonds 2` → selected real coarse F/G test. `SelectedOriginalD1FullWilsonForNativeF19` only adds pointwise **original test membership/identity** at cutoff 3 to the **already original** `D1.OriginalSmallLargePhysicalSource` record; it does NOT postulate an extra covariance upper bound, construct another Markov/Gibbs measure, discard 896 spectators or replace all-cutoff original D1. `originalD1SelectedCovarianceIsNativeWilson` derives equality of original Gibbs connected covariance using `Wilson.originalWilsonExpectationExtensional` for F,G,FG, no function extensionality. `originalNativeWilsonCutoff3CovarianceIsE1` is an explicit source-definition **`refl` candidate** from already-original same-measure E1/D1 modules, and the preceding #1536 `originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective` completes the selected E1/F19 weighted physical source. `originalF19EffectiveCovarianceFromFullWilsonD1` therefore **transports the EXISTING** original full-Wilson small+large field uniform envelope directly onto the same cutoff3 F19 interacting effective covariance, CONDITIONAL on those source records/test identities and on earlier Agda candidates type-checking. It creates no new physical rate or continuum clock. If a kernel failure occurs, fix the precise original n3 field/vector normalization instead of assuming equality of two probability measures.
  
**Executed LOCAL SymPy 1.14.0, no CI/Agda:** `scripts/check_ym_d1_full_wilson_f19_source_weld_sympy.py` [commit `88e4fe68`](https://github.com/chboishabba/dashi_agda/commit/88e4fe6889e43293654be6a6a8906f7f86217923) is **byte-verified** against executed `/mnt/data/check_ym_d1_full_wilson_f19_source_weld_sympy.py`: both git blob hash `6e30992591d9ea79421dd06cfaff4a9f1010968b`. It uses the already original source-shaped 4D 1024-link 3-active Q8 conditional Wilson slice: **512/512** exact original native/F19 pointwise blocked source marks and products with 896 spectators influencing the weight; **symbolic exact Z,F,G,FG and centered covariance identity**, four rational coupling comparisons, exact algebraic identity for combining two geometric envelopes (a chosen illustrative rational amplitude, NOT a source Wilson bound), and **fixed-side-two C2 time periodicity negative control** (not actual unbounded Euclidean time). None of this proves source `OriginalSmallLargePhysicalSource` is inhabited for full all-cutoff interacting Wilson or physically reconstructs `H_{OS}`.
  
**BIDI roadmap payment NOW:** Original D1 FULL Wilson theorem and R491/R551/R556 marked Wilson shell/continuum compilers are **KNOWN existing producers**; branch #1536 joins their original real Wilson source to E1/R445/F19 physical marked observables at n=3 without duplicating decay or making a new metric. The remaining *source instantiation* is exactly original gauge-invariant `physicalTest n` for the true all-cutoff Wilson W1/W3 field, physical source CMP116 same-J/common-domain response, original small+large-field decomposition and the two calibrated cutoff/volume-independent rates, or a stronger existing original donor that supplies them. Then original selected `t,k` time-scale/OS-positive limit, dense SAME-H source and nonvacuum spectrum (E1/D1/D2/N1/G1). A single fixed side2 C2 coarse time block cannot certify arbitrary Euclidean separation. P0 YM first, P1 antigravity next. NO Clay mass gap claimed.

**Branch/acceptance:** #1444 is stacked and is **roadmap owner**, #1536 independently master-based is source-written code owner; original full-Wilson estimate files already present on master/#1444. #1536 golden `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` imports new D1/E1/F19 adapter [commit `3cad0322`](https://github.com/chboishabba/dashi_agda/commit/3cad032282f2026c060a8e6e96e4f295c39678bb). Source checker manifest includes original D1, real CMP116, literal W1/W3 and new D1 adapter plus local SymPy [commit `0d525112`](https://github.com/chboishabba/dashi_agda/commit/0d525112d642c4fd5dd70f512ce305328d46d49c). Agda kernel and exact checkout integrated runner NOT RUN; only local SymPy execution accepted.

---

## 21 November 2026 — P0 original E1 cutoff-3/1 ↔ F19 effective ↔ three-moment **physical error compiler** (BIDI steelman)

**Forward and reverse ends now identified on the SAME original field/measure.** This source review uses original `master` `YMClaySUNVariablePhysicalCutoffFamilyExact.physicalFiniteCutoffMeasure`, `YMClaySUNConstructedPeriodicGaugeCodecExact.actualPeriodicProductMeasure`, `YMClayNativePositiveBondEnumerationVectorExact.decodeOriginalBonds`, `YMClayE1OriginalSUNDependentCylinderExact.actualOriginalWilsonMeasureAt`, `YMClayE1A3OriginalR445CrossCutoffSourceExact.originalE1FineBlockedIsR445EffectiveCoarse`, `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` and `YMClayE1OriginalR445ThreeMomentCutoffTransportExact.originalE1CovarianceErrorFromThreePhysicalCutoffMoments`. These constructors use ONE selected product-Haar source and the actual n=3 1,024-link six-plane Wilson weight. **No alternate action/clock/measure/regular conditional is added.**

**New master-based #1536 source-written** `YMClayOriginalE1A3NativeF19WeightedBIDIExact.agda` committed [`e2d9f8be`](https://github.com/chboishabba/dashi_agda/commit/e2d9f8be756c46fe8fab040aa3e12812079410c4), then completed at [`d646aa01`](https://github.com/chboishabba/dashi_agda/commit/d646aa011e22d4ce75ba7ae052e41476a87968cb). `coarseVectorTestAsNative` uses the EXISTING `Codec.encodeOriginalBonds 2`, no new observable dictionary. `originalE1Cutoff3IsNativeR445VectorExpectation` is a closed original-definition reduction **candidate** (`refl`, Agda NOT RUN), with identical source density, normalized partition, side-four source decoder and native two-link block. Compose with new original weighted BIDI from prior cut:
```
  actual E1 n=3 original blocked Wilson expectation
     = actual native R445 n=3 vector Wilson Gibbs expectation
     = original F19 n=3 weighted effective expectation
```
for every selected 64-vector coarse Wilson test. **NOT** the independent bare n=1 Wilson state at beta(1). `originalE1Cutoff3ConnectedCovarianceIsOriginalF19Effective` proves F/G/FG covariance congruence on this same original n=3 physical measure, conditional on the two upstream source candidates.

**No new quantitative RG theorem needed**: `originalE1VectorCovarianceIsOriginalThreeMomentE1` source-equals the EXISTING n=3 E1 connected covariance; `originalF19EffectiveCovarianceIsOriginalR445ThreeMoment` composes this with original effective R445 covariance. `originalF19EffectiveCovarianceErrorFromE1ThreePhysicalMoments` then transports the **existing original** `originalE1CovarianceErrorFromThreePhysicalCutoffMoments` to F19. Its precise selected physical bound is
```
 |Cov_F19,eff(F,G) − Cov_E1,bare,n=1(F,G)|
 <= err_FG + err_F * bound_E1,eff(G) + bound_E1,bare(F) * err_G
```
where `err_FG`, `err_F`, `err_G`, the magnitude bounds, and their nonnegativity are ALL explicit **original n=3 effective-vs-n=1 bare Wilson** inputs. **No geometric cutoff rate, 1/k decay, uniform Wilson D1, E1 limit or physical mass gap is manufactured.** Keep independent source Euclidean time `t`, RG cutoff stage `k`, zero/phase, and all 896 interacting residual links in the original integrand.

**LOCAL SymPy 1.14 ONLY, no CI/Agda**: uploaded `/mnt/data/check_ym_native_f19_weighted_fibre_sympy.py` was run locally and PASS (the original 4D geometry, 1,536 plaquettes, 1,024 links, 128 chosen + 896 spectators, 512/512 three-active-link exact Q8 conditional Wilson weighted configurations, all eight coarse pair fibres 64 configurations, symbolic weighted partition and three moments and centered covariance). Added and actually ran `/mnt/data/check_ym_e1a3_f19_three_moment_sympy.py`, source-equivalent of [committed `efc527a0`](https://github.com/chboishabba/dashi_agda/commit/efc527a022ead800ef9bbd4fd35e90b22cb42285), using independent original coarse Q8 beta(1)=0 marginal as a **particular bare comparison only**. Symbolic polynomial/rational calculation established the exact three-moment telescope; at `z=1` the effective and bare test marginal coincide; at `z=2`, original conditional effective-minus-bare covariance equals `-50463508331656977/256158079841410082`, nonzero, and the exact source upper bound is `638868999623286135/256158079841410082`; 4/4 rational coupling bounds for `z = 1/2,1,2,3` PASS. **This 3-active-link source-shaped conditional slice is NOT full infinite-dimensional original SU(N) Wilson E1, nor an arbitrary-cutoff physical bound.**

**Critical status and next reverse-payment:** new Agda was written and read back but UNCOMPILED, `originalE1Cutoff3IsNativeR445VectorExpectation = refl` depends on original dependent link field↔1024-vector/source measure definitional reduction. Agda kernel must actually accept both this and earlier F19 native 64-ordered SU(N) `refl` candidates. Original already-existing E1 all-cutoff cylinder limit theorem `YMClayE1VariableCutoffCylinderLimitExact`, CMP119/122/116/W1/W3 marked Wilson source, original physical Wilson RP and one OS H spectral consumer remain DONORS, not missing generic constructions. **Actual remaining physical INPUT:** interacting original cutoff/volume-uniform three-moment error and original Wilson two-support marked-clustering estimates, genuine `t,k` cutoff/volume physical-scale limits and dense same-`H_OS` spectral gap (E1/D1/D2/N1/G1). Don't confuse finite exact comparisons or Q8 tests with continuum mass gap; P0 YM first, P1 antigravity after. Source-writing branch #1536 is independent from #1444 stacked roadmap; no merge claimed.

---

## 21 November 2026 — P0 steelman BIDI **original native R445 Wilson Gibbs → existing F19 weighted effective density**

**Weld forward from the ORIGINAL source, reverse from physical E1/OS.** The latest source audit found the receiver we should use: `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` already proves the **same original interacting 1,024-link Wilson-Gibbs** numerator and partition are transported to the full F19 64-coarse-link **weighted effective density**, integrating original selected 128 links and all 896 interacting spectators. We must not replace it with the pure-Haar result or invent another effective action. The preceding native-64 square `YMClayOriginalF19R445Native64HolonomySquareExact.originalF19CoarseWilsonObservableEqualsNativeR445` identifies each original coarse Wilson test at fixed fine U with the F19 original constructed adjacent-swap 64-block test (the latter still has an **Agda-unchecked 64-index `refl`**).

**New #1536 SOURCE-WRITTEN direct BIDI module** `YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact.agda` (latest corrected [commit c0c54b0d](https://github.com/chboishabba/dashi_agda/commit/c0c54b0d9c48dfde94395f4e2bac552217feb04b)) defines exactly the native source mark
```
N_native(F) = productHaarIntegral_1024 (λU ->
               originalWilsonVectorWeight(U) *
               F(originalNativeCoarse64(U))).
Z = productHaarIntegral_1024 originalWilsonVectorWeight.
```
It first invokes existing `Original.productIntegralCongruent` and original native/F19 pointwise `cong` to show `N_native(F)=N_originalF19(F)` **under the SAME full interacting Gibbs integrand**. Then it invokes the **ALREADY EXISTING** F19 `originalCanonicalBlockedNormalizedEqualsPhysicalEffective` for every `F : Vec SUN 64→ℝ`, obtaining the *finite cutoff side4→side2* normalized equality
```
divide(N_native(F),Z) = originalEffectiveBlockedNormalized(divide,F).
```
No new quotient axiom (the same caller-supplied `divide`), no new Wilson density or field/Haar space, and no assumption that the effective density equals **bare** side-two Wilson at beta(1). All original 896 spectators remain *inside the full original weight* until the ORIGINAL F19 effective fibre integration. **This Agda source is a proof candidate, NOT KERNEL-ACCEPTED**, and depends on earlier original 64-link/index candidates plus original source imports.

**LOCAL SymPy 1.14.0**, no CI/Agda: ran the supplied `/mnt/data/check_ym_f19_r445_sympy_purehaar_weld.py` successfully (1,024 permutation both inverses, noncommutative 64 original blocks, 96 plaquette words, 5,120 Q8 link values, 320 ordered blocks, 480 traces, original 896 spectators and 5,376 original fine Wilson plaquette incidences). Then constructed and actually ran `/mnt/data/check_ym_native_f19_weighted_fibre_sympy.py`, a STRICTLY **conditional 3-active-link source-shaped slice** of the original 4D 1,024-link Wilson action: fix other 1,021 links to identity, enumerate both selected links and one adjacent original spectator through the eight exact Q8 SU(2) matrices (8³=512). Precisely 16 original fine plaquettes are affected; all 512 configurations reproduce original native 2-link product `W=U·V`. The full original (restricted-slice) Wilson weighted partition, `F(W)` and `G(W)` marks, product mark, and **centered covariance numerator** equal the grouped F19 conditional effective sum as polynomials in positive symbolic coupling `z`. Each of eight coarse Q8 products has 64 preimages; at `z=1` the effective weights are 64 each, while at `z=2` they have THREE distinct values. Script is source-equivalently committed on #1536 as `scripts/check_ym_native_f19_weighted_slice_sympy.py` [commit a6d80a04](https://github.com/chboishabba/dashi_agda/commit/a6d80a040342bcb0eef2f897dd86de0a111fd13f). This is **NOT** the full SU(N) Gibbs/Haar integration over 1,024 active links; it is a local exact falsifier for dropping spectators/assuming pure Haar and a source-shaped test of native/F19 weighted composition. No comparison of physical continuum rates or compact simple G obtained.

**BIDI reverse solve**: the original `YMClayE1A3OriginalR445CrossCutoffSourceExact` already gives fixed original n=3 blocked Wilson vs SAME R445 effective expectation; `YMClayE1OriginalR445ThreeMomentCutoffTransportExact` already converts original three-test physical cutoff residuals to native R445 effective-vs-bare covariance error. The exact `YMClayE1VariableCutoffCylinderLimitExact` and T5 Gram/R278 OS compilers already exist, but need **actual interacting changing-cutoff** source convergence, **literal original Wilson W1/W3** cutoff/volume uniform bounds (or direct spectral construction), published original positive-time RP, and ONE dense reconstructed `H_OS` on nonvacuum physical states with nonzero mass gap. Those are actual E1/D1/D2/N1/G1 physical obligations; no missing finite 1024-link codec, 16-site origin, proof-iteration chronology, or new arbitrary metric/time model. Keep independent physical time `t` and cutoff `k`, actual phase/zero and all 896 physical residual links. P0 YM first; P1 antigravity second.

**Acceptance/branches**: #1536 original golden root imports weighted source [commit 35dadd12](https://github.com/chboishabba/dashi_agda/commit/35dadd12a49902eb7f3cf25ab7b1d06a3e7de55a); `scripts/check_ym_1444_cmp119_r445_weld_forward.py` source owner manifest and local SymPy list updated [commit f37a761a](https://github.com/chboishabba/dashi_agda/commit/f37a761a78415266d8feff7ab87b839a7a85c872). Exact committed script and source-written Agda **not** checked out / kernel executed; independent local equivalent passed. Historical #1444 is stacked; #1536 is master-based, independent; source changes are **not** represented as merged into master or into #1444. Roadmaps updated directly, not replaced.

---

## 2026-11-21 — P0 local SymPy exact F19/native R445, existing PURE-HAAR receiver instantiated as Agda candidate

**Owner-first audit**: newest inspected #1444 historical head `83b2fd9a3ce87b2d91c7b54340183c0723ece965`, latest inspected #1536 master-based head `5e0db1252b1a629642106f5fdfde27bf9bfd98d3`, original `master` `YMClayR445OriginalPureHaarBlockWeldExact`, F19 adjacent-sort, original native 64 SU(N) pair theorem, canonical R445 128+896 full field codec and F19 weighted Wilson effective source. **P0 is the physical 4D interacting mass-gap endpoint E1/D1/D2/N1/G1; finite identity successes are source consistency, not solved continuum analysis.**

**Verified independently in LOCAL SymPy 1.14.0, no CI, no Agda toolchain**: `/mnt/data/check_ym_f19_r445_sympy_purehaar_weld.py`, source-equivalent committed `scripts/check_ym_f19_r445_sympy_purehaar_weld.py` on #1536 ([commit 8e204d70](https://github.com/chboishabba/dashi_agda/commit/8e204d706ccf047749b7719fa6b062faf758205b)). Original side-four 1024 positive bonds, side-two 64 positive coarse bonds, native even origin and two *ordered noncommuting* fine links, original canonical 896-bond spectator filter. Computed **complete 1024-index F19 ↔ R445 permutation**, verified both inverses using SymPy `Permutation`; proved **64/64** original-block equalities in noncommutative symbolic expressions and **96/96** noncommutative coarse plaquette-word equalities; evaluated **5,120/5,120** canonical/sorted exact Q8 (SU2 2×2 matrix) field values, **320/320** ordered pair blocks, **480/480** exact coarse Wilson plaquette traces. Deliberately reversed link ordering differs on **124** of those assigned Q8 blocks; altering one of five original spectators changes an original fine Wilson plaquette word but NONE of the 64 chosen blocked link values. These checks are NOT a full universal SU(N) analytic theorem: the symbolic word equalities are universal in the free-word model; the matrix evaluations are only exact Q8 negative controls. Exact committed GitHub checkout was NOT locally executed (network unavailable from container); local script content follows source-defined geometry but is not byte-verified against committed file.

**Most useful original receiving theorem ALREADY EXISTS**: `YMClayR445OriginalPureHaarBlockWeldExact.OriginalR445PermutationAndNativeBlockWeld` owns (i) actual `Haar.LinkPermutation 1024` matching original R445 complete sorted field and (ii) equality of **original native 64-link SUN holonomy** to its **original flat consecutive 64 ordered SU(N) pair products** on the full 128+896 sorted canonical field. If both are inhabited, its original `originalR445PureHaarBlockedIsOriginalCoarseHaar` proves **unweighted product-Haar pushforward** by existing Haar-invariance and pair-convolution, *not* interacting Wilson Gibbs or bare beta(1) n=1 source equality.

**New source-written, uncompiled direct instantiation candidate** `YMClayOriginalF19R445PureHaarReceiverCandidateExact.agda` ([commit 350273ec](https://github.com/chboishabba/dashi_agda/commit/350273ec3dde467abb6ba8fd3e8d7c10f59a52c9)) plugs in the **actual original `OriginalSort.actualPairProgram`**, transports it through original 1024-count proof by generic exact `transportPermutationAction`, composes #1536 `FullValue.originalPhysicalF19ActualSortIsOriginalR445Codec` for field (i), and composes #1536 `Native.originalPhysicalF19Blocked64EqualsNativeR445` for field (ii). Only remaining source-specific check (not a new axiom) is equality between **F19 `Torus.Product` pairs** from `coarseFromSortedOriginal` and **original pure-Haar `Data.Product` pairs** from `Flat.splitFlatPairs`. Named `originalF19FlatPairBlockAgreement` is currently a **`refl` normalization candidate**, NOT VERIFIED: it might require a source-derived inductive flat-pair decoder bridge and count transport rather than definitional equality. Similarly `originalF19PermutationIsR445Reorder` uses two original count casts that the Agda kernel MUST normalize. The record constructor `originalActualF19PureHaarReceiver` and pure-Haar consequence are **proof candidates**, not accepted theorems. No Agda compiler present; do not call them closed kernel proofs.

**Commuting-square scope**:
```
 original 1024 canonical fine links
    |  original F19 adjacent swaps              | original canonical fine decoder
    v                                           v
 sorted selected128 + residual896       original native R445 SU(N) fine field
    | original 64 ordered F19 pair multiplication | native 2-link selected coarse field
    +-------------------------- SAME 64 coarse links (symbolic/local) ------------+
    | full original 896 spectator variables retained in Wilson integrand
    v
 original existing pure-Haar receiver (UNWEIGHTED, source-specified)
    != full interacting Wilson effective Gibbs, nor all-cutoff physical E1/D1/D2
```
**BIDI follow-up**: first locally test any suspect count transport or pair structure as exact finite SymPy; when Agda is permitted, kernel-check and correct `originalF19FlatPairBlockAgreement` using the original `YMClayOriginalWilsonPairSpectatorDecoderExact`, `YMClayR445FlatPairedHaarIntegrationExact` and `YMClaySUNWeightedDisjointPairFibreReparamExact` inductive pair-product owners; do NOT invent arbitrary function-extensionality or assert `refl` succeeds. Then use the *already existing* `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` for original full weighted Wilson, preserving 896 interacting spectator links. Physical first-order work still E1 original interacting actual measure source and W1/W3 marked uniform small+large-field source (or independent direct same-H D2 argument), RP complex star/dense same (H_{OS}), N1/G1. Chronological R445/F19 theorem numbers ≠ source time `t` or scale `k`. P0 first, P1 antigravity after.

**Integration:** #1536 `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` now imports the source-receiver candidate (commit `283b4799`); its fail-closed local source checker includes original receiver symbols and NEW SymPy local test (commit `acdd2940`). Both #1444 documents and #1536 canonical roadmap are updated DIRECTLY on respective draft branches, no merge into `master` asserted; any formal trust must await actual Agda elaboration when allowed.

---

## 2026-11-21 — NEW P0 F19 → **actual native R445 64 SU(N) block** commuting square, existing pure-Haar interface identified

**User-directed method:** check newest original #1444 and #1536, weld *forward* from existing finite source and *backward* from physical E1/D1/D2 onto the SAME Wilson field. Do not reconstruct parity/measure; preserve all 896 original spectators and the independently indexed physical time `t`, cutoff `k`, signed zero/residual hyperfabric. R445/F19 names are chronology of proof construction, not physical indices.

### The real square, not just a sorted-label equality

```
                 original canonical SU(N) links (all 1024)
                  /                                 \
  actual F19 adjacent-swap into 128+896       original native fine field decoder
           |                                            |
  original F19 pair/spectator decoder           original native R445 2-link holonomy
           |                                            |
  F19.coarseFromSortedOriginal                 SUNBlock.nativeSUNBlockLinks m=l=1
           \                                            /
                SAME 64 original ordered coarse SU(N) links
                           | any original Wilson coarse test
                   SAME finite observable value
```

**Original master sources directly inspected:** `YMClayR445OriginalNativeParityPairWeldExact.originalR445NativeBlockAgreesExplicitParity` proves for **each original coarse bond** the ordered native SU(N) blocked holonomy is the multiplication of original phase-zero and phase-one fine link values; `YMClayNativeSideFourTwoLinkPairSameObjectExact.originalSUNBlockIsLiteralTwoLinkProduct` independently owns the exact path-vs-pair native identity. `YMClayR445CanonicalBondPermutationCodecExact` preserves full **128 selected + 896 original residual** and true two-way original vector codec. `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.coarseFromSortedOriginal` builds the **actual F19 64 pair product** from the original adjacent swap, pair+896 spectator decoder; its `originalCanonicalBlockedNormalizedEqualsPhysicalEffective` already owns same-original-Wilson weighted all-observable normalized expectation, **not bare coarse n=1 Wilson**. The original `YMClayR445OriginalPureHaarBlockWeldExact.OriginalR445PermutationAndNativeBlockWeld` already specifies the **actual** two needed source identities `permutationIsOriginalReorder` and `actualNativeBlockIsFlatPairBlock`; do not replace it with invented Haar assumptions. Existing #1536 F19/R445 full label/field/vector/decoder source remains Agda uncompiled.

**New source-written #1536 native block owner:** `DASHI/Physics/YangMills/YMClayOriginalF19R445Native64HolonomySquareExact.agda`, initial commit `3d769d3ffa7534c9a955fa1a0b3542da2a5d1260` and corrected source `303f2b5ebdf36e5a11a7a7e30532711e4f95277a`, coarse-observable extension `4708a364a988505a9dc2b61631d3aa34a30838d9`. Its `originalNativeCoarse64` encodes the **actual original nativeSUNBlockLinks** on the actual 64 positive-bond enumeration; `originalExplicitParityCoarse64` uses the original two signed-phase source bond lookups; `originalNative64IsExplicitParity64` is a genuine use of **existing source `NativeParity.originalR445NativeBlockAgreesExplicitParity` and `Codec.originalBondsEncodePointwise`**. `originalF19SortedCoarse64` uses the actual F19 `coarseFromSortedOriginal` on the whole R445 128+896 vector. **Precisely one remaining candidate finite computation** `originalF19Sorted64AreNativeParity64` asks for kernel normalization of these exact 64 selected pair products; it is source-written as `refl`, **not compiler accepted**, so if elaboration fails recheck original vector count transport/definitional equality and original pair/64-order proofs, not add axiom. `originalPhysicalF19Blocked64EqualsNativeR445`, `originalF19AndNativeR445Actual64CommutingSquare` and `originalF19CoarseWilsonObservableEqualsNativeR445` compose actual F19 adjacent-sort vector/64 blocked output with original native field, producing **every coarse Wilson test** pointwise **conditional on the closed normalization candidate type-checking**. No synthetic SU(N) block/clock/measure.

**Independent local exact noncommutative test:** `/mnt/data/check_ym_native64_f19_r445_local.py` run against actual original 4D side-four/coarse side-two source-shaped labels and Q8 subgroup of SU(2) (not a Yang-Mills integral), five configurations: **320/320 original native vs F19 pair block products**, **480/480 original coarse plaquette traces**, **160** deliberately reversed two-link products differ, **5/5** spectator modifications change original FINE Wilson plaquette traces while leaving the chosen 64 coarse blocks unchanged. This is a key physical warning: spectators do not enter the 64 two-link holonomies but DO enter the full original Wilson action and cannot be deleted from the interacting measure. The existing #1536 `scripts/check_ym_f19_r445_full1024_labels_p0.py` was committed with independent native/endpoints and fine-spectator Wilson tests as commit `c4632d3aba65d7f7d7809470613f0755d02d1e66`; its exact checkout was NOT run. #1536 golden regression root imports the new Agda owner (`f82f391aab8f3f8af2c8e6de6b4ed93e6c358d53`) and fail-closed source checker requires eight new native/64-source theorem identifiers (`d866a4f67438ce706c976b9aa87010a89923885a`). None is an Agda 2.9 kernel receipt.

### BIDI status / next payment

- **F0 exact finite:** original F19/1024 effective measure and R445 128+896 code/16-site native parity are already provided by `master`; F19↔R445 sorted vectors, pointwise decoder and native 64-block are now *closed Agda proof candidates* on #1536, **not accepted proofs**. Run pinned `bash scripts/check_ym_original_rg_p0_kernel.sh`; repair genuine Agda errors against source definitions. After kernel acceptance, instantiate the already-existing original `OriginalR445PermutationAndNativeBlockWeld` with the actual F19 adjacent-sort and native 64 theorem; avoid another Haar theorem.
- **F1/R1 physics:** original actual compact `SU(N)` Wilson all-size changing-cutoff interacting Gibbs/E1 (not one side-four sample), original W1/W3 **literal Wilson-loop** small/large field marked locality and cutoff/volume uniform exponent, actual original CMP119/122/116 sources and same real/rational carrier interpretation. Existing conditional generic CMP theorem machinery DOES NOT supply the physical data automatically.
- **F2/R2 OS time:** original positive-time Wilson words, reflection-compatible actual link source, published Wilson reflection positivity **complex-star** source; R332 OS1 time and R556/R278 actual same-source cutoff-indexed covariance. Preserve original `t×k` + residual and real physical units.
- **F3/R3:** original E1 interacting continuum/nontriviality + one **actual same reconstructed H_OS**, dense vacuum-orthogonal cylinder family, uniform positive mass (m), G1 group scope. No finite commuting square or Q8 check proves Clay mass gap. P0 YM first; P1 antigravity second.

**Branch discipline:** roadmaps updated DIRECTLY on historical stacked draft #1444 and independent master-based draft #1536. This entry is source-specific implementation status, not a merge into `master`.

---

## 21 November 2026 — P0 F19↔R445: a TRUE *finite decoder* commuting square, plus the physical blocked-observable corollary

**Question answered precisely:** the earlier `P_F19(U) = Encode_R445(U)` is an equality of parallel routes from ONE original canonical 1024-link vector to ONE complete 128-selected+896-spectator vector. It is **not itself a four-arrow commuting square**, and it is **not yet** a Yang–Mills OS/continuum/RG commuting theorem. The genuine square is now stated explicitly, with original source-owned maps only:

```
       actual original CANONICAL Vec 1024  -- P_F19 original adjacent swap -->  sorted Vec 1024 (128+896)
                      |                                                            |
       Codec.decodeOriginalBonds 4                                 Codec.decodeField originalR445PairResidualFinite
                      |                                                            |
                      v                                                            v
             original full fine bond field   ------------ IDENTICAL ------------> original full fine bond field
```

Precisely **for every original positive fine bond and arbitrary Value**, `decode_R445(P_F19(U),bond) = decodeOriginal(U,bond)`. On **independent draft #1536** this is implemented source-written as `YMClayOriginalF19R445DecoderCommutingSquareExact.originalFull1024DecoderSquare` ([commit 373707dc](https://github.com/chboishabba/dashi_agda/commit/373707dc293f288c7bce156cb4aea6a4243939c9)). It composes existing original master `YMClayNative1024ClosedReindexHaarConsequencesExact.actualPairSpectatorReindexEveryOriginalVector`, `YMClayR445CanonicalBondPermutationCodecExact.decodeEncodeAt`, and #1536 `YMClayOriginalF19R445Full1024LabelsP0Exact` **full label equality candidate**. **Both inverses** are stated: unsort after F19 sort restores original canonical vector, and F19 sort after R445 unsort restores any complete sorted vector. These use already-written R445 original two round-trip theorems. The actual proof body depends on older source-written `refl` candidates and is **NOT Agda kernel accepted**.

A second, physically more meaningful **finite blocked-observable** corollary on #1536 uses the REAL original `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.coarseFromSortedOriginal` and `canonicalSourceCoarseObservable`: the **same** original canonical Wilson U under the REAL F19 constructed adjacent-swap sort or under the original R445 complete selected+residual coordinate reorder yields the **same 64 physical F19 coarse SU(N) holonomies** and every original F19 coarse Wilson observable. New source `YMClayOriginalF19R445PhysicalBlockedObservableSquareExact.agda` ([commit 4bdc52f7](https://github.com/chboishabba/dashi_agda/commit/4bdc52f73f652e3c56f42216e0f79c6f05fa1f39)) composes original F19 block and preceding vector theorem by `cong`. This is **not** a duplicate measure, alternate block or invented Haar. Full 896 spectators retained in the original 1024-link vector.

**The precise downstream junction is still different:** compare the above original F19 `coarseFromSortedOriginal` **coarse Vec 64** with the already ORIGINAL `YMClayNativeSideFourTwoLinkPairSameObjectExact.originalSUNBlockIsLiteralTwoLinkProduct` and `YMClayR445OriginalNativeParityPairWeldExact.originalR445NativeBlockAgreesExplicitParity` original `nativeSUNBlockLinks` on EACH of 64 coarse bonds, with original enumeration order. This is a **native blocking-square**, not the lossless decoder square, and must be kernel-accepted before claiming full F19 ↔ native-R445 blocked observable identity. Original F19 `originalCanonicalBlockedNormalizedEqualsPhysicalEffective` already gives full finite 1024-link Wilson normalization for every coarse test, but does NOT automatically imply original cutoff-uniform Wilson W1/W3 physical decay, E1 continuum or same-H OS.

**Acceptance and falsifiers:** local independent finite Q8 reference `/mnt/data/check_ym_f19_r445_all_link_values_p0.py` actually executed: 128/128 selected, 896/896 spectators, 2048/2048 inverse, five 1024-link Q8 configurations 5120/5120, 320/320 noncommutative pair holonomies, 7680/7680 original Wilson plaquette-trace invariance. Intentional reversed within-pair order changes 160 blocks; modifying each of five spectators changes the original field (5/5). This is *not exact checked-out head script or Agda kernel acceptance*. New source modules imported in original golden root `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, and fail-closed `scripts/check_ym_1444_cmp119_r445_weld_forward.py` manifests both. Existing `master` source was inspected; historical #1444 and master-based #1536 remain **separate draft PRs**.

**P0 theorem-first unchanged**: actual original interacting four-dimensional YM E1 limit/nontriviality, original full Wilson W1/W3 physical small+large-field cutoff/volume-uniform decay (or another direct same-H gapped reconstruction), published fine physical RP, one dense physical OS Hilbert/H generator and full vacuum-complement spectrum D2, N1/G1 group scope all remain OPEN. No finite coordinate-square counts as the Clay mass gap; P1 antigravity after P0. R443/R445/R320 are chronological proof attempts, not physical t or RG k. Preserve zero and all parity and 896 physical residuals.

---

## 21 November 2026 — latest-head P0 F19/R445 *arbitrary original link values* commuting square; physical theorem remains governing target

**Review order actually followed:** checked #1444 head `583b063c5c18b56a046b22749127134c11890d76` and its two existing roadmaps, #1536 master-based starting head `0016ed414b9acfcecafffd4660ac9391a887c221` and its canonical roadmap, plus the exact `master` original F19/R445/vector/Haar owner bodies. #1444 is stacked on `research/ym-route-s-r320-direct-mass-gap-20261030`; #1536 is 64 ahead / 0 behind `master` at inspected prewrite comparison. Other newest #1537/#1538 are different research lanes, **not newer substitutes for the original YM Wilson source**. Re-read current heads before future imports; chronology R445/F19/R320 is theorem iteration, NOT scale k or physical time t.

**Already original master sources, therefore NOT new P0 missing constructions:**
- `YMClayNativeSideFourPairSpectatorSortProgramExact`: native adjacent-swap F19 target is **original 64 ordered pairs plus canonical 896 spectators**.
- `YMClayNative1024ClosedReindexHaarConsequencesExact.actualPairSpectatorReindexEveryOriginalVector`: original source-generated F19 adjacent-swap permutation reads **arbitrary original link values** via original 1024-link decoder. Finite product-Haar reindex is likewise source-owned; interacting Wilson weight stays in integrand.
- `YMClayR445CanonicalBondPermutationCodecExact.originalR445CanonicalToPairResidual` + **two round-trip theorems**: existing original complete selected-128 / residual-896 field reordering.
- `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective`: full original interacting F19 1024-link normalized effective expectation for **every** original coarse observable, already existing. Prior #1536 `YMClayOriginalF19R445Full1024LabelsP0Exact` is a **source-written, not kernel-accepted** full 1024-order candidate.

**New actual vector commuting square on independent draft #1536, not merged onto #1444 or master:** `YMClayOriginalF19R445EveryLinkValueBIDIExact.agda` (`7921880be20f8dc642d05af4d3bb5087633dd8df`) transports original complete F19/R445 label equality through original `Codec.listValues/encodeField` for every value carrier and every original 1024-link canonical vector. `YMClayOriginalF19R445ActualSortedVectorBIDIExact.agda` (`44fbcc4e7203db739017389da3fbe7552e965e6e`) composes **master's actual F19 adjacent-swap `actualPairSpectatorReindexEveryOriginalVector`** with that full-label equality to state:
```
Haar.permuteLinks (Sorted.actualPairProgram theory) original1024
   == R445.originalR445CanonicalToPairResidual original1024
```
for **every** link value carrier, then by congruence for every consumer of that sorted vector. This is a SAME original finite source, including all 896 interacting spectators; no new Wilson measure/action/clock/H. Both new files are **Agda proof candidates, UNCOMPILED**, transitive dependencies include earlier closed `refl` candidates and the #1536 896-spectator equality; compiler acceptance is a hard dependency, not inferred from text.

**Regression correction**: old `check_ym_f19_r445_full1024_labels_p0.py` “inverse” wrote each canonical position back to itself (tautology). The updated committed script `4cbf50eae094716a221d86a530e9e65d1dace12e` now computes real **canonical-index→target-index inverse** and checks both permutations. It also exercises full original 1024-link fields over five noncommutative Q8 SU(2)-subgroup assignments, all 64 ordered blocked products, and original interacting spectator negative control. An independently executed, more extensive local source-shaped regression passed **128/128 selected, 896/896 spectators, 2048/2048 forward/inverse, 5120/5120 link values, 320/320 ordered Q8 blocks, 7680/7680 original Wilson plaquette traces**, reversed-pair Q8 difference **160** and five altered-spectator source differences. The exact modified GitHub checkout checker was NOT run; those are **equivalent local reference** results, not pinned Agda or exact-head Python receipts.

**P0 steelman BIDI next payment (theorem-first):** distinguish (A) pending **kernel acceptance** of finite F19↔R445 ordered target/adjacent-swap source equality from (B) genuinely open physical **E1** interacting 4D Wilson continuum and published complex-star reflection positivity, **D1** original full Wilson W1/W3 small+large-field `a,V`-uniform physical covariance rate (or another direct gapped-reconstruction proof), **D2** ONE actual dense vacuum-orthogonal `H_OS` with full nonvacuum positive gap, and **N1/G1**. The next candidate exact handoff is original `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.coarseFromSortedOriginal` to **original** `nativeSUNBlockLinks` on the same SU(N) field, then instantiate existing real original E1 three-moment residual/W1/W3 producers. Do not build another finite codec or metric. R445 16-site origin, all-coarse normalization, 896 spectator order and E1 limit *interfaces* are already owned; their physical analytic hypotheses remain actual obligations. P1 antigravity second.

**Acceptance:** original 1444 roadmaps updated **in place** and #1536 canonical roadmap synchronized. Changes are committed and read back, but **Agda/Nix kernel not installed; all new Agda is source-written/unverified**. No Clay physical mass-gap completion claimed.

---

## 21 November 2026 — P0 original F19 canonical Wilson NORMALIZATION/COVARIANCE already paid; source-native R445 ordered-target seam narrowed

**Source-first reverse solve / no reinvention.** Direct GitHub readback of five **exact source Agda files on BOTH** master and #1444 confirms **bytewise/blob-SHA identical**, not merely similar names:
`YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.agda` SHA `18e8cdb65edcceaf15fbf627eb99b90d51b9bd6a`,
`YMClayOriginalWilsonPhysicalF19PartitionExact.agda` `470bdd191c57d3a98d2e5a785f113abc4592be5e`,
`YMClayF19OriginalAllCoarseCylinderNormalizationExact.agda` `dfb5c8fb8615add9aa2b41dbbef08b3d3b53e7cc`,
`YMClayE1OriginalR445ThreeMomentCutoffTransportExact.agda` `3217c4e7a56bae1c94474107dbcba2bc7ac2ed03`,
`YMClayR445OriginalNativeParityPairWeldExact.agda` `c5a1a2d9d7dd9044a770e1e50e396c495e4569eb`.
**Already source-written on master/#1444**: canonical original 1024-link Wilson Gibbs Haar marked numerator is the original 64-pair/896-spectator physical effective numerator for EVERY coarse observable; `originalCanonicalBlockedNormalizedEqualsPhysicalEffective` proves equality after the ORIGINAL canonical partition, not an independent bare n=1 normalization. `originalFinePhysicalPartitionEqualsActualEffectivePartition` and original `originalPhysicalF19TwoMarksNormalizeByCanonicalPartition` already carry full physical spectator coupling. `YMClayF19OriginalAllCoarseCylinderNormalizationExact.originalF19AllCoarseNormalizedSamePhysicalSource` already proves a separate all-coarse F19 equality. **These are ALREADY constructed finite F19 results**, source-written/unverified locally by pinned Agda; remove false “missing F19 all-coarse original normalized identity” from active frontier.

**New *composition*, not a new measure**, on independent master-based #1536: `YMClayOriginalF19CanonicalConnectedWilsonBIDIExact.agda`, commit `c8663700a540607258648bc24e9df1bc647e7365`, takes the original named `canonicalOriginalWilsonExpectation` and `originalF19EffectiveWilsonExpectation` from `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact`, uses original SAME normalized equality on `F`, `G`, `FG` and ordinary `cong₂` of multiplication/subtraction, and constructs:
```text
Cov_actual_original_1024_Wilson_canonical(F,G)
  = Cov_original_F19_64_pair_896_spectator_effective(F,G)
```
Both are the ORIGINAL **real `ℝ`** Wilson expectation under the same canonical partition, NOT a rational surrogate or new Marked J. This is exact finite three-moment/covariance transport for any source-owned 64-link coarse tests. No E1/R445 across ALL cutoffs, analytic W1/W3 estimate, physical RP/OS spectrum or full mass gap follows.

**Original F19 vs R445 selected-order proof**, #1536 `YMClayOriginalF19NativeR445SelectedOrderBIDIExact.agda`, commit `c71a29e722a422003aada57b9232a7cdf99d364d`: imports ORIGINAL `YMClayNativeSideFourPairDistinctCertificateExact.selectedFinePairLabels`, ORIGINAL `YMClayR445OriginalNativeParityPairWeldExact.originalR445NativeFirstBondIsParity` and `originalR445NativeSecondBondIsParity`, ORIGINAL `YMClayR445CanonicalBondPermutationCodecExact.originalSelectedEncode/originalR445SelectedBondEnumeration`. A structural list induction proves the F19 **two fine positive bonds per original coarse bond** equal the R445 parity `phase=0,1` source IN THE SAME ORDER, for ALL original 64 coarse positive bonds. No replacement native `Fin.combine` map, no assuming commutativity and no arbitrary permutation. Proof is source-written, **new Agda kernel not executed**.

**Local exact reference**: recreated BOTH original list-construction algorithms from the inspected source on the 4D side-four/side-two periodic torus, and independently verified ordered **128/128 selected F19↔R445 labels**, ordered **896/896 spectator suffix**, **1024/1024 full bijective reorder/inverse** and **64/64 native ordered pairs**; the deliberately reversed pair order fails **128/128** comparisons. The source-equivalent check is committed as `scripts/check_ym_original_f19_r445_selected_residual_source.py` on #1536, commit `10e282b975f3ea645b078d21a1535adb74a2c1ad`. It is a finite executable reference, NOT the Agda proof of the two independently defined 896-spectator filters or whole 1024-label vector equality. Current #1536 source checker/golden root import both new theorem owners; no pinned Agda receipt.

**Shortest REAL remaining native/source junction** is **full target-Vec equality** between original `YMClayNativeSideFourPairSpectatorSortProgramExact.originalPairSpectatorTargetVector` (native adjacent-sort program, ORIGINAL selected+remaining) and `YMClayR445CanonicalBondPermutationCodecExact.originalR445PairResidualBondEnumeration`, including exact **896-spectator order**, followed by source-word identification of `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.coarseFromSortedOriginal` with original `nativeSUNBlockLinks` under native decoder. The **finite F19 partition, all-coarse normalized expectations, native 16-site origin and selected 128-link order are no longer the proof targets**. Then plug the original real Wilson same-source 3-moment into existing `YMClayE1OriginalR445ThreeMomentCutoffTransportExact`, CMP119 Wilson W1/W3, R332 OS1 and original E1/T5 physical Gram continuum. Physical uniform small+large-field Wilson shell estimates and same reconstructed H remain real open analytic inputs, not a generic toy obstruction. R443/R445/R320 numbers are chronological owner iterations, **not** Euclidean t or RG k. Retain original zero, odd/even phase, 896 spectator links and the distinct signed trit wave symbols.

**Branch/control**: this note updates the #1444 canonical and Steelman BIDI roadmaps DIRECTLY; #1444 is stacked draft, while implementation is on distinct #1536 master-based draft. Do not claim source commits merged into #1444/master; do not promote the new uncompiled source to the Clay gap. P0 before P1.

---

## 21 Nov 2026 — canonical master cross-check: six original owners

**Correction to missing-theorem language:** exact blob-SHA readback found **6/6 original YM theorem owners byte-identical on this #1444 branch and current `dashi_agda@master`**: `YMClayOriginalR445ReflectedAllWordGramExact`, `YMClayOriginalR445PublishedWilsonRPWordWeldExact`, `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact`, `YMClayD1OriginalCovarianceToR320Exact`, `YangMillsClayCriticalPathRound578Exact`, `YangMillsClayCMP119H1OS4AttachmentRound583Exact`. Do not relabel original same-measure finite R445/R320, arbitrary finite reflected-word algebra, conditional published RP transfer, R320 finite covariance source, seven-family critical path or H1→OS4 compiler as absent.

**Conditional does not mean inhabited:** `sourceIdentifiesActualWilsonReflection`, physically uniform cutoff/volume full Wilson W1/W3 estimates, actual E1 interacting continuum OS measure, same full H_OS and dense vacuum complement, genuine N1 and all-group G1 remain physical source obligations. CMP102 is limited to actual nonlinear average + mixed-scale shell support and per-plaquette Eq7, not another general Haar/plaquette construction.

**Branch lineage:** this PR is stacked on the historical `research/ym-route-s-r320-direct-mass-gap-20261030`; `master` is the default branch (not `main`). The **master-based** follow-on #1536 owns new OS1/R556 and fine↔coarse time × k residual commuting-square source, not merged here. Keep indexed physical time t, RG scale k, proof-iteration labels, signed zero trits and actual 896 field residuals distinct. No Agda kernel or Clay promotion from source text / finite regression.

---

## 21 Nov 2026 — P0 R445 **time × RG stage k** reversible hyperfabric; exact original source recheck correcting false outstanding gates

**Latest correction to the earlier BIDI/commuting-square audit**: The original #1444 `master` tree already owns exact **C4 ↔ (C2 coarse, C2 even/odd residual)**, actual native 16-site `Fin.combine` even origin, and **128 selected + 896 residual = 1024 source SU(N) positive links**. These are NOT missing new YM geometry or an unsourced toy carrier. We have now inspected the ORIGINAL source Agda bodies and reattached to their existing owners.

### Original source owners and what is actually paid

- `YMClayR445OriginalAxialBondParityInjectiveExact.agda` owns `coord : Bit→Bit→Quad`, `coarse`, `phase`, `even`, `coarseCoordRoundTrip`, `phaseCoordRoundTrip`, `originalR445SelectedFineBond`, selected-positive-bond source injection and round-trip. The exact finite 4↔(2×2) coding (including coarse zero and odd phase) was **already constructed**.
- `YMClayR445OriginalNativeParityPairWeldExact.agda` already defines `originalR445NativeOriginIsEvenSite` (16 original coarse sites, `refl` cases) for the ACTUAL original `Block.fineBlockOrigin`, `originalR445EvenSiteOneStepIsOddPhase` (8 source-axis parity cases), and `originalR445NativeBlockAgreesExplicitParity` on the genuine SU(N) native 2-link holonomy. DO NOT re-prove the 16-case native block origin or say it is the next missing theorem. Only the selected **reflected/translated field** square under this source's mirror and positive-time grammar may need actual Agda compiler acceptance.
- `YMClayR445CanonicalBondPermutationCodecExact.agda` constructs literal **64 coarse bonds × 2 selected phases = 128**, retains the remaining **896** original fine bonds, and proves disjoint/complete selected+residual enumeration; `YMClayR445OriginalFullWilsonFiberDensityExact.agda` already consumes that exact original decoder to form the **full interacting 1024-link Wilson Gibbs weight**, not just the 128 selected part. Keep the 896 residual even when deriving coarse blocks; the even/odd **C2 time remainder is a DIFFERENT residual** from those 896 link variables.
- `YMClayE1A3OriginalR445CrossCutoffSourceExact.agda` already gives same-object E1 original n=3 blocked Wilson expectation = R445 **effective pushed-forward** coarse expectation, but *not* equality with independently bare n=1 Wilson source. `YMClayE1OriginalR445ThreeMomentCutoffTransportExact.agda` already transports original n=3/1 E1 three-test moment residuals into the true R445 connected-covariance/RG error compiler. Those are **chronological proof-iteration achievements**, not physical time indices.
- `YMClayE1VariableCutoffCylinderLimitExact.agda` already has an E1 continuum-labelled cylinder observable with `realization : ∀ cutoff → Observable→Configuration cutoff→Scalar`, original changing-link carrier by `cutoff : Nat`, selected scalar convergence, and proofs of continuum positive/normalized/linear expectation **once actual original Wilson source convergence is provided**. Do not say finite→continuum theorem machinery is absent.
- `BalabanClayT5LimitAndNontrivialityExact.agda` already owns finite→continuum OS closure requiring full reflected Gram convergence, and nontrivial fourth cumulant source witnesses. `BalabanClayT5PhysicalMeasureGramContinuityExact.agda` owns the direct original finite Gram→limit proof compiler. `BalabanGaugeInvariantWavefunctionFiniteL2Round203Exact.agda` owns finite rooted gauge-invariant wavefunction sample pairings, explicitly NOT a full Haar/Gibbs Hilbert theorem.
- General shared finite/wave/recovery sources `DASHI.Core.MultiscaleMDL` already provides `ResidualCodec`, `split`, `join`, `join-split` at every k; `DASHI.Physics.WaveAlgorithmLift` already has balanced-ternary `neg,zero,pos`, zero amplitude, sign involution, and `WaveRefinementTower`; `DASHI.Physics.Limits.PhysicsLimitCommutingSquare` already has `ExactCommutation`, `ResidualControlledCommutation`, `AsymptoticCommutation` **with a stage-indexed residual-to-zero obligation**. Existing `FiniteToContinuumGeometry` concerns *different Lorentzian geometry* and generic `ShiftWaveScalingInterface` explicitly says its two levels are identity packaging, not a continuum PDE. Do NOT promote those to proof of original 4D YM wave/OS continuum.

### 21 Nov further source weld: actual E1 time × k finite-to-continuum adapter, no false tail law

On master-based draft #1536, `YMClayE1TimeKResidualCylinderWaveTransportExact.agda` (commits `ccf0259d06a68dc4bcbb372b12b8825e04415b3f`, **corrected** `0da5d6d299cd5284502cbb8a963da0e543ef70bf`) directly consumes ORIGINAL #1444 `YMClayE1VariableCutoffCylinderLimitExact.CylinderRealization` and `ActualVariableCutoffCylinderFamily`, instantiated on the already-original `DASHI.Core.MultiscaleMDL.MultiscaleCarrier` and `ResidualCodec`. Independent (t) is a **supplied original Euclidean-time word translate** (still needs same-object OS1/R332 identification), (k) is the *exact* original cutoff `Nat`. `timeKOriginalCylinder t k word fine` evaluates the original selected cylinder on `Configuration k`; `timeKOriginalCylinderRetainsResidual` uses EXISTING `MDL.join-split` at `suc k` to prove the same original observation is unchanged by reversible coarse+residual decomposition. The original **physical measure** stays `E1.finitePhysicalMeasure k`, not an arbitrarily invented fixed C2 carrier.

`timeKOriginalWilsonExpectation t k word` is literally `E1.finiteExpectation original k (timeTranslate word t)`; the named selected original `E1.originalWilsonConverges` proves convergence to `E1.continuumExpectation original (timeTranslate word t)` **if the original physical family is inhabited**. IMPORTANT: no unjustified reindexing `Converges (λ k → f (suc k))` from arbitrary `Converges (λ k → f k)`—the first candidate was immediately corrected before kernel claims. This is a real proof composition through already-supplied finite-to-continuum machinery, **not** a proof that the uninhabited original physical E1 measure/OS/W1/W3 source has appeared.

User geometry retained: (t) time, (k) source refinement, (a\in C_4) selected finite time coordinate; C2 parity remainder remains reconstructible, balanced trit zero/sign is not a C2 time parity, and original 896 Wilson links are not thrown away. `YMClayR445TimeKResidualHyperfabricExact.oddFineStepCannotFactorThroughCoarseOnly` now **formally states the exact negative control**: there is no coarse-only (C_2→C_2) one-fine-time-step action because original fine 0 and fine 1 have the same coarse address but different coarse successors. Yet `oneFineStepKeepsCarryAndResidual` **does** lift every original one-step motion when remainder is retained. This fixes the earlier overbroad phrasing “odd translation does not descend”: it fails only after *forgetting residual*.

All new Agda source is committed/readable on #1536 but remains UNCOMPILED; local finite Python reference genuinely PASSED 8/8 chart and 13,068/13,068 indexed reconstructions. Do not promote scalar/wave→physical SU(N) or E1/H-gap from index identity. The explicit same-source physical leaves remain original CMP119 Wilson W1/W3, E1 measure convergence, published RP/Gram, real↔rational source, physical uniform decay and same-H OS spectrum.


### Time-and-k indexed hyperfabric, ZERO and all residuals retained

**Independent indices**: `t ∈ ℕ` = chronological Euclidean translation from the original OS1/R332 source; `k ∈ ℕ` = changing-cutoff/RG *scale* index (not the source file number R445); `a ∈ C₄` = concrete finite-side-four periodic time coordinate; `σ ∈ {−1,0,+1}` = OPTIONAL original finite-wave signed/zero phase code; `r ∈ C₂` = actual original time parity residual. **Never treat R443/R445/R320 theorem labels as `k`**, nor conflate a C2 parity with ternary signed zero, nor collapse the full 896-link physical residual.

Existing original `coord/coarse/phase` gives an exact **set-coordinate bijection**, not a time-translation group isomorphism, `C₄ ↔ C₂ × C₂` with `a = 2c + r`, including zero `(c,r)=(0,0)`. Native one-step time transport in these coordinates is
`(c,0) → (c,1)`, `(c,1) → ((c+1) mod 2,0)`.
Thus **a one-step fine translation does not descend through coarse-only C2**, but with *original phase residual retained* it transports **exactly** with nontrivial carry. Two fine steps give `(c,r) → ((c+1) mod 2,r)`, recovering the existing commuting square; NO discarded odd shift or erased residual. The finite C2 time periodicity `T_c² = id` is real, so only the SOURCE changing-cutoff/OS1 family, not that fixed torus, represents all physical times.

**New master-based #1536** `YMClayR445TimeKResidualHyperfabricExact.agda` now **imports original `OriginalCodec.coarse/phase/coord` and `OriginalNativeOrigin.originalR445NativeOriginIsEvenSite` rather than rewriting their proof**, constructs exact `joinSplitNativeTime`, `splitJoinNativeTime`, `originalNativeBlockOriginIsSelectedGeometry` by reusing original 16-site source theorem, `oneFineStepKeepsCarryAndResidual`, `twoFineStepsExactlyDescend`, `zeroIsARealNativeState`, `waveZeroIsNotDeleted`, `indexedZeroModeIsExactFiniteZeroWave`, `timeKScaleResidualRoundTrip` from the original `MultiscaleMDL.ResidualCodec` and uses original `originalR445PairResidualFinite` exact complete **128+896** fine-bond source. The `TimeKFiniteWaveCell` stores `(t,k,a,σ)` independently; neither the symbolic `Wave.encodeTritWave` nor the generic codec is automatically the physical SU(N) Wilson continuum. The 128/896 links are *interacting field variables* not automatically a split into independent statistical factors.

**Locally executed finite exact reference** `scripts/check_ym_r445_time_k_residual_hyperfabric.py`: **8/8** round-trips for 4 finite states and 4 coarse-residual pairs, **4/4** carry and **4/4** two-step source identities, **13,068/13,068** independent `(t,k,a,σ)` record reconstructions for (t,k=0…32), (sigma=-1,0,+1), zero retained; negative control: coarse-only cannot know whether shift past original 0 or original 1 crosses an even block. Original source 128+896+1024 count verified, but rigorous disjointness/completeness comes from **already original Agda owner**. **Agda kernel acceptance not run**.

### Strongest existing finite→wave/continuum physical producer chain, not a new one

`original Wilson 1024-link E1 n=3/1 source + R445 native full selected+residual effective density`
→ `E1A3 exact blocked/effective same source`
→ `E1OriginalR445ThreeMomentCutoffTransport` (three-test RG residual)
→ `E1VariableCutoffCylinderLimit` (changing-cutoff continuum-labelled cylinders with explicit genuine convergence)
→ `T5PhysicalMeasureGramContinuity + T5LimitAndNontriviality` (whole reflected-OS-Gram convergence/OS existence when physical hypotheses are inhabited)
→ `R332 OS1 Euclidean translation + R556/R278 Wilson covariance convergence + R281 same-H spectral consumer` (source physical W1/W3 and H identification still genuine inputs).
Generic `WaveAlgorithmLift` contributes **reversible zero/sign finite chart**, not automatically the interacting Yang–Mills measure, infinite-time OS semigroup, physical wave equation or cutoff rate. `PhysicsLimitCommutingSquare.AsymptoticCommutation` says **retain (r_{t,k})** and control its real source value, prove convergence to zero only if applicable, NEVER replace by (r=0) or discard by quotient.

**Source status correction**: the old list marking original R445 native origin, finite residual decoder, or existence of a finite-to-continuum *interface* OPEN is inaccurate: these have named source owners. Still **unpaid physical source** are selected real/complex Wilson→CMP119/T5 same-family measure/scalar correspondence, literal Wilson W1/W3 physical two-support cluster rates (published bond-valued J does not automatically imply loop bounds), cutoff/volume-uniform small+large-field estimates, published RP positive-time complex star, an interacting OS E1 limit/nontriviality, one reconstructed H with dense vacuum-complement states and physical mass scale. Do not infer Clay gap from finite-wave code or the filename chronology. **P0 YM first; P1 antigravity next.**

**Cross-PR discipline**: #1444 is STACKED historic Voyager PR; #1536 is independently master-based, remains draft; #1444's roadmap is updated in place here, **new implementation has not been merged into #1444**. Both must be read back and new native Agda must be kernel-checked before promotion.

---

## 21 November 2026 — P0 commuting-square BIDI audit (#1444 roadmap synchronization with master-based #1536)

**WELD, DON'T REBUILD.** This is the original Yang–Mills source-first, steelman BIDI programme. Reverse from one reconstructed physical OS (H) and its time-translated Wilson covariance; plug forward from the **already existing** CMP119/122/116, original side-four SU(N) Wilson Gibbs, R445/R320 and R332/R556/R551/R281 donors. The actual R445/OS1 commuting-square implementation lives on **[draft PR #1536](https://github.com/chboishabba/dashi_agda/pull/1536)** based on `master`; #1444 is a stacked historical Voyager branch. **This documentation entry does not assert that #1536 source has been merged into #1444 or master.**

### Square 1 — original 4D Wilson lattice link blocking, reflection and compatible translation

The actual native `B: U_4→U_2` is an **ordered two-positive-link SU(N)** holonomy from the original original 4⁴ periodic 1024-bond Wilson fine source. For fine time translation `T_f`, coarse time translation `T_c`, original even-origin block and site reflection `θ`:

```
             T_f^(2k)
 U_f --------------------------> U_f
  |                                |
  | original B (2-link SU(N))      | original B
  v                                v
 U_c --------------------------> U_c
             T_c^k

             θ_f
 U_f --------------------------> U_f
  |                                |
  B                                B
  v                                v
 U_c --------------------------> U_c
             θ_c
```

**EXACT tested universal noncommutative free-word relations**: `B T_f^(2k)=T_c^k B`, `B θ_f=θ_c B`, and `θ_f T_f^(2k)=T_f^(-2k) θ_f` (coarse analogue). Locally ran independent `/mnt/data/check_ym_original_r445_os1_translation_square.py`: **576/576** shifted coarse-bond equalities over nine k values, **64/64** reflected-block bonds, **9216/9216** fine time dihedral comparisons. **Negative controls**: `T_f^1` does **NOT** descend to `T_c^1` on the selected even-block source (**64/64 mismatches**); finite coarse time C2 wraps `T_c^2=id`, so times t and t+2 alias. These are *not* claims of full Agda kernel acceptance or continuum time symmetry.

**Source-written Agda #1536** `YMClayR445SelectedTimeReflectionForwardExact.agda` adds `selectedNativeSiteTimeSquare`, `selectedFineSiteReflectShiftDihedral`, `selectedCoarseSiteShiftHasPeriodTwo` on actual Torus C4/C2 site-index forms. The link-field-level identification with the **actual** `Native.fineBlockOrigin` / `nativeSUNBlockLinks` is **still an explicit selected native `Fin.combine` proof payment**. Reuse original `YMClayNativeR445TemporalReversalExact.originalSUNTimeReversalTwoLink` and `YMClayNativeSideFourTwoLinkPairSameObjectExact`, not duplicate its non-Abelian group theorem. Choose OS-positive reflection plane from ORIGINAL published Wilson RP support, not from an arbitrary site mirror.

### Square 2 — one OS1 Euclidean translation, actual R556 covariance, R278 limit, one R281 spectrum

```
       same selected Wilson pair (F,G), time t
                     |
            original R556 index ((F,G),t)
            /                      \
 source T5/R556 τ_tG           OS1/R332 τ_tG
            \                      /
       finite original *same* R278 covariance at cutoff n
                 | R278 convergence
       ONE original continuum covariance
                 | R281 same all-pairs/time index
       ONE R281 spectral connected correlation
              (not yet actual H_OS)
```

**Source-written #1536** `YMClayOriginalWilsonOS1R556R281CommutingSquareExact.agda` proves source-side `originalWilsonTimeTranslationSquare` from original R332/R556 selected geometry witnesses, `originalFiniteCovarianceSquare` at every cutoff under the **same** `Gram.measureSequence`, `originalContinuumCovarianceSquare` under the **same** `Gram.continuumMeasure`, and `originalOS1SquareEndsInSameR281Spectrum` using the ONE all-pairs/all-times R281 index dictionary `indexFor spectrum a t = ((F,G),t)`. The vertical arrow is existing `R278.selectedConnectedCovarianceMagnitudeConverges`, **not finite=continuum equality**; arbitrary `Converges` also needs a sequence-congruence law before freely replacing equal-pointwise functions (no invented funext).

**Key BIDI correction:** *a common index family alone does not prove a commuting physical square*. The original source-time map must agree with `OS1.translate`, the selected R556 physical shell distance must agree with the source R304 time-distance carrier, the exact original Wilson measure must match the chosen CMP119/T5 state at each cutoff, and the R281 object must be the **one physically reconstructed H_OS**. Finite fixed C2 time cannot model all `Nat` Euclidean time; the R332/R556 all-time source is a **changing-cutoff/continuum carrier**, not the side-two blocked torus. R349 already owns related selected R318↔R284 distance comparison; reuse it rather than invent a time theorem.

### Existing producers and surviving honest payment

- `BalabanLiteralWilsonMarkedLocalizationSourceExact` → R556 uses original literal Wilson W1 (actual mixed marked derivative) and W3 (two-support rooted-shell bound); **their physical original Wilson source inhabitants, small+large fields and uniform cutoff/volume estimates remain open**, notwithstanding already existing CMP119 anchored insertions, CMP122 boundary reinjection and CMP116 conditional localization. Printed CMP116 bond-J is NOT identical to Wilson-loop insertion by name.
- Earlier `WilsonWEXTDownstreamSemantics` quantified over *every arbitrary metric*, making it vacuous on any inhabited observable type (`d≡0, t=1` yields `0=1`). #1536 surgically corrects **both existing consumers** to use their **selected physical distance**, and records exact negative-control theorem `universalTimeForEveryDistanceIsImpossible`. This is a type error repair, not newly proved physical decay.
- The finite original **real** n=3 R445/R320 mixed-J/centered reflected pairing and the **rational** R575/T5/WEXT R556 carrier must still be identified by a faithful actual physical scalar/measure/observable interpretation. Use existing `YMClayP0BishopToOriginalWilsonRealWeldExact`, `BalabanCMP109116BishopRealSetoidInstantiationExact` and rational→real `RationalRealRingEmbedding` donors; do **not** assert an automatic real→rational equality or a second Gibbs source. Fixed finite R445 n=3 does not by itself supply an all-cutoff OS1 physical time state.
- **P0 physical open**: published Wilson fine RP on selected positive-time (complex star), original Wilson W1/W3 analytic insertion/locality on actual small+large-field Gibbs, original E1 interacting/nontrivial continuum, source-consistent cutoff-uniform physical rate, one dense vacuum-complement Hilbert/H_OS and same correlation/spectrum identification, G1 all groups. **P1 antigravity later**.

**Acceptance/trust:** exact local tests PASS as specified; new #1536 Agda sources **not pinned-Agda-kernel checked**. Existing `scripts/check_ym_original_rg_p0_kernel.sh` is the local toolchain acceptance owner; #1536 `scripts/check_ym_1444_cmp119_r445_weld_forward.py` adds this commuting-square and source-selector checks. Do not merge/promote to Clay on source-writing or finite enumeration alone.

---

### 20 November — CMP102 Eq. (7) plaquette owner and source norm reconciliation

Supersedes broad "missing plaquette" and "missing gauge representative" labels in preceding history. Existing BalabanPeriodicPlaquetteHolonomy supplies six oriented positive planes and endpoint covariance; BalabanSU2RationalWilsonLargeFieldGapExact already proves unitChordalEqualsTwiceTraceDeficit, and BalabanClayGate4LiteralPeriodicPlaquetteHolonomyGaugeExact proves conjugationPreservesChordalDistanceSq. No new plaquette or chord theorem needed. YMClaySUNSideFourBlockedWilsonGaugeExact supplies coarse plaquette consumer for straight 2-link blocking, NOT nonlinear CMP98 averaging. CMP102 printed pp277–278 (1),(7) visually checked: on interface replace missing bond with one-step averaged finer V, with actual endpoints and ordering; source plaquettes include at least one corner in shell. CMP98 extract pp19–21 (15),(17)–(19) defines nonlinear exp(mean log relative contour) times central holonomy and distinguishes normalized trace norm from operator norm. In SU2 quaternion matrix coordinates M=P-I, M* M=||P-I||_quat² I; thus operator norm and normalized Hilbert-Schmidt norm both equal quaternion chord, and unit norm gives chord²=2(1-ReTr_normalized P). Local SymPy script scripts/check_ym_cmp102_plaquette_norm.py actually executed PASS for symbolic M* M and polynomial deficit identity. This supplies exact normalization, not an estimate of actual mixed-scale plaquette deficit. Eq7 equivalent to per-source-plaquette deficit < epsilon1²/2 in this convention; total action or fine-link radius alone not same hypothesis.

BalabanCMP98Path13BishopNativeSourceExact owns relativeUnit, principalLog, outerYFrom and actual differential route; use same nonlinear group average, not straight-path blocking. Need concrete source boundary endpoint membership and group-valued reconstruction on actual mixed-scale V; targeted default-branch searches did not locate completed same-object interface, not proof of absence. BalabanRootedCoarseAnchoredOrbitSectionRound194Exact and BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact supply rooted based orbit representative uniqueness and preservation of selected average under existing gauge action/root restriction inputs. Source CMP102 Eq4 fixes all mixed-scale coarse sites, so single-root section must not be assumed to preserve multi-anchor condition; use actual compatible section/quotient. BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact is rational-to-rational group word erasure; YMClayOriginalRationalSU2BishopUnitaryWeldExact explicitly only forward embedding into Bishop unit group, not surjective. Retain actual physical minimizer in real carrier; rational fixtures do not establish existence of rational representative. Path13 specialization's selectedBackgroundIsPath13 and selectedBondGroupIsPath13Link already refl once source instance supplied. BackgroundFieldVariationalTheorem.backgroundUnique literal equality requires identified gauge section, not just published unique critical orbit. No new generic adapter, no radius shrink, no Agda or Clay gate promotion. Next actual work: concrete mixed-scale shell V boundary link input using same CMP98 nonlinear group average, actual per-plaquette Eq7 witness and physical minimizer carrier specialization. Prior source authority remains unchanged.

### 20 November — both missing primary PDFs recovered; CMP96/CMP102 exact source recut

Recovered both originals from user's prior uploads: 10.1007@BF01240221.pdf (CMP96 223–250) and 220_2005_Article_BF01229381.pdf (CMP102 277–309). No further upload required. CMP96 printed p224 visually verified, p225 text read; CMP102 pp279,305–306 visually verified. CMP96 (2.1)–(2.4) nests Omega_j=B^j(Omega_j^(j)), coarse domains unions of big blocks, scale-normalized distance between successive boundaries > RM, lifted shells cover lattice with exterior Lambda0=Omega1^c and B^0 identity. Site domains extend to bonds with at least one endpoint inside; do not use induced interior-edge deletion. Empty shells/whole-lattice initial domains permitted. Need exact coarse lattice shell subtraction/support alignment per source, not raw subtraction of differently indexed coarse sites. CMP96 (2.7) gauge parameters zero in exterior and Q'_j lambda=0 on selected shells; (2.11) supplies scale-weighted Laplacian floor on this kernel; (2.14)–(2.17) regularized penalty and projector. Do not reopen scalar martingale or Schur algebra.

CMP102 Theorem1 pp279 (9),(10) supplies actual minimal-orbit gauge-chart regularity including first derivative, Holder, and d* d A control at physical scale under source smallness and cube hypotheses. Section G p305 (170),(171): stationary annihilation on Q(U_k) and source R D* tangent. Stronger p306 (178): <delta A',J>=0 for Q(U_k)delta A'=0 without further gauge fixing. This is source-owned stationarity, not a new result. Eq174 actual fine reconstruction Acal=A1+H1 B-H D(A1+H1 B); (175) solves A1; (176),(177) A1 begins quadratic and reconstruction expansion has BOTH tangent correction and normal -H C^(2)(H1 B). Eq178 kills the tangent first-variation pairing, not the normal term. Eq179–180 alternative gauge-free representation with H0 and modified Green. This confirms prior CMP99/109 corrected Gaussian curvature bookkeeping and gives direct route to published regularity/applicability through actual Theorem1, not selected single-link radius alone.

Inspected ScaledFilteredEstimateExact (scale algebra), GradedLocalCompatibilitySystemExact (abstract local compatibility), BalabanP33WreathBlockSpinCrossPollinationExact (prototype explicitly not gauge/RG), and P10SourceFaithfulActivityContract (P10P11WeightedRelativeDomainCarrier, actual nested relative-domain interface with terminal ownership, not concrete source instance). Prefer existing source domain interface with scale-indexed block expansion, separation and incident-bond geometry. Next identify concrete selected RG domains, original coarse smallness and source minimizer with CMP102 Theorem1 and CMP96 domain hypotheses; then apply existing BalabanExactPublishedCarrierMatching to corrected G1/H1/Delta_k. No new generic adapter, no new SymPy run this source-only round, no Agda or physical gate promotion. Both PDF access blockers resolved; source matching remains open.

### 20 November — CMP99 Dirichlet compression and exact penalty-subtracted lift energy

At 06a93ad5 inspected BalabanCubeEdgeDomains, BalabanCMP116DomainSpecificSupportGeometryRound447Exact, BalabanClayGate4CMP109BlockConventionSeparationExact, BalabanClayT3OperatorSchurComplementExact, BalabanBulkPropagatorAnalyticInhabitation. Existing localization closed-cube/tree geometry and Schur algebra are reusable; no evidence that the concrete CMP99 nested site-domain sequence is already instantiated. BulkPropagatorAnalyticInhabitation is an input record, not an inhabitant. CMP96 extract fetch at Docs/support/reference/balaban-source-extracts/cmp96-propagators-ii.txt returned 404. CMP99 extract (3.18)-(3.25) explicitly uses characteristic compression on enlarged Omega0 and scale-indexed Q' rows. Its (3.35),(3.36) are local gauge-chart bounds on A, first and second derivatives at physical scale L^j eta, with sufficiently small M alpha0, not a single link chord bound. Do not identify the periodic selected radius with all these hypotheses. Actual nested blocks and support alignment remain to be verified against CMP96 (2.1)-(2.4); prior CMP99 PDF verified as above.

For zero extension E_Omega and correct weighted adjoint, actual Dirichlet scalar compression L_Omega=E^* D_U^*D_U E=(D_U E)^*(D_U E), retaining crossing bonds. Deleting crossing bonds changes the energy. For complete supported transported block rows, earlier weighted coisometry remains valid; for truncation use the compressed row map Q E and its true adjoint, not an assumed identity Gram. Source penalty is B=diag(a_j/ell_j²) in site metric. On finite spaces with full-row-rank Q and positive definite K=F+Q^* B Q, set G=K^-1, M=QGQ^*, H=GQ^*M^-1. Then QH=I and H^* F H=M^-1-B, since H^* K H=M^-1. This standard constrained minimization/Schur algebra isolates Eq3.156's penalty subtraction exactly; no second subtraction or coercivity claim follows from G positivity alone. Same identity applies to corrected source G1 when F includes actual inner curvature and gauge contributions, with outer curvature separately as printed. It does not identify the site Q' with bond Q, or construct physical G1. Local scripts/check_ym_cmp99_dirichlet_lift.py genuinely executed PASS: scalar six-site ambient cycle, four-site Dirichlet compression, explicit missing boundary diagonal, mixed complete block weighted adjoint, source R projector identities and penalty-subtracted H lift identity. Fixture is not physical 4D CMP99 domain. Next recover actual CMP96 nested domain definition and instantiate source transported Q' and Q on that carrier; use actual correction and published hypotheses before applying positivity. No new generic adapter, radius reduction, Agda acceptance or Clay promotion. Paper 3 and both roadmaps synchronized.

### 20 November — weighted multiscale CMP99 site average, same-source domain cut

At head 812fb281 recovered BalabanPropagatorSourceLedger.md (historical CMP102 variational PDF filename 220_2005_Article_BF01229381.pdf, not locally recovered in this turn), BalabanCMP98MultiscaleAveragingDerivativeRound126Exact, BalabanClayGate4FiniteWeightedAdjointFubiniExact, BalabanClayGate4FiniteWeightedAdjointFormulaExact, BalabanClayGate4PhysicalWeightedL2NormalizationExact, BalabanClayGate4PrimaryQkWeightedSchurExact, BalabanMarkedHessianPublishedDecayBoundaryExact and BalabanCMP109DirectBetaSourceRegression. Weighted formula is existing finite algebra; physical weight inputs explicitly conditional. PrimaryQkWeightedSchur concerns bond derivative, not automatically site Q'. Marked Hessian source owner already credits CMP99 Theorem 3.14/(3.154), CMP109 (4.35)-(4.37),(5.10), CMP116 localization; do not reopen marked decay shape. PositivePatchCorrection is a downstream beta patch interface, NOT a corrected G1 producer.

Using CMP99 (3.18)-(3.24) site average and physical site metric: for complete disjoint B^j(y), N_j=L^(jd), ell_j=L^j eta, fine weight eta^d, coarse ell_j^d, each transport T_yx orthogonal. Weighted adjoint of Q'_j has block T_yx^* since ell_j^d/(eta^d N_j)=1. Thus Q'_j Q'_j^*=I on complete disjoint block cover, and compositions are weighted coisometries. Mixed-level complete disjoint cover retains this identity; no independent 169 row preconditioning in physical weighted metric. Do not confuse site volume with penalty (3.24), which uses a_j ell_j^(d-2), hence multiplier a_j/ell_j^2 relative to site metric. Recurrence a_(j+1)=a a_j/(a L^-2+a_j), a_1=a, implies 1/a_j=(1/a) sum_{m=0}^{j-1} L^(-2m) for j>=1 (a_0=a separately). Local script scripts/check_ym_cmp99_weighted_site.py executed PASS: rational nested site average fixture, weighted adjoint composition, mixed-level disjoint cover and truncated-support negative control, five penalty recurrence checks. Not full physical domain sequence, no uniform Green claim. Actual CMP99 nested domains and complete-block support under Dirichlet restriction still need verification; overlapping or truncated blocks are not automatically coisometries. Next use exact source domain membership and penalty normalization in G', R, Pi, then attach corrected G1/H1/Delta_k (including subtraction aI and curvature); no new generic adapter, martingale or independent marked decay theorem. Missing variational PDF still blocks independent Eq171/174 verification. No Agda kernel or Clay gate promotion. Paper and both roadmaps synchronized.

### 20 November — CMP99 transported site average and exact projector reuse

At 16c50551 inspected BalabanCMP109RootedLoopAverageCompatibilityExact, BalabanClayGate4PrimaryAveragingLocalityExact, BalabanSelectedBackgroundGaugeConstraintMatrixExact, BalabanSelectedFlatGaugeRegularizedGreenExact. Reuse canonical rooted path transport and covariant gradient/divergence algebra, locality composition and finite KKT projection. Flat Green donor explicitly side-four, not the source nonflat G'. No complete same-object multiscale CMP99 instance located in targeted search.

CMP99(3) original supplied PDF printed pp.393–394 eqs.3.18–3.25: Q' is site-valued transported average (distinct from bond Q and background derivative of Q). On selected literal one-block side13, N=13^4, Q'=(1/N)[Ad_U(Gamma_yx)]_x, each block orthogonal. Q'Q'^*=I/N in unweighted Euclidean site and coarse norms, normalized 169 Q' coisometry at arbitrary unit background. Weighted/multiscale domain adjoints require actual source metrics. Native canonical path length <=24, chord e<=1/4096 gives each transport adjoint defect <=48e; normalized site row defect <=r=48e by Cauchy. On ker Q', flat mean mode norm <=r||lambda||, existing componentwise four-axis Poincare yields ||D0 lambda||² >=(1-r²)||lambda||²/18. Four positive directional covariant gradient defects each <=2e, total norm <=4e||lambda||. Exact rational inequalities (1-r²)/18>1/25 and 1/5-4e>1/6 yield ||D_U lambda||²>||lambda||²/36 for nonzero kernel lambda. Hence L_U+Q'^*aQ' positive definite for a>0 on this finite periodic one-block carrier, by sum of squares and kernel intersection. Not uniform in arbitrary domain or scale; radius and canonical transport semantics conditional.

Eq.3.25 R=I-W^*(WW^*)^-1 W, W=Q'G', G'=(L_U+Q'^*aQ')^-1. Existing rectangular KKT algebra: R self-adjoint idempotent, Q'G'R=0, L_U G'R=R. Pi=I-D_U G' R D_U^* satisfies R D_U^* Pi=0, Pi²=Pi; not asserting orthogonal Pi. Image R=L_U ker Q' since G' maps ker W onto ker Q' and inverse penalty vanishes there. Local exact SymPy script scripts/check_ym_cmp99_site_projector.py genuinely executed: rational nonflat 3-site cycle fixture verifies all identities, R differs from I-N Q'^*Q', and exact side13 scalar budget comparisons PASS. Fixture not full physical Path13 execution; analytic side13 bound conditional. Actual multiscale transported Q', Dirichlet domain and weighted adjoints, source smallness, corrected G1/H1/Delta_k and axial/free carrier still need same-object matching. No published theorem application or Agda kernel acceptance claimed. Paper and both roadmaps synchronized.

### 20 November — primary PDF verified CMP99 corrected quadratic; existing authority reuse

User supplied balaban1985.pdf (CMP99(3), 389–434) and balaban1985a.pdf (CMP102, 255–275, 3D UV stability, NOT CMP102 277–309 variational paper). Visually verified printed CMP99 pp.421 and 428, equations (3.127)–(3.129), (3.155)–(3.158); CMP102 3D pp.260–261 eqs. (17)–(22) confirm separate source reconstruction and negative quadratic J pairing, not a 4D stability theorem.

Critical constructor correction: CMP99 pp.393–394 (3.18)–(3.23) defines Q' as background-transported SITE gauge-parameter averaging, R orthogonal projection onto Delta_U ker Q', Delta_U=D*D. It is not the flat mean-zero projector on divergence rows. Eq. (3.128) uses Pi=I-D G' R D*, then <A,G1^-1 A>=<Pi A,Delta Pi A>-2<H C^(2)(Pi A),J>+||R D*A||²+a||QA||². H1=G1 Q*(QG1Q*)^-1 (3.129). On the unit-lattice carrier (3.156) is Delta_k=(QG1Q*)^-1-aI minus the quadratic form 2<H1 tilde D^(2)(B),J>. The minus aI subtraction is essential; cannot infer Delta_k coercivity just from a positive Schur complement. Eq. (3.156) domain B=0 outside Lambda, B=0 on designated axial bonds, Q1 B=0 (not the earlier selected reduced divergence kernel). C embeds the remaining coordinates by solving selected corridor pivot rows; (3.157)–(3.158) covariance C(C*Delta_k C)^-1 C*. Printed p.428 explicitly states uniform lower bound gamma0>0 independent of k,U under (3.35),(3.36) and sufficiently small M alpha0. No numeric gamma0=1/64 asserted. Reuse published authority, not an invented curvature penalty.

Existing owners inspected at 4013691e: BalabanPublishedAnalyticAuthorities already has theorem1BackgroundUniqueModuloGauge and propagator bounds; BalabanExactPublishedCarrierMatching owns exact lattice/field/gauge action/operator/Green/norm/domain/smallness matching, not an inhabitant; BalabanCMP99EliminatedPivotDerivativeExact owns algebra of pivot derivative, actual coefficient and source Q' derivative conditional (avoid confusion with site averaging Q' above). BalabanCMP109FixedConstraintCoordinateGaussianExact and BalabanCMP109DirectBetaSourceRegression own fixed-coordinate downstream algebra. No new adapter necessary. Actual remaining source match: transported site average Q', R and Pi, inner and outer quadratic jets and J, same Delta_k and axial/free carrier, normalized scales and (3.35),(3.36) with small M alpha0. Previous conditional one-block bare Wilson floor remains auxiliary, not source Gaussian floor. Do not reopen martingale or finite KKT algebra. Missing CMP102 variational PDF still needed for direct verification of eq171/174, not for verifying CMP99 corrected quadratic. This round source audit only, no new SymPy execution or Agda kernel result. Paper and both roadmaps synchronized.

### 20 November — literal CMP109 reconstruction and CMP99 corrected Gaussian source recut

Recovered local text extracts CMP109 (1987), pp.265–268, eqs. (2.6)–(2.12), and CMP99(3) background propagators (1985), pp.421,428, eqs. (3.127)–(3.129), (3.155)–(3.158). These are OCR working extracts, not page-verified authoritative transcriptions. CMP102 UV-stability 3D extract is the wrong paper; actual CMP102 variational paper not in extract packet per README. Do not claim direct inspection of it.

CMP109 uses a corridor-supported h, LQh=I, and B'=B-hD(B), with D(B)=C(B-hD(B)) for the nonlinear remainder C=O(B²). Thus D'(0)=0 and D²D(0)[v,v]=D²C(0)[v,v]; the reconstructed second jet is -hD²C(0)[v,v]. Existing BalabanCMP109QuadraticNormalCorrectionExact pays a conditional 4/3 residual correction; no new implicit-function theorem needed. Existing BalabanCMP109FixedConstraintCoordinateGaussianExact and BalabanCMP109DirectBetaSourceRegression own the fixed Gaussian and pivot/measure derivative interfaces.

Do NOT conflate outer unit-lattice B' with lifted fine fluctuation H_1 B'. CMP109 (2.6)–(2.8) already includes an inner nonlinear lift correction contracted with the source first variation J, producing Delta_1; linear term annihilation on the final constrained tangent does not by itself erase normal acceleration. CMP99(3) (3.128) explicitly includes -2<H C^(2)(...),J> in its gauge-extended quadratic form. Its (3.156) additionally includes -2<H_1 D^(2)(B),J> in A^(k). Thus the published Gaussian operator is NOT the ambient bare Wilson Hessian; it already contains curvature terms (as well as gauge terms). Both inner and outer reconstruction contributions must be tracked on their respective levels; do not add a duplicate multiplier penalty to an A^(k) that already includes them. Exact equality/sign of every OCR term, scale normalization, H_1 and J identification, and source actual constrained carrier still require verification. The source states a uniform strictly positive lower bound for C*Delta_k C via prior propagator analysis, conditional on its own hypotheses; this is an imported theorem candidate, not proof our selected radius/normalization matches.

Native flat one-block comparison only: selected Q0 per-link coefficient 1/13^4; for LQ0 the single-bond right inverse coefficient is 13^3=2197 whereas constant section coefficient is 1/13. Their Euclidean norm ratio is 169. Therefore a corridor pivot on that carrier cannot inherit the norm of the orthogonal section. Actual unit-lattice source pivot coefficient must be recovered separately (may be different). On same stationary tangent, different feasible reconstruction second jets differ tangentially and pair equally with the first variation; this does not establish equivalence of the actual multiscale carriers.

Locally executed scripts/check_ym_cmp109_reconstruction_jet.py (SymPy exact polynomial model): implicit two-jet identity, two-level fine-lift correction chain rule, tangent counterexample, native-flat pivot normalization and inherited allowance PASS. Initial assertion required expansion of both polynomial sides; corrected and rerun. Not a physical evaluation of D^(2), H_1 or J. Inherited ambient allowance 146885123507709280708194373/91687345185165225945115656192 remains conditional, no new physical Hessian floor. Next recover actual CMP102 Sec C/G and Eq171 plus CMP99(3) definitions and verify the same-source H_1, D^(2), J and A^(k) against the already published coercivity and local smallness estimates. No new martingale, no radius change, no Agda kernel or Clay gate promotion. Paper and both roadmaps synchronized.

### 20 November — source coordinates, stationary constraint curvature and raw gauge discriminator

Actual existing CMP109 source owner BalabanCMP109FixedConstraintCoordinateGaussianExact records the nonlinear Q(B') linearization before delta(Q B'), and fixed-coordinate quadratic C(U)^* A(U) C(U). Do not add an independent second variation penalty after adopting a source A that already includes it; nor identify A with ambient Wilson Hessian without proof. Existing BalabanSelectedVariationKKTMultiplierExact, BalabanSelectedVariationSignConventionExact, BalabanPublishedCriticalToSelectedKKTAnnihilatorExact, and BalabanCMP109QRConstraintAnnihilatorReductionExact are first-variation algebra (several literal side-four). They do not supply a Path13 second-jet identity. BalabanClayGate4BackgroundFieldVariationalTheoremExact retains FineConstraint/FineRegularGauge/action as abstract fields.

For the actual local nonlinear constraint map F, a chart Phi with F(Phi(z))=F(U), and D Phi(0)h=v, differentiation gives DF(U)D²Phi(0)[h,h]=-D²F(U)[v,v]. With stationary dS=DF*lambda (positive sign), D²(S∘Phi)=v^*H_S v-<lambda,D²F[v,v]>. Hence the normal acceleration term is exactly the multiplier curvature, not an additional independent correction. Tangential acceleration drops by stationarity. This is classical chain rule, not a new physics theorem. If using the previous right inverse T, an admissible second jet is -T D²F[v,v]; tangent ambiguity does not affect stationary Hessian. Previous Eq120 printed differential must first be identified as derivative of the actual constraint in the chosen tangent coordinates (it includes connector correction); differentiated moving-frame terms cannot be ignored. For the conditional inherited bare floor f=1579499892025915936100626501/91687345185165225945115656192 the remaining absolute curvature allowance for 1/64 is 146885123507709280708194373/91687345185165225945115656192 ~0.001602. Exact requirement <lambda,D²F[v,v]> <= (f-1/64)||v||², not a mandate for a stronger absolute bound. For fixed-background affine gauge condition in fluctuation coordinates its second jet is zero IF that is the actual source gauge; do not differentiate G_U with respect to the background instead of fluctuation.

Important actual native geometry negative control: constant rational SU2 link q=((1-r²)/(1+r²),2r/(1+r²),0,0), r=1/16384, on direction 0 only, other links identity, lies inside native chord radius 1/4096. Constant color-y perturbation on direction 0 has G_U h=(I-Ad_{q^-1})e_y nonzero constant in space by BalabanPath13BackgroundGaugeConstraintMatrixExact's actual entry formula. Mean-zero projection kills it, raw divergence does not. This disproves automatic raw/reduced gauge-kernel equality from radius alone, NOT equality on actual joint constraint (constant h not asserted to satisfy Q_U h=0), nor a stationary-source counterexample. Gauge invariance alone does not imply zero gauge multiplier unless actual averaging is invariant along enough gauge directions (or an equivalent identity); exact small matrix discriminator A=(1,1,0), G=(0,1,0), g=(1,0,0)=A^T-G^T. Existing source may implement reduced gauge as actual gauge fixing; identify rather than reinstate all rows by fiat.

Locally executed scripts/check_ym_constraint_curvature.py with Python/SymPy: chain rule/sign, gauge multiplier discriminator, native-radius constant residual and inherited allowance comparisons PASS. No numerical physical second jet, no Agda acceptance. Next actual producer: recover nonlinear fluctuation coordinate change from CMP109 §2 (and CMP102 variational constraint), identify its second jet and multiplier action on same selected Path13 source; verify actual gauge condition, then pay signed curvature allowance or show source A already contains it. Do not promote inherited ambient floor to full variational Hessian. Roadmaps and Paper 3 synchronized.
### 20 November — paired periodic Eq120 cancellation and conditional moving-kernel bare Wilson floor

See Docs/physics/YMClayPath13PairedMovingKernel20261120.md. Actual one-block wrap makes W=U and RC=UVU^-1, allowing paired connector bound p=26e(2+j), and the offset-independent central velocity permits quadratic average coefficient h via J Ad_R=J+ad_y. Exact local SymPy enumeration scripts/check_ym_path13_paired_defect.py gives normalized squared defect K~0.248064 (previous 227.54), constant max-section bound r~0.0883121 at unchanged e=1/4096. Existing martingale/Poincare and constant section give on actual selected A h=0: mean/detail norm ratio squared <=K/(1-2r)^2, scalar periodic difference floor fD>1/25. Existing reduced background gauge defect delta and flat periodic Hodge then give bare flat curl floor fD-delta on joint kernel. Literal unweighted quaternion Wilson left-exponential second variation deviates by <=96e via four-factor telescope, four-edge Cauchy and six plaquette incidence. Thus conditional ambient bare Wilson Hessian floor fD-delta-96e~0.0172270>1/64 on selected reduced joint kernel. This does NOT identify actual variational constrained Hessian including multiplier/constraint curvature, effective action terms, full gauge reduction or multiblock source. Recover original stationary constraint-curvature/second variation weld and actual selected chart/radius; side-four tangent projector is not a Path13 instance. No new martingale, no radius reduction, no Agda kernel or Clay gate promotion. Executed exact local arithmetic and incidence, not numerical Hessian. Paper and both roadmaps synchronized.

### 20 November — reduced joint constraint: gauge-projected constant section at native radius

Reuse BalabanPath13PreconditionedAverageGaugeOrthogonalityExact, BalabanCMP109L13ConstraintRowPreconditionerExact, BalabanPath13BackgroundGaugeConstraintMatrixExact and BalabanPath13SelectedBackgroundGaugeAdjointFloorExact. The existing BalabanPath13PreconditionedSelectedCombinedFloorExact is for normalized flat averaging plus the actual selected background gauge, NOT full nonlinear Eq120. Its reduced gauge carrier is the flat mean-zero multiplier space; here G is the covariant divergence compressed to that reduced codomain, not all gauge rows. With A=169 Q (selected twelve rows), Sbar=S/169, A0 Sbar=I, Sbar is Euclidean isometry, G0 Sbar=0. Existing gauge adjoint floor f=130991/3145728 and defect coefficient delta=9/1048576 imply ||G Sbar||_2<=sqrt(delta) and ||G^*(GG^*)^-1||_2<=1/sqrt(f). Thus P_G=I-G^*(GG^*)^-1 G satisfies ||(P_G-I)Sbar||_2<=sqrt(delta/f)<1/69. This finite-dimensional inference uses the existing reduced gauge floor, not a new gauge law.

At e=1/4096, retain the preceding conditional signed Eq120 coefficient bounds a,b,c,h and row r=501336717/1379256320. On literal one-block periodic geometry translated connectors wrap onto the same fine bond labels. Sum weighted occurrences per selected row and fine label BEFORE squaring; for each color-vector block use its operator norm majorant, then vector Cauchy-Schwarz and sum four output direction squares (no extra color factor). Exact enumeration gives ||A-A0||_2^2<=K=320169499653314191/1407062127411200<256. Hence ||A||_2<17. In coarse max-of-four Euclidean color norm, ||A Sbar-I||<=r, and ||A(P_G-I)Sbar||<=2*17/69 (input Euclidean <=2 times max; output max <= Euclidean). Thus ||A P_G Sbar-I||_max<=81486948353/95168686080<7/8. The inappropriate all-Euclidean triangle estimate 2r+correction exceeds one; use the mixed norm exactly as specified. No radius reduction.

Define J=P_G Sbar (A P_G Sbar)^-1, so A J=I and G J=0, inverse coarse max-norm factor <8; J maps coarse max to fine Euclidean with norm <16 (P_G contraction and Sbar isometry). Joint right inverse for any reduced gauge target g and coarse target alpha is T(alpha,g)=G^*(GG^*)^-1 g + J(alpha-A G^*(GG^*)^-1 g). This is an analytic finite-dimensional conditional certificate on selected twelve Eq120 rows plus projected mean-zero gauge, not a kernel-checked theorem, not the original variational identification, not full gauge rows. Full gauge mean modes must not be discarded without a source identity. The signed differential semantics and native chart/radius remain premises; no physical admissibility or Hessian floor follows just from this right inverse. Next check actual variational constraint and original gauge reduction, and energy-weighted moving-kernel estimate. Existing martingale and Poincare unchanged; no Clay gate promotion.

Local execution of scripts/check_ym_path13_joint_projected_section.py succeeded with exact K, r, bound above and rational assertions K<256, delta/f<1/69^2, bound<7/8. Paper 3 and both roadmaps synchronized.

### 20 November — geometry correction: selected one-block constraint, native radius, constant section

Supersedes the interpretation of the previous multiblock Schur diagnostic as the source-native radius test. BalabanPath13BackgroundGaugeAdjointDefectExact.SelectedInverseLinkRadius13 has squared Euclidean quaternion chord <=4 rho^2, rho=1/8192, so e=1/4096, NOT 1/2048. BalabanPath13RadiusOperatorDefectRouteExact derives 1/2048 as quaternion L1 and representation-dependent operator majorant; do not treat it as the source chord or apply a second adjoint inflation to that majorant. NativeGeometry in BalabanCMP98Path13BishopNativeSourceExact uses R192.path13PeriodicIndex, the side-13 periodic site carrier; Path13PositiveBond is site x axis, not one row per coarse block of an arbitrary multiblock torus. At identity the entire all-site Q repeats the directional mean, rank 12, whereas any one selected center with four direction rows has codomain R^12. Do not demand all-site surjectivity, or infer which subset defines the original variational constraint without the existing fine-constraint identification.

On the selected one-center twelve-row constraint, let S extend a coarse Lie vector as constant in space for each bond direction, with max of the four Euclidean color norms on both sides (fine max over sites and directions). Q0 S=I by the existing wrapped directional mean. Use the previously derived signed Eq120 row budget on this section, with the actual e=1/4096: ||Q S-I|| <= R_e=501336717/1379256320 <1. Neumann yields a right inverse S(QS)^-1, max-norm bound 1379256320/877919603 <8/5; no factor 13^4 from estimating arbitrary fine-domain perturbations is needed for this sufficient surjectivity test. This analytic argument is conditional on the printed left differential and the selected chart/radius and actual row identification; it is not a proof of combined gauge/averaging constraint surjectivity or moving-kernel coercivity. It does not establish the arbitrary multiblock extension, where a block-constant section has a different Q0S. No changed radius, no new martingale, no physical gate promotion. Locally executed exact script scripts/check_ym_path13_selected_constraint.py PASS (radius, wrapped stencil, rank, row budget and Neumann bound). Next identify the selected actual constraint and gauge-compatible section and compare its energy norm; reuse existing constrained Hessian owners. Do not call the prior sufficient estimate failure a physical obstruction.

### 20 November — signed Eq120 coefficient defect: conservative radius audit

Use the actual Eq120 source (BalabanCMP98Equation119TwoCarrierSelectedBondExact), NOT unsigned contour incidence alone. In left trivialization let M=U V, P=C W, R=M P^-1, y=log R, Y=avg y; D=dexp(Y), J=inv-dexp(y), E=Ad_exp(Y). Denote path velocities r_U,r_V,r_C,r_W, and adjoint operators by Ad. The exact Eq120 (including its translated-connector correction) is 1/13 times avg[(DJ-I)r_U + DJ Ad_U r_V + (I-DJ Ad_R) Ad_C r_W + (E-DJ Ad_R)r_C]. At flat field only r_V survives. This is a source-level analytic rewrite of the existing printed calculus, not a new averaging map. Requires the selected principal chart and ordinary SU2 left differential semantics; verify normalization on the physical background before formal promotion.

For unit quaternion link chord <= e, e<=1/2048, relative contour chord <=74e; ||Ad_q-I||<=2||q-1||. Principal log angle <=3/2 chord on this ball, so ||ad_y||,||ad_Y||<=x=222e. Integral rotation representation implies ||D||<=1, ||D-I||<=x/2=d; Neumann gives ||J-I||<=j=x/(2-x). Write a=d+j, b=a+148e, c=a+74e, h=x+b. By telescoping against the flat path velocity, coefficient defect per occurrence on U,W,V,C respectively <=a,b,c,h (V includes <=24+13 prefix links; others multiply zero-flat coefficients by isometries). This retains cancellation before taking absolute values. Uniform on compatible periodic multiblock tori provided the actual selected background admits this link radius and the same source geometry. No Hessian perturbation conclusion yet.

Exact occurrence class column maxima U,W,V,C = 52728,52728,13,28561. Sum weighted folded columns before maximizing, divide by 13*N (N=13^4). Row bound (168/13*(a+b)+13*(c+h))/13. Weighted Schur squared defect for coarse norm N times unweighted coarse norm = N*row*col. Locally executed scripts/check_ym_path13_signed_defect_budget.py: squared upper bounds 1349.0930479433102 at e=1/2048; 1.2739903923858924 at 1/65536; 0.004971707998158777 at 1/1048576. Compare flat squared smallest singular value 57/169 in matching normalized coarse norm. At e=2^-20 the bound proves surjectivity persistence under these assumptions, but does not establish physical admissibility of that radius or moving-kernel Hessian coercivity. At e=1/2048 the sufficient Schur estimate fails, not the actual operator. Next recover sharper source-localized/covariant coefficients or admissible smaller radius and match constrained Hessian reference/variation. Existing martingale unchanged. Local arithmetic execution only; no Agda or physical gate promotion.

### 20 November — literal nonlinear contour incidence, reuse existing martingale

Do not recreate Martingale or Poincare: BalabanNormalizedFourAxisMartingaleExact and BalabanPath13FourAxisPhysicalPoincareExact already own the same-carrier variance and scalar 1/18 floor. Read actual ordered signed-axis path executable check_ym_path13_full_mixed_jet.py: Eq120 includes correction average(Ad_C r_plus - r_minus)/13, not solely the differential of exp(mean log relative) C. The finite contour incidence counts the actual ordered connector, translated connector, crossing and central segment, using positive-bond labels for inverse traversal. For connector direction d=0..3, prior axes fixed and later axes zero, multiplicity on axial edge k is (6-k)13^(3-d) for k=0..5 and (k+7)13^(3-d) for k=-6..-1. Each connector total 4*42*13^3. Full unsigned contour row mean 674/13, not worst-case 74. Folding by fine residue mod 13 sums across all translated coarse rows on an arbitrary compatible periodic multiblock lattice; max column mean 10310/2197, per-axis raw maxima 134030,36686,29198,28622. At most eight unwrapped row-offset incidences per fine bond (periodic identifications can only merge rows). These are unsigned contour counts before signed cancellation, inner/outer log derivatives or the separate Eq120 correction. They are not Hessian overlap (plaquette incidence) or a perturbation norm bound. Use weighted Schur with actual operator coefficients and subtraction of flat terms; do not substitute 8 directly into LocalHessianRadiusBudget, whose 1/32 reference floor also requires matching the moving kernel. Existing 1/57 multiblock constrained bound is not automatically 1/32. Local Python/SymPy executed scripts/check_ym_path13_contour_incidence.py: PASS with above exact output. Next reconcile the actual coefficient defect and moving-constraint norm, retaining all mixed detail sectors; no new martingale or physical gate promotion. Paper and both roadmaps synchronized.

### 20 November — 369 / 13 / relative j geometry reconciliation

Use the actual same-carrier Path13 four-axis martingale theorem (BalabanPath13FourAxisPhysicalPoincareExact), already present, not the older AllPhysicalFibresPoincare note's outstanding martingale status. It applies the 1/18 fibre floor and conditional-expectation orthogonality on 4*13^3=8788 literal fibres. The SU2 state has (4*3)*13^4=342732 coordinates. Reuse the axis average and detail operators for factorized flat calculations: P=ones(13)/13, H=I-P, ranks 1 and 12. Tensor products give transverse ranks by detail count 1,36,432,1728 and four-axis ranks 1,48,864,6912,20736; ordered martingale ranks 26364,2028,156,12 plus constant 1. These are exact scalar carrier decompositions, not nonlinear Hessian diagonalization or gauge/constraint ranks.

Cross-PR source owners: docs/crystallography_13_in_27_antipodal_diamond_crosspr_20261026.md and docs/crystallography_369_hyperfabric_thread_master_roadmap_20261026.md on default branch (not present on audited YM head); original 27-site cube = origin + 13 antipodal pairs, projective strata 3+6+4. Preserve orientation and seam/adjacency residuals. A 13-label codec to [-6,6] can index Path13 transverse factors but is not an intertwiner of cyclic translations, nearest-neighbour adjacency or gauge operators; do not replace geometry. Reuse #1249/#1261 native owners if an actual action weld is needed. 13^3 is the transverse tensor power, not the Monster 13-primary subgroup (Base369OggNestedPhaseRound7 records 13^3 exponent), nor tetration. Same cardinality is not same algebra.

DASHI/Foundations/JPlusOneScaleBridge.agda gives 10+1 local j-unit extension and 10+2 relation stage, with semantic separation from modular j and McKay 196883+1. DASHI/Foundations/TernaryThirteenCentralCompletionBundleSheafExact.agda gives actual 12+1 central gluing with common-centre agreement, not independent centres. 11+1=12 is another cardinal step, requiring its own source relation constructor, not a proof of equal stage semantics. The Path13 12+1 projector split is constant plus mean-zero, distinct from the stage completion and the 12 Lie/bond components plus a scalar coordinate. JFineCoarseRelativeScaleExact (present on YM head) fixes jCoarse=3^2, jFine=3^9 relative, jAbsolute=3^11; reciprocal spatial-frequency scale. Distinguish 3^12 * 3=3^13 central trit extension from exponentiation of 13 labels. No 3-adic refinement identity between 3 and 13; exact periodic block refinement requires compatible divisibility. AnalyticJTetrationActiveMaxCut20261109 and RSA260369DNA27CodecNDimTetrationCrossPollinationExact retain natural-height iteration vs fixed tensor nesting boundaries.

Local executed SymPy script scripts/check_ym_path13_369_factorisation.py: exact representative codec/strata, rational projector laws, tensor ranks and relative scale arithmetic PASS. No new physical theorem or kernel claim. Next audit actual nonflat contour incidence using transverse factorization and existing source path operators, retaining mixed terms; reuse conditional-expectation and hyperfabric local/seam reconstruction rather than equating carriers. Historical rounds provenance only. Paper 3 and both roadmaps synchronized.

### 20 November — constructor correction: literal Path13, not straight F19 holonomy

The straight-boundary estimate in YMClayOriginalWilsonBlockedSurfaceEnergy20261120.md applies to native ordered path blocking only. It is NOT a bound on the nonlinear CMP98 Eqs.(119)-(121) averaging operation; a side-13 square fixture is not a Path13 test. The actual owners are BalabanCMP98Path13BishopNativeSourceExact, BalabanCMP98Path13PrintedRoleSourceFamilyExact, BalabanCMP98Equation119TwoCarrierSelectedBondExact (assembledEquation120QSource), BalabanPath13RadiusOperatorDefectRouteExact, and BalabanCMP98Path13RelativeContourPrincipalImageExact. The latter already supplies the literal 74-factor contour budget 37/1024 conditional on the selected fine-link radius; do not rebuild it. NativeGeometry selects the background via BackgroundFieldVariationalTheorem, whose original fine-constraint/action identification and small-field admission remain explicit. Do not substitute the F19 straight map for that constraint.

Exact separation at identity: a fine axial link at axial offset zero but nonzero transverse offset has straight center-path differential zero and literal Eq120 coefficient 7/13^5 on a multiblock direction, or 1/13^4 on the one-block wrapped torus. Thus the constructors differ even at first order. Local SymPy executed scripts/check_ym_path13_constructor_boundary.py: six exact cyclic geometries, Gram SOS identity, column sums and overlap, and off-center derivative coefficient. The existing flat Gram is (113I+28(T+T^T))/13^6; independently its difference from 57I/13^6 is 28(I+T)(I+T^T)/13^6. This is corroboration, not new flat coercivity. Flat support overlaps at most two longitudinal blocks per fine axial link; nonlinear transverse contour contributions must not inherit that overlap without an actual incidence proof.

Next use actual selected variational background, complete Eq120 derivative and actual contour support/defect operators to inspect the nonflat operator budget and nonlinear RG marked activity. Do not promote the earlier straight surface transport to physical CMP116. This packet is a source/geometry correction and exact finite check, not a physical moment or spectral theorem; no Agda acceptance claimed.

### 20 November — original aligned blocked surface moment transport and scale obstruction

See Docs/physics/YMClayOriginalWilsonBlockedSurfaceEnergy20261120.md. The existing straight native holonomy map yields d_coarse <= b^2 sum_surface d_fine; aligned coarse faces have disjoint fine plaquette labels. Via the previous microscopic chessboard bound (conditional on its closed-cube applicability), the actual pushforward satisfies E exp(theta beta/b^2 sum_A d_coarse)<=exp(C(beta)b^2|A|/4) for theta<=1/96. Existing canonical F19 marked expectation owns the selected b=2 effective measure attachment. The resulting rate beta eps/(96 b^2)-C(beta)b^2/4 is useful only when beta eps>24 C(beta)b^4. Exact commuting rational SU2 patch control shows fine deficits O(b^-4) can produce order-one coarse holonomy. Therefore deterministic transport alone cannot pay fixed-physical-scale moments. Reuse existing nonlinear/source-localized marked CMP116 estimates and actual chargeSumBelowRootedTail, not bare coarse substitution or a new compiler. Earlier 19 November BIDI chessboard note already owns a related direct mixed-defect bound; credit both. Local executed regression: 120 noncommuting fixtures, 4 periodic incidence fixtures, 5 flux controls, 1 symbolic rate identity. Analytic finite-scale result, native formalization and physical-source verification pending; no Clay gate promoted.

### 20 November — sparse microscopic Wilson energy / chessboard reduction

New source-specific analytic note: Docs/physics/YMClayOriginalWilsonSparseChessboard20261120.md. Reuse the original Wilson pressure, site-plane Haar factorization and standard chessboard inequality (Biskup arXiv:math-ph/0610025, Theorem 5.8). Closed unit cubes: 24 orientation/transverse parity classes, each dissemination marks V/4 plaquettes four times. For theta<=1/96, joint moment E exp(theta beta sum_A d_p)<=exp(C(beta)|A|/4), hence sparse plaquette event rate beta epsilon/96-C(beta)/4. Frustrated links use six witness choices and four-link multiplicity; mixed contours use partition union, then existing rooted animal entropy. This is an analytic microscopic UV bound, with standard chessboard input, on even reflection-compatible SU2 tori; no fixed-physical-block/nonlinear renormalized moment, IR, or Clay endpoint promotion. Local SymPy exact combinatorial regression executed: 3 period fixtures, 72 orbit classes, incidence, one symbolic rate identity and 999 ceiling checks. Agda kernel pending; next identify native site-plane all-direction chessboard weld and true blocked-energy source. Historical rounds are provenance only.

### 20 November 2026 — normalized native-real bounded-observable route

Historical round identifiers (R444, R559, etc.) are provenance, not independent proof phases. Prefer the normalized original Wilson owners in PR #1444. Extended YMClayOriginalWilsonFiniteNumeratorOrderExact with originalWilsonNumeratorConstant and originalWilsonNormalizedBelowConstant, using existing source Haar scale, positivity, and partition lemmas. Given pointwise nonnegative slack to a constant B and ordered division cancellation, E_n(test)<=B on the actual original Wilson family. For a bounded word |F|<=b and lambda>0, choose test=exp(lambda |F|), B=exp(lambda b); pointwise exponential monotonicity supplies the slack. For a sum of m bounded nonnegative insertions this gives exp(lambda b m), without rational-to-real measure substitution. This elementary bound does not provide a useful rare-event exponent if b grows at the same rate as the bad-field threshold, nor does it establish moments for unbounded renormalized fields. Original signed Wilson word and three-moment cutoff owners already exist; do not duplicate them.

Local SymPy regression scripts/check_ym_native_real_bounded_moments.py executed 333 exact rational assertions on a positive polynomial-weight fixture (not the physical exponential Haar measure). The earlier factorial/SZZ regression formulas were also locally replayed (25 assertions in the full prior script, not the previously reported 26). Native constant bound source-written, kernel pending; no physical endpoint promoted. Next locate actual normalized blocked-energy mark envelope and source-uniform nontrivial moment costs, then active-window/terminal curvature receipts. Preserve original-source distinctions and attribution.

## 20 November 2026 — exact symbolic moment normalization and source-native IR audit

Local SymPy execution of scripts/check_ym_moment_szz_weld_20261120.py passed: 25 assertions (including nine factorial scalings and nine positive Taylor bounds). This is mathematical regression evidence, not Agda elaboration or actual Wilson continuum acceptance.

The exponential-to-polynomial normalization is corrected at T5, R444, R559, R560, R514 and moment compact containment: for lambda>0 the bound is n! M/lambda^n, not n! M/lambda. Counterexample to the former declaration: X=20, lambda=1/10, n=2; 400>20 exp(2). A shared scalarNatPower avoids an independent radius choice. Positivity and actual moment-production hypotheses still need source realization; no universal claim for arbitrary record operations.

Recovered existing IR source owners: BalabanSZZSourceNativeHessianHandoffExact already welds the effective Hessian margin to the running coupling; BalabanSZZActiveWindowOverlapNecessaryExact already proves the necessary UV/SZZ window overlap. The perturbed threshold is u<N^2/48-N rho/24. SymPy verifies its algebra and curvature slack subtraction. The original active scale must lie in the overlap, with the actual remainder Hessian norm; a positive target does not supply that fact. Stochastic and OS physical time remain distinct.

R444/R445 -> R559: BalabanRationalRealConnectedCovarianceExact provides a scalar embedding and selected-expectation identity pattern, not an exponential expectation identity. YangMillsLiteralCMP119ExponentialMomentTheoremExact is a native-real constructor consuming the actual moment producer. The finite rational fixture checks normalized expectation and polynomial scaling only. The missing transport is actual marked exponential observable/expectation equality (or native-real bounds), positivity and uniform integrability, not a second generic moment compiler.

Status: SYMBOLIC_PASS / SOURCE_WRITTEN / KERNEL_PENDING. No E1/D1/D2/N1/G1 promotion. Next: find actual real marked activity inputs and source-valid active crossover. Maintain Paper 3 and both roadmaps with each implementation.

## 20 November 2026 — R559 same-family and SZZ typed terminal weld implementation

- R559 commit 510f57d75d9b2642fee870403cc37af2623cf578: added preOSToSameOSMoments / sameOSToPreOSMoments and definitional producer-preservation proofs in the existing YangMillsLiteralCMP119QuantitativeMomentsRound559Exact owner. The OS interface reuses the pre-OS producer on A.family and A.observableAlgebra; no second moment selection.
- SZZ commit 415210fc567ac692c9bfc590b5e5d5c2bdf76b5f: terminalCriterionFromCrossover constructs SZZPerturbedTerminalCriterion directly from crossover drift and positive target margin, without Set-valued stochastic/OS predicates; actualTerminalCriterion preserves actual trajectory coupling and remainder cost definitionally.
- Exact boundary: R444/R445 and Physical.MarkedMomentClosure use rational scalars, R559 uses real expectations. Do not assume definitional equality. Next weld must transport the actual marked observable operations, expectations, inequalities and uniform integrability to the original real family, or locate a native real producer. The current polynomial bound divides by lambda rather than lambda^degree; verify normalization or correct before promotion. Pre/post weld does not discharge source estimates.
- SZZ arithmetic criterion is not proof of actual effective density, physical curvature, or OS-time gap. Verify source applicability and common physical gap separately.
- Status: SOURCE_WRITTEN / KERNEL_PENDING. No new physical endpoint closure. Existing theorem owners extended; roadmaps synchronized in the same PR. Next: native real marked moment transport and actual crossover source cost.

## 20 November 2026 — reuse-first UV/IR/OS weld reconciliation (audit of 62fe5287)

**Policy:** assume a candidate existing producer until the relevant historical/current owners have been searched. Do not reopen generic mathematics or declare entire work packages unimplemented. Distinguish SOURCE_OWNED, WELD_REQUIRED (existing producer/consumer with exact same-object or typed realization outstanding), SOURCE_ESTIMATE_UNVERIFIED (a quantitative input whose actual producer has not yet been identified), and KERNEL_PENDING. A weld may itself contain a substantive mathematical obligation. Neither a status label nor an assumed completed producer is evidence of physical closure.

| Prior synthesis target | Existing source owners (Agda unless specified) | Exact remaining verification/weld |
|---|---|---|
| P1.1 Gaussian/FP/Haar/Ward | check_ym_path13_hessian_gaussian.py; check_ym_cmp109_restricted_ward.py; BalabanCMP109DirectBetaSourceRegression; BalabanCMP109MixedDerivativeBetaExtractionExact | Identify actual same-background total off-diagonal two-jet including the correct delta density, FP and Haar; Ward remainder degree >=3. Do not repeat determinant calculus. |
| P1.2 physical beta | BalabanCMP109WardFloorToBetaJetExact; BalabanCMP109MixedDerivativeBetaExtractionExact; #1498 B4 denominator and #1503 P0 original-source convergence | Actual global Gaussian lower <= same beta jet; physical scalar integral/error and normalization receipts. #1503 donor BalabanP0OriginalSourceConvergence20261114 is not present at audited #1444 head (404); check exact sibling before transplant. |
| P1.3 nonflat coercivity | BalabanYM4UniformCoercivityPerturbationExact; BalabanBackgroundFieldClosure; current Path13 flat Gram and Bishop principal-log inverse | Existing 1/32 reference -> 1/64 perturbed floor compiler; verify literal local Hessian Lipschitz, radius, overlap budget <=1/64 and same moving constraint/norm. No new generic perturbation theorem. |
| P1.4 nonlinear remainder | BalabanBackgroundFieldClosure; BalabanBetaHistoryLocalizedInfluenceExact; BalabanCMP109DirectBetaSourceRegression; BalabanYM4LargeFieldCoupledStepExact | Match actual five-channel current-step nonlinear remainder, Jacobian and marked derivative costs to history-uniform source; only irrelevant memory may use geometric forgetting. Verify shared slack. |
| P1.5 joint moments | BalabanClayT5MarkedMomentProducerRound444Exact -> BalabanClayT5MarkedPreferredExpectationRound445Exact -> YangMillsLiteralCMP119QuantitativeMomentsRound559Exact | R444 already constructs ExponentialMomentProducer from MarkedMomentTypedRealization, R445 reuses it definitionally; no independent second moment theorem. Identify joint separated blocked energy as admitted marked insertion, actual FP closure and typed uniform bound K^|T| on original family; rational/real alignment. |
| P1.6 scale and convergence | BalabanSZZWilsonCrossoverTerminalGapExact; BalabanP33TerminalScaleGapPullbackExact; R566 projective source, variable-cutoff cylinder limit, R445 preferred expectation | Existing coupling crossover and gap recursion; verify actual trajectory reaches valid crossover, terminal spacing bounded in physical units, source losses and bounded-tail/limit inputs. |
| D1 UV polymers | BalabanYM4LargeFieldCoupledStepExact; BalabanClayGate4GaugeRootedEntropyDecayExact; BalabanStepVConnectedCorrelationSourceSnowballExact | Source-owned entropy summation and shared large-field RG slack; identify original connected mixed/frustrated activity bound and marked support/connecting-weight tail. Joint moment -> Markov -> entropy needs no new theory. |
| D1 IR | BalabanSZZWilsonCrossoverTerminalGapExact; BalabanTerminalScalePhysicalClustering; BalabanCutoffUniformPhysicalTransferGapMasterExact | SZZ normalized pure Wilson margin N/2 - 24u/N; crossover u<N^2/48 plus actual remainder Hessian cost rho leaves positive margin. Verify actual terminal effective density and source applicability; SZZ stochastic gap is NOT automatically OS physical-time gap. Existing gap master needs common physical floor, not pointwise positivity. |
| D1 transfer / D2 same OS | BalabanClusteringRateSameGapCandidateWeldExact; R320/R333/R577/R583; BalabanTerminalScalePhysicalClustering | Same mStar=gapCandidate already definitionally welded; no second gap positivity theorem. Verify actual terminal correlation, physical-distance calibration, residual conditional covariance, full complete OS test density, same physical-time spectral representation. |
| N1 | YMClayRGLossBudgetToNonGaussianExact; existing finite SU2 variance and R563 same-family Ward owners | Identify fixed physical observable and actual continuum source survival/loss budget or equivalent witness. No duplicate telescoping. |
| G1 | BalabanGroupParametricFiveBlockSignedG2Exact; R569–571; CompactSimpleQuantitativeCoverage | Group-parametric five-block signed absorption already exists; actual selected-background/KKT/Green scalar estimates per G and same physical family remain to be verified. |

**Highest-value weld path:** R444/R445 marked moment realization -> R559 on literal original Wilson/CMP family; existing UV large-field shared-slack compiler -> existing SZZ crossover/terminal physical clustering or independent physical transfer route -> R320/R333/R577 same-H. Do not assume SZZ heat-bath/Langevin time equals OS Euclidean time. Preserve the exact beta/source normalization and moving constraint measure. Existing fixed-volume Combes–Thomas and bare Poincare negative controls prohibit direct uniform-volume promotion.

**Acceptance:** all owners in the table were located by source search; R444/R445, R559, Ward beta extraction, coercivity perturbation, SZZ crossover, terminal clustering, cutoff-uniform gap master, gap pullback, same-rate weld, large-field shared slack, rooted entropy and group-parametric five-block source were directly read at the audited head. The remaining exact hypotheses have not been proven absent repo-wide. No new Agda kernel receipt or physical endpoint closure is claimed. Update this ledger after each successful source weld with producer declaration, consumer field, exact source identity, commit and kernel receipt, rather than expanding the generic roadmap.

## 18 November 2026 — exact 2T conjugation symmetry boundary and Burnside compression

The checker `scripts/check_ym_original_L1_2t_symmetry_boundary_20261118.py` constructs the original 24 rational Hurwitz quaternions, uses the actual pair deficit `2 sum_{1<=a<b<=3}(q_a r_b-q_b r_a)^2`, and verifies exact group closure, inverses, and 13,824 ordered conjugation/pair identities. Simultaneous conjugation of *all four links* preserves the six-commutator action and coarse squared real trace `(Re(U0U1))²`; this is the legitimate symmetry for orbit reindexing. The source action is **not invariant under simultaneous left multiplication**: for `(-1,-1,-1,-i)` and `g=-j`, action changes from `0` to `6`. Hence no one-link gauge fixing by that action has been justified.

There are **seven true 2T conjugacy classes**, sizes `1,1,6,4,4,4,4`, but **five distinct real trace values**, not seven. The four size-4 classes comprise two pairs sharing trace `+1/2` and `-1/2`. The source depends on relative orientations; independently replacing four variables by their seven class labels (`7^4`) is NOT an established action-preserving quotient. Exact Burnside counting for simultaneous conjugation gives `(2*24^4+16*6^4+6*4^4)/24=28576` true fine-configuration orbits, versus `331776` configurations (approximately 11.61x reduction). A formal Agda orbit enumerator and the original conditional-moment reindexing to the 24 blocked B values remain OPEN.

**Related algebraic boundaries:** the sign-forgetting quotient `Trit→Bit` does not induce a quaternion/SU2 matrix isomorphism; the 2x2 quaternion-to-complex-matrix map needs independent ring laws. The group C3 acts on ternary sheets, but does not supply the B4 invariants, real Cauchy modulus or original physical RG. For F8, the diagonal `(6,14,22)` coefficients are a nonzero radial defect relative to the S3 symmetric average; they cannot be averaged away to assert full physical equivariance. Neither the full F8 theorem nor the 27-trit Hilbert/physical collapse interpretation is newly kernel-certified in this tranche.

**Verification:** exact Python rational/conjugation and Burnside assertions locally checked; no Agda kernel receipt. Open targets remain finite original 24^4 conditional moments, complete B4 polynomial invariant induction, Bishop modulus/Haar invariance, SU2 matrix identification and physical Wilson RG/continuum transfer.

## 18 November 2026 — exact finite 24-cell blocked expectation / variance

PR #1444 now includes `YMClayOriginalL1Rational24CellBlockedMomentsExact.agda` and `scripts/check_ym_original_L1_24cell_blocked_moments_20261118.py`. From the existing positive three-class quadratic-Taylor blocked density (multiplicities 6/16/2), the Agda source writes a normalized rational functional on arbitrary coarse scalar observables `f(t)`, its constant-one and first/second moment equations, and the strictly positive rational variance of `t=(Re(U0U1))²`:
`806306942803/12833778905928 > 0`. The exact independent Fraction calculation verifies 12 exact assertions. This proves finite normalized nonconstancy only, not a spectral mass gap.

**Trust boundary:** No Agda compiler is available in the current execution environment, so the source-written Agda proofs are **not kernel accepted**. The exact original 24⁴ source action→conditional-moment theorem remains open in Agda. The full exponential Gibbs/Haar measure and continuum physical RG transfer remain open. Similarly the full Reynolds invariant basis, constructive effective `bn`, Bishop Cauchy/invariance and original SU(2) carrier equality remain open.

## 9 November: NEW actual SU(2) Wilson conditional analytic estimate (not a Clay endpoint)

An independent analytic calculation on the **original** four-dimensional SU(2) Wilson one-link Gibbs conditional is in [YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md](YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md), with successfully executed exact-rational certificate `scripts/check_ym_su2_wilson_singlelink_uv_influence_20261109.py`. For six staple quaternion sum `S=R V` with `0≤R≤6` and coupling `β≥0`, the selected original one-link Haar conditional obeys `P(t(UV)≤0 | staples)≤3 exp(−βR/2)`, using the concrete SU(2) Haar cap `H(t≥1/2)>1/6`. Thus `P(t≤0)≤P(R<r₀)+3 exp(−βr₀/2)`, a quantitative reduction of this **local** large-field probability to actual original frustrating-staple mass. This proves a finite-volume-uniform aligned-staple conditional tail, not the requisite large-field **spatial covariance** bound.

With opposite six-staple boundary data, the same original conditional has `L1 ≥ 2(1−6e^(−3β))`, tending to 2. This **rules out uniform bare-link L1 Dobrushin q<1 at diverging bare β** for that boundary class, but does NOT refute fixed-physical-cube Dobrushin, gauge-invariant Wilson correlations, CMP116 or Clay. The distinguishing single-link event is gauge variant. At β=2, a degree-four rational Taylor lower bound certifies `L1≥218/115>1` with no floating-point quadrature.

**Physical and Agda acceptance remains open:** the selected SU(2) Haar/conditional/staple realization must still be kernel-welded to the original carrier; the actual *spatially connecting bad polymer mass* and CMP116 small/large source decompositions must be bounded uniformly. Do not claim the new one-link probability estimate is the D1.03 physical covariance result. Remaining E1, D2, N1, G1 physical endpoints unchanged.

## 9 November 2026 — latest 23-producer physical audit and true all-word E1/D1 source

**Current focused ledger:** [Docs/physics/YMClay23PhysicalProducersCurrentMaxCut20261109.md](../physics/YMClay23PhysicalProducersCurrentMaxCut20261109.md). This reconciles all 23 proposed E1.01–07, D1.01–04, D2.01–05, N1.01–03, G1.01–04 owners against the *latest* original SU(N) variable-cutoff real Wilson source, finite epsilon–N gauge-cylinder laws, the real CMP116 direct route and especially the full original small-field + large-field decomposition. Original analytic/continuum/spectral endpoint witnesses are not yet inhabited.

**New source proof (same original physical family):** `YMClayE1D1OriginalVariablePlaquetteWordsExact.agda` takes the original `Plaquette.PeriodicPlaquette n` carriers at **every** n, evaluates arbitrary finite words as products of the *actual* positive-plaquette real Wilson traces, and inductively proves original gauge invariance for **every word length**. Any original changing-cutoff word section is gauge invariant. `originalAllLengthWordE1D1CovarianceIdentity` connects its two-word actual E1 finite cylinder expectations to the original real D1 connected covariance. `originalAllLengthWordMixedJetIsD1Covariance` connects these same word labels to the preexisting native real finite two-J mixed-log coefficient; this is the formal jet and **not** an independently proved CMP116 analytic derivative. The file is imported into `YMClayOriginalWilsonPhysicalRegression`.

**The E1.02 vs E1.03 boundary:** arbitrary all-length Wilson words are a real **finite cylinder** source on changing lattice carriers, but their arbitrary n-dependent locations do not by themselves define consistent fixed-physical-support continuum cylinders. Actual cutoff/volume convergence and renormalized noncollapse of such tests remain physical E1.03/N1. Do not mark continuum existence closed.

**The D1.02 vs D1.03 boundary:** native original real same-source formal mixed J/covariance is established on each finite Wilson measure. To claim full 4D clustering, inhabit the literal CMP116 analytic source identity, **full original measure vs small-field CMP116 plus large-field remainder**, and a positive cutoff-independent physical decay rate for both terms. A selected small-field source estimate is insufficient.

**D2/G1 unchanged:** full OS Hamiltonian spectral detection and all compact simple gauge groups remain physical research requirements, not consequences of the finite word grammar. Status SOURCE_WRITTEN / KERNEL_OPEN / PHYSICAL_OPEN.

## 7 November — final source-validity cuts on PR #1444

The native E1 source now selects an explicitly proof-bearing gauge-invariant original Wilson polynomial cylinder class (`SelectedNativeCylinderAlgebra`; example `OriginWilsonPolynomial`) instead of all arbitrary n-sections. `PhysicalRealConverges` uses an explicit epsilon--N definition and `PhysicalRealSequentialConvergenceLaws` carries standard topology; no tautological `lim(s)=lim(s)` can close E1. `YMClayE1VariableCutoffCylinderLimitExact` uses explicit cutoff-indexed congruence and arithmetic convergence transports with no inferred holes, and its physical owner derives finite integration laws from actual native variable Wilson/Haar.

For D1, `YMClayD1OriginalRealCMP116VariableCutoffExact` now **derives** its exact real original covariance identity via `YMClayOriginalWilsonFiniteTwoSourceJetExact.originalWilsonMixedJetIsSameFiniteCovariance` and asks only for genuine analytic CMP116-to-original-literal-J identification and physical rate, rather than another independent covariance identity.

The source-valid full-Gibbs route is `YMClayD1OriginalFullWilsonSmallLargeFieldExact.originalFullWilsonUniformGeometricClustering`: original full covariance <= small-field CMP116 source + large-field remainder, both controlled by the same cutoff-independent physical-block geometric profile q<1. It is a mathematical conditional compiler. Published CMP116 four-dimensional small-field bounds do **not** supply the original full Gibbs large-field error; Bałaban CMP119 convergent expansions are stated in superrenormalizable scope, not a completed 4D full Yang–Mills measure. Missing hard D1 inputs are exactly `originalFullCovarianceBelowSmallPlusLarge`, `smallFieldEnvelopeCalibration`, `largeFieldErrorCalibration`, `smallFieldGeometricRate`, `largeFieldGeometricRate`, source admissibility and geometric physical calibration.

D2 H2/H3 OS semigroup and R287 cyclicity, N1 H6 Ward/Maxwell or RG cumulant, G1 all compact simple physical continuation remain the same cross-cutting terminal science. An Agda source-written record with physical theorem-valued fields is not a proof of those inputs. Only exact-head `parallel_checker` + trust audit can certify the formal code; no such receipt exists from this session. Clay completion is not claimed.

---

## 7 November — CLAY YM production sprint, E1 genuine convergence + D1 full Wilson

Current canonical max-cut remains **E1, D1, D2, N1, G1**, not a 1024-link/observer/KK package. See `Docs/physics/YMClayMinimalEndpointMaxCut20261107.md`.

**E1 now source-written** in `YMClayE1VariableCutoffCylinderLimitExact` (safe, carrier-parametric; fully explicit all-cutoff convergence transports) and `YMClayE1OriginalSUNFiniteCylinderLawsExact` (actual original varying-link Wilson/Haar finite normalization, positivity, additivity, scalar multiplication; concrete gauge-invariant original plaquette polynomial test algebra by induction). `ActualSelectedOriginalSUNConvergence` now requires **epsilon–N** convergence of native original Wilson expectations on that **selected** gauge-invariant algebra, not reflexive equality against an arbitrary `limit` selector and not all n-dependent sections. UV/IR existence and full 4D QFT axioms are still unproved.

**D1 now source-written** in `YMClayD1OriginalRealCMP116VariableCutoffExact` (actual native real Wilson two-J jet, physical q<1 rate) and `YMClayD1OriginalFullWilsonSmallLargeFieldExact` (published **small-field CMP116** + genuine full-original **large-field** error; combined amplitude/physical geometric rate). Correct published source provenance: Bałaban CMP109 I and CMP116 II are **four-dimensional small-field approximation** theorems; CMP119's convergent complete large-field expansion scope is **superrenormalizable models**, not automatically the complete original four-dimensional YM. The full original-measure source decomposition, nonperturbative cutoff/volume-uniform large-field error and uniform positive physical rate are the outstanding D1 analytic inputs. A citation to a published small-field estimate cannot inhabit those.

**D2** already has R287/T5 cyclicity and `YangMillsClayCMP119CoreSemigroupH3Exact`, but physically selected E1 Wilson OS dense cyclicity, spectral-measure lower bound, subgap-state detection and full-sector proof on SAME H_OS are required. **N1** original same-source Ward/Maxwell H6 or actual fourth-cumulant survival; **G1** genuine all-compact-simple-G physical continuation, including global forms/central quotients, not an SU(N)-only quantifier.

**Verification:** new owners regression-imported and GitHub source read back. No local Agda or `parallel_checker` available; no exact-head accepted proof or complete Clay solution. Do not promote conditional records to closed physical theorems.

---

## 7 November: original LOCAL two-plaquette Wilson physical D1 test class and marked-source identity

`YMClayOriginalVariableWilsonCovarianceSourceExact.agda` additionally constructs `originalLocalPlaquetteTraceAt n p` for **every** original positive plaquette `p : Plaquette.PeriodicPlaquette n` at every changing cutoff `n`. This uses the actual original Wilson plaquette holonomy and selected SU(N) real trace—not a synthetic test or one global all-lattice action. `originalLocalPlaquetteTraceAtGaugeInvariant` consumes `Variable.periodicSUNPositivePlaquetteGaugeTrace`; `originalLocalPairProductGaugeInvariant` proves any two selected plaquette insertions produce a gauge-invariant original test.

Most importantly, `originalTwoLocalWilsonMixedLogIsOriginalD1Covariance` directly instantiates **the original real-valued** `YMClayOriginalWilsonFiniteTwoSourceJetExact.originalWilsonMixedJetIsSameFiniteCovariance` on these two local plaquette insertions. For all n and all p,q it identifies the actual original same-source real mixed-log two-J coefficient with the **same** `originalWilsonConnectedCovariance n` on the changing four-torus; no auxiliary rational `R320` source introduced. Together with `originalE1LocalPlaquetteConnectedCovarianceIsSameD1`, this welds E1 finite observable, physical two-source marked J, D1 covariance on precisely one selected original finite Wilson measure.

**Decisive remaining analytic D1:** derive a quantitative original-source CMP116/RG clustering bound on exactly these physically located plaquette pairs and the chosen renormalized fixed-physical-size Wilson observables; prove a positive physically calibrated rate uniform in a→0 and volume→∞. A single microscopic plaquette has support O(a) and its naive trace may collapse to the identity, so this is NOT N1, no continuum source and no mass-gap claim. Full E1 nontrivial local continuum construction, D2 full spectrum, N1 survival and G1 remain OPEN. No Agda exact-head parallel_checker receipt.

## 7 November original Wilson E1 physical local-test producer, no new carrier

`YMClayOriginalVariableWilsonCovarianceSourceExact` now contains a literal n-dependent **gauge-invariant** real Wilson cylinder subalgebra: `OriginalGaugeInvariantSection` states invariance under the original variable periodic-site gauge action at **each n**, and the source proves `originalGaugeInvariantZeroCylinder`, `originalGaugeInvariantUnitCylinder`, `originalGaugeInvariantSectionAdd`, `originalGaugeInvariantSectionScale`, and `originalGaugeInvariantSectionProduct` from the actual Wilson matrix/gauge operations rather than a second arbitrary cylinder carrier. In particular, `originalSixPlaquetteDeficitSection` is the native six-positive-plaquette Wilson action density of the changing four-torus, `originalSixPlaquetteDeficitIsGaugeInvariantSection` consumes the real selected `Variable.periodicSUNSixDeficitGaugeInvariant` theorem, and its square remains in the same algebra. `originalE1SixDeficitCovarianceIsSameD1Source` is an exact equality of E1's second moment and D1's original connected covariance of that physical gauge-invariant cylinder at **every cutoff**.

**What this actually closes:** the E1 physical cutoff-dependent **gauge-invariant polynomial cylinder closure and native Wilson-deficit generator** and its same-measure E1/D1 covariance source equality. These are finite proofs, not yet the projectively compatible **bounded-support localized continuum subalgebra**. The six-plaquette action sums the entire lattice; it does NOT itself furnish local-test support or a nonzero renormalized continuum observable. Required E1 physical locality, ultraviolet scaling/convergence, Osterwalder-Schrader limit and axioms, D1 uniform original covariance bound, D2 full cyclic spectral detectability, N1 original continuum noncollapse and G1 all groups remain OPEN. Neither scalar ℝ nor matrix Haar is genuinely kernel-accepted here; source-written and regression-imported only.

**Additional exact E1↔D1 source weld:** `actualE1D1SameWilsonConnectedCovariance` is proved in `YMClayOriginalVariableWilsonCovarianceSourceExact` for **all** cutoff-dependent original cylinder sections and **all** n, by literal definitional identity with `YMClayE1OriginalSUNDependentCylinderExact.actualOriginalWilsonCylinderExpectation`. Thus E1's finite cylinder sequence and D1's finite connected covariance are now the **same selected original real physical measure**, not merely two records with matching symbolic names. This is a finite identity, NOT selected source convergence or uniform covariance decay; the same true original ℝ ↔ historical rational T5 source scalar representation and actual Wilson CMP116 estimate remain outstanding.

## 7 November continuation — literal all-cutoff REAL Wilson connected covariance

New source owner `DASHI/Physics/YangMills/YMClayOriginalVariableWilsonCovarianceSourceExact.agda` constructs **the actual changing-cutoff SU(N) Wilson covariance directly in the same original family** `YMClaySUNVariablePhysicalCutoffFamilyExact.physicalFiniteCutoffMeasure` for every `n`. It uses the original `Codec.decodeOriginalBonds (suc n)` and **proved product-Haar integral congruence** `YMClaySUNMatrixProductHaarC3Exact.productIntegralCongruent` to establish `originalWilsonExpectationExtensional`. Hence `originalWilsonConnectedCovarianceSymmetric`, `originalGaugeInvariantProduct`, and `originalWilsonGaugeInvariantConnectedCovariance` are proved algebraically for arbitrary finite test cylinders on the actual n-dependent ℝ-valued Gibbs measures, not via an independent n=3 pushforward or unrelated rational T5 record. Imported in `YMClayOriginalWilsonPhysicalRegression`.

**Sharp remaining D1:** prove one quantitatively cutoff/volume-uniform rooted-shell/exponential bound on `originalWilsonConnectedCovariance n F G` for the physical gauge-invariant localized F,G and chosen distance and β(n) scaling, then relate that very original real expectation to the selected rational (ℚ) T5 `R320` consumer without equating distinct scalars by fiat. The existing `YMClayD1OriginalCovarianceToR320Exact` identifies the selected ℚ mixed-J Hessian with its own ℚ-valued finite covariance; **it does not itself identify that sequence with ℝ-valued n-dependent `YMClaySUNVariablePhysicalCutoffFamilyExact`**. The new module supplies the *concrete real physical side* of that remaining weld, not a rate or limit.

**E1/D2 owner alignment:** independent #1444 E1 constructors for true varying configuration carriers and selected cylinder limit-state laws now exist, and the finite rational invisible-sector example correctly falsifies an unqualified selected-covariance → whole OS spectrum inference. Neither the original admissible local cylinder continuum convergence, whole-H spectral detectability, N1 or all compact-simple G follows from this finite theorem.

**Trust status:** source-written on #1444 and regression-imported, no exact-head Agda 2.9 `parallel_checker` receipt; the ℝ analysis facade has external/postulated authority. No physical endpoint claim.

## 7 November 2026 — E1 original changing carriers and D2 invisible sector

`YMClayE1VariableCutoffCylinderLimitExact.agda` proves normalized/positive/additive/homogeneous selected real cylinder limit-state laws while preserving `Configuration : Nat → Set`; `YMClayE1OriginalSUNDependentCylinderExact.agda` identifies each finite component with the **literal n-dependent original Wilson-Gibbs/Haar family**. The unrestricted n-dependent section algebra is not an automatically convergent continuum observable algebra; E1 still requires a physical gauge-invariant local selection, compatible embeddings, actual selected convergence/tightness and complete 4D axiomatic reconstruction.

`YMClayD1OriginalCovarianceToR320Exact.agda` proves selected R320 decay iff the actual finite covariance rooted-shell inequality; that **physical inequality remains open**.

Independent exact-rational counterexample in `scripts/check_ym_selected_covariance_spectrum_bidi_20261107.py`: selected covariance `(1/2)^t` can coexist with an invisible slow transfer eigenvalue `n/(n+1)` and full gap `1/(n+1) → 0`. Thus D2 MUST derive a full-sector/cyclic-spectrum detection theorem for the **same** reconstructed YM OS Hamiltonian rather than promote a bound on a strict selected subspace to the full spectrum. Do not add this as an independent Clay condition: it is the mathematical premise for the chosen spectral-clustering proof.

No Agda exact-head `parallel_checker` receipt, original source analytic bound, continuum theory, physical same-H gap, N1 or all-group result is claimed.

---

## 7 November 2026 — implemented D1 narrow original-source equivalence

`YMClayD1OriginalCovarianceToR320Exact.agda` is the new source-written, regression-imported exact bridge: selected normalized T5 mixed-log Hessian at cutoff `n` = **same finite original measure's actual connected covariance** at `n`. It transports the single genuine physical rooted-shell bound to R320 in BOTH directions, and consumes it through already-written Route-S H1/R313/R296 to produce the selected R333 finite source. The single open hard estimate is the ORIGINAL, physically cutoff/volume-uniform covariance shell inequality; no separate formal-jet theorem, generic J oracle or second coarse density is needed.

E1's genuine limiter is original Wilson physical cylinder tightness/convergence and full four-dimensional Schwinger/OS QFT axioms. The previously added general E1 limit-state adapter duplicated already-existing `YangMillsLiteralRealCylinderLimitPhysicalMeasureExact`, `YangMillsFinitePhysicalMeasureContinuumOS2Exact` and symmetry-limit owners; it was deleted. Reuse those existing source proofs. Keep D2 physical OS spectral semantics and N1 noncollapse independent.

`parallel_checker` exact-head and trust receipt **not available**; the new theorem is source-written, not kernel certified. Do not claim Clay.

---

## 7 November 2026 — canonical CLAY endpoint cut (supersedes oversized M.01–M.05 priority)

The **authoritative minimum proof frontier** is now [`YMClayMinimalEndpointMaxCut20261107.md`](../physics/YMClayMinimalEndpointMaxCut20261107.md). Prior ten-gate and M.01–M.05 inventories are **implementation dependencies only**, not Clay prerequisites or the active priority list.

For each externally specified compact simple group `G`, prove:
- **E1:** construct the actual nontrivial candidate four-dimensional continuum Yang–Mills Schwinger theory from the selected source, with full accepted OS/Wightman-strength axioms and local gauge-invariant observables.
- **D1** (only for the selected direct source route): prove one physical cutoff/volume-uniform selected R320 differentiated Wilson source bound on **that exact E1 family**; consume R295/R313/R296/R333 rather than rebuilding the compiler.
- **D2:** construct the *same reconstructed* `H_G`, vacuum and spectral transfer identification, proving `sigma(H_G) ⊂ {0} ∪ [Delta_G,∞)` with `Delta_G > 0` in physical units.
- **N1:** supply an actual nontrivial continuum local gauge-invariant witness on the E1 source; the existing RG fourth-cumulant charge route is sufficient but stronger than logically necessary.
- **G1:** quantify independently over all externally specified compact simple `G`, allowing group-dependent mass-gap constants. No SU(2) or SUN-only scope promotion.

R443/R445/F19/CMP119/122/CMP116, fixed 1024-link and abstract compatibility record work is **deprioritized** unless it directly supplies E1/D1/D2/N1/G1. No observer, TSVF, Lorentz or KK work enters Clay YM.

**Important semantic check:** Existing `BalabanOSMassGapClosure` and `YangMillsClayLiteralTopDownConstructionExact` package endpoint semantics in externally supplied `Set` fields. Their assembly theorems are not an unconditional derivation of a physical 4D QFT. A required endpoint cannot be paid by passing a new record containing its desired conclusion.

Status: source audit and roadmap correction committed; no Clay proof, Agda exact-head receipt or physical endpoint source supplied by this update.

---

## 6 November YM M.01/M.02 deep source implementation

New original-source Agda owners: `YMClayNative1024ClosedReindexHaarConsequencesExact`, `YMClayNative1024WeightedWilsonReindexExact`, `YMClayNative1024FullMarkedWilsonReindexExact`, `YMClayOriginalWilsonF19ConcreteWeightExact`, `YMClayNativePairsSpectatorsFubiniExact`, and `YMClayOriginalWilsonPhysicalF19PartitionExact`. The last three identify the original complete Gibbs density as the interacting F19 pair/spectator weight and provide an arbitrary-integrand flat ordered product-Haar to nested pair/spectator equality. The physical original Wilson partition is source-written as the same nested F19 fine partition. The F19 full two-marked and normalized effective-density identities are instantiated using that physical source.

Original finite 1024-link C3 and pair/spectator sorts are checked by an executed exact Python reference (46592 and 41792 swaps respectively), not Agda kernel acceptance. The independent physical-rate BIDI check establishes that a fixed q=1/2 lattice envelope corresponds to envelope rate log(2)/a; a finite continuum rate needs explicit cutoff calibration. A separate exact Q8 toy reference confirmed interacting non-Abelian finite fibre disintegration and rejected uniform bare-coarse substitution; it is not a continuous compact-SU(N) proof.

**Strict remaining source contracts:** Agda pinned parallel_checker acceptance; same full marked flat-to-F19 integration at the literal native coarse cylinder insertion, including the real scalar algebra; physically instantiated compact Borel SU(N) Haar on an integrable test algebra; CMP119/122 complete effective-action E/R/B/V and boundary/ghost equality at every physical scale; CMP116 literal uniform differentiated spatial localization and calibrated same-source time; genuine fine Wilson RP/half-space native-block compatibility and full complex OS positivity through continuum; nontrivial four-dimensional local fields, same H_OS and positive calibrated spectral gap. No invented physical inputs and no Clay completion claim.

---

## 6 November — YM-only all-word R445/OS and published Wilson RP (source implementation)

Two pre-existing, source-written finite Wilson results on the separate #1460 branch have been adapted as **YM-owned** Agda sources on #1444, with no dependency on TSVF/observer/KK:

1. `YMClayOriginalR445ReflectedAllWordGramExact.agda`: `actualNativeR445AllReflectedWordGrams` proves that the *original 1,024-bond fine Wilson-Gibbs measure* and its exact non-Abelian R445 pushforward give the same real reflected pairing for **any two finite coarse-observable words**. `originalFineOSPositiveTransfersToNativeR445` transports a nonnegative original pairing to the same native coarse pairing.
2. `YMClayOriginalR445PublishedWilsonRPWordWeldExact.agda`: `originalPublishedWilsonRPYieldsNativePositiveWord` invokes the existing `BalabanClayOSWilsonReflectionPositivityExact` published Osterwalder–Seiler / Menotti–Pelissetto owner, to infer positivity of the original R445 reflected word **under the literal original-to-published Wilson reflected-expectation identity, gauge invariance, positive-time admissibility and scalar order interpretation**.

Both are imported by `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`; original donor/provenance retained.

**Do not promote a named imported theorem as a concrete Wilson RP instantiation:** the published owner is a `WilsonReflectionPositivityData` record of theorem premises, not a literal constructed analytic continuum Wilson measure. Source-specific `sourceIdentifiesActualWilsonReflection`, reflection plane/support, real-to-complex OS star and positivity under physical cutoff/volume limits still need proof. All-word pushforward is **not** CMP116 decay or an OS mass gap.

M.01 actual closed `refl` kernel candidates remain in `YMClayNativeClosedThreeEqualitiesCandidateExact`, not a compiler receipt. M.02 original CMP119/122 complete-density equality, M.03 selected differentiated uniform CMP116 estimates, M.04 literal physical reflection/RP/limits, and M.05 nontrivial R4 OS reconstruction and strictly positive physical gap remain *unpaid*. This change neither resolves the Clay theorem nor imports any observer/KK theorem.

**Verification:** GitHub source commit/readback only; exact-head Agda `parallel_checker` receipt not obtained.

---
## 6 November — finite ORIGINAL Wilson reflected cross-Gram transport (new source theorem)

The existing original same-source native R445 OS pullback has been strengthened to **two different real observables**, not merely the quadratic diagonal. New declarations in `YMClayOriginalWilsonNativeOSPullbackExact.agda`:

- `originalFineOSCrossGram`: original fine Wilson reflected bilinear expectation `E_mu[(Theta_f f) g]`.
- `actualR445CoarseOSCrossGram`: original weighted R445 pushforward expectation `E_B*mu[(Theta_c F) G]`.
- `originalR445CrossGramIsFineWilsonCrossGram`: exact finite equality for all coarse real tests `F,G` when the *literal* native block intertwines the selected reflections.

This is derived by the same existing Haar cylinder congruence, unchanged Wilson density and unchanged partition, using the actual native non-Abelian block. It does **not** assume a separate covariance, a bare coarse Wilson weight, or isolated CMP122 crossing-fragment positivity.

**Status:** source-written; not Agda-kernel accepted. `NativeBlockReflectsExactly` is still an explicit premise, as are the selected ordered Haar laws. Full fine Wilson RP, positive-time support preservation, complex adjoint transport, physical CMP119/122 whole-form identification, cutoff/volume limits, CMP116 localization and the same continuum OS spectral gap remain unproved for the selected original family. No such gate is marked closed by this finite Gram identity.

**Next strict max-cut:** instantiate native reflection geometry and fine Wilson RP on the original gauge-invariant positive-time algebra, then transport the full Gram matrix through the complete CMP119/122 source/continuum; in parallel complete M.01 kernel receipt and M.02/M.03 selected-source and uniform-rate applications. Keep the pure 4D YM chain independent of TSVF/KK/observer claims.

---
## 6 November correction: same ORIGINAL R445 reflected OS form, no per-polymer PSD tax

New physical-source Agda owner `DASHI/Physics/YangMills/YMClayOriginalWilsonNativeOSPullbackExact.agda` defines the real two-point reflected quadratic forms **from the exact original fine 1024-bond Wilson–Gibbs normalized expectation and its exact R445 native weighted pushforward**, not from independent fine/coarse reflection forms.

- `originalR445ReflectedQuadraticIsFineWilsonQuadratic` proves the **literal whole-form equality** `Q_coarse(F) = Q_fine(F ∘ B)` using the existing original product-Haar weighted cylinder congruence and the single selected same-source partition.
- `originalR445OSReflectionPositiveFromSameFineWilson` derives `Q_coarse(F)≥0` from the original selected Wilson fine reflection positivity and the physical block's positive-time support and reflection-equivariance properties. This is restricted to the chosen **real** gauge-invariant test algebra; a general complex OS statement must also transport its adjoint.
- **Reuse already present:** `BalabanClayExactOSPullbackRecombinationExact`, `BalabanClayOSPullbackBlockingBridgeExact`, `BalabanReflectionPositiveCoarseGrainingTransportExact`, and `ReflectionPositiveBlocking`. Their general RP transport does NOT demand each separately labelled CMP122 crossing-polymer term be positive.
- **Exact unpaid geometry/source:** establish for the *literal native R445 ordered two-link block* that `NativeBlockReflectsExactly` holds at the selected OS plane and that coarse positive-time observables pull back to fine positive-time observables, together with original real Wilson fine RP (standard imported finite Wilson theorem). Then prove equality of the FULL reconstructed CMP119/122 reflected OS form with this original coarse pullback after recombination, including crossing terms. An Eq.1.100 absolute crossing bound alone neither proves nor disproves whole-form RP.

**Revised M.04:** do not require an unnecessary separate PSD theorem for each crossing-polymer summand if the selected entire original OS form is reflection-positive by exact source pullback. The genuinely new quantitative tasks remain the cutoff/volume-uniform CMP116 marked bound and physical RG/T5/OS limit.

**Acceptance:** source-written / no Agda kernel receipt / original exact field and selected reflection semantically uninstantiated; no Clay promotion.

---

## 6 Nov latest max-cut: ORIGINAL TWO-PLAQUETTE MARKS / WHOLE R445 SOURCE / F19 EFFECTIVE FIBRE

**Implemented on PR #1444 (source-written; Agda kernel unverified; no CI claim):**

1. `YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact.agda` derives `originalPlaquetteMarkGaugeInvariant` and `originalPlaquetteMarkPointwise` directly from the *actual* periodic SU(N) plaquette holonomy and real trace. The marked source `actualOriginalTwoPlaquetteNormalizedSource` has an original-gauge-invariance proof `actualTwoPlaquetteSourceIsGaugeInvariant`, the exact normalized moment-polynomial theorem `originalTwoPlaquetteActualMomentPolynomial`, and the original real-Wilson covariance `originalTwoPlaquetteMixedJetIsActualWilsonCovariance`. This works on **every changing finite cutoff n**, not just the fixed 1,024-link side-four sample. Local insertion traces and real Haar are still typed physical inputs, not a constructed Borel SU(N) matrix implementation.
2. `YMClayOriginalWilsonNativeMarkedPushforwardExact.agda` proves for the actual side-four native 1,024-link full Gibbs family that `fineWilsonMarkedPartitionIsNativeR445Pushforward` and `fineWilsonNormalizedMarkedIsActualR445Normalized`: these are equalities of the **entire two-variable original marked partition**, not merely its mixed coefficient. `originalMarkedR445IsSameFiniteMomentPolynomial` composes existing exact real-division/numerator laws; `originalNativeR445MarkedSourceGaugeInvariant` retains the original native coarse-gauge law. No fictitious bare coarse Wilson density.
3. `YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact.agda` specializes **existing** full noncommutative weighted fibre disintegration F17/F18/F19 to the entire two-marked polynomial on the actual 64 original disjoint ordered link pairs **plus all 896 spectators**. `originalFullTwoMarkedFibreEqualsActualEffectiveDensity` proves the fully interacting fine/true effective density equality; `originalSamePartitionNormalizedMarkedSource` uses the **same** partition on both sides; `originalSelectedEffectiveMarkedDensityStrictlyPositive` derives strict positivity from the original positive fine weight and existing Haar laws. This all-arbitrary-weight theorem still needs the native 1024-bond codec/reordering witness to identify the interleaved F19 carrier with literal original Wilson coordinates.

**Exact finite bridge now completed at source level:** full marked source on selected native Wilson -> its genuine R445 weighted pushforward -> existing R320 covariance; literal positive plaquette marks on every finite original cutoff; F19 64+896 effective density with an arbitrary coupled interacting weight. Generic source differentiation already exists in `YangMillsClayPinnedCMP119RealTwoJSourceExact`, `BalabanObservableIndexedT5SourceMeaningRound403Exact`, `BalabanCMP116SelectedJCommonDomainRound327Exact`, and the bounded finite compact-SU(N) analytic proof in `YMClayR320BoundedMarkedSourceLemma20261106.md`. It is *not* a fresh research lemma.

**True selected physical cut, exact owner obligations:**

| ID | Original theorem to produce | Reuse | Current status |
| --- | --- | --- | --- |
| `M.01` | Selected 1,024-link permutation program equality reorders the **actual** original positive-bond decoder into the 64 native ordered block pairs and 896 spectators, with same Haar product and full Wilson weight | `YMClayNativeClosedThreeEqualitiesCandidateExact`; `YMClayNativeSideFourPairSpectatorSortProgramExact`; F17/F18/F19 | Agda candidate, kernel not confirmed |
| `M.02` | Exact original selected 4D continuous SU(N) Borel Haar, normalized trace and finite matrix interpretation, original CMP119/122 **full** E/R/B/V/ghost/background `rho_k = T_k e^{-S_k^{eff}}` and selected R-operation integral equals native weighted Wilson pushforward at every physical scale, including reflection supports | `SUNMatrixCarrier`; `YMClaySUNVariablePhysicalCutoffFamilyExact`; `BalabanCMP119Section2CompleteDensityDictionaryExact`; `BalabanCMP119Section2FiniteDensityEvaluationExact`; CMP122 Eq.1.100 | **Physical same-source theorem**, not supplied by the finite algebra |
| `M.03` | Actual marked plaquette/loop insertions and root/time/support on the **same renormalized** CMP119/122 density are admissible CMP116 coordinates; published selected CMP116 differentiated localized response inequality applies to them uniformly | `BalabanCMP116SelectedTwoSourceLocalizationRound454Exact`; R327, R342, R344, R467; literal WEXT; new two-plaquette owner | **Decisive analytic application**, not another `D^2\log Z=Cov` rule |
| `M.04` | Original differentiated shell envelope with physical units and `a\to0,L\to\infty` quantitative tails; whole-form OS pullback through a reflection-compatible native block, not positivity of each CMP122 crossing summand | `BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact`; R445/T5/Bishop; `BalabanCMP122ROperationReflectionSupportCutExact` | **Physical uniformity/reflection** |
| `M.05` | Noncollapsed, non-Gaussian 4D OS reconstruction of **that same continuum source**; local density/cyclicity, original self-adjoint H, strictly positive physical mass gap and full externally selected compact-simple group scope | R479/R482, R333, `YMClayRGLossBudgetToNonGaussianExact`, OS endpoints | **Continuum/Clay endpoint** |

**Important falsifiers:** a formal 2-J jet does not prove spatial decay; a bounded analytic plaquette source does not prove CMP116 localization; a one-step weighted pushforward need not be bare Wilson; F19 interleaved pairs do not automatically equal the original native 1024-bond vector; an absolute crossing-polymer bound does not imply reflection positivity; an OS gap on a mismatched Hamiltonian is not a Clay mass gap. Treat each as BIDI-negative unless the original physical source equality is proved.

---

## 6 November 2026 correction — the FINITE analytic-J identity is NOT a new Clay leaf

The previously reported "formal jet -> actual analytic mixed derivative" should not be presented as an independent, unproved *mathematical* theorem for bounded finite original Wilson marks. The rigorous finite continuous-compact-Haar proof was already written in [YMClayR320BoundedMarkedSourceLemma20261106.md](../physics/YMClayR320BoundedMarkedSourceLemma20261106.md): for each finite original Wilson Gibbs law and bounded local marks F,G, M(s,t)=E_mu exp(sF+tG) is holomorphic on a uniform nonzero neighbourhood, and (d_s d_t log M)(0,0)=E_mu(FG)-E_mu(F)E_mu(G). For |F|,|G|<=2, |s|+|t|<log(2)/2 is sufficient. Uniform *analyticity* is not uniform *spatial clustering*.

**New genuine same-source finite integration proof:** `YMClayOriginalWilsonAffineMarkedPartitionExact.agda`, with `originalAffinePartitionIsExactNumeratorPolynomial`, directly constructs the ORIGINAL unnormalized Wilson product-Haar marked integral
`Z_aff(s,t)=int exp(-S)(1+sF)(1+tG) dH`
and proves equality to `Z_0+s N(F)+t N(G)+st N(FG)` using the EXISTING integration/numerator linearity theorems. The two source marks are the actual Wilson observables, not a second J oracle. Consequently the affine and exponential source have the same first and mixed derivatives at zero by elementary bounded analytic differentiation. The existing `YMClayOriginalWilsonFiniteTwoSourceJetExact`, `BalabanObservableIndexedT5SourceMeaningRound403Exact`, `NormalizedTwoSourceConnectedCumulantExact` and `BalabanCMP116SelectedJCommonDomainRound327Exact` already own the coefficient, covariance, observable-index and common-domain compilers. **Status:** original integral polynomial equality SOURCE-WRITTEN, not Agda-kernel-accepted; bounded exponential derivative analytic theorem proved in source-facing mathematical dossier, not yet a native Bishop/Agda differentiability proof.

**Do not retain finite derivative calculus as a new independent physical gap.** The next source-specific mathematical obligation is different: identify the COMPLETE renormalized CMP119/CMP122 effective density and exact selected marked insertion with the actual original Wilson source at each scale (including E/R/B/V, boundary/ghost normalization), then instantiate CMP116's published *localized* mixed-source estimate on those precise original supports, with a cutoff- and volume-uniform physically calibrated distance/rate. An arbitrary compact plaquette has a bounded analytic source; that alone says nothing about decay between two distant plaquettes. Existing R342/R344/R467/R482 and literal two-Wilson quarter-dyadic authors compile the subsequent bound/gap only after those physical estimates and limit semantics are supplied.

**Remaining maximal physical cut:**
- `Y.01/R445`: original Wilson positive-Haar/Gibbs source ↔ actual CMP119/CMP122 complete E/R/B/V/ghost/background density and RG pushforward, including reflection-compatible crossing R-terms, all changing cutoffs/volumes.
- `Y.02/R320`: select the original two local/loop insertions as admissible CMP116 analytic marks of *that same renormalized density* with exact root/support and source-time calibration. The generic finite mixed derivative is ALREADY accounted for.
- `Y.03/T5`: pay original cutoff/volume-uniform connected rooted-shell response, quantitative physical RG drift/defect tails and the same expectation limits; reflection positivity through the physical R-operation.
- `Y.04/R333/Clay`: reconstruct one noncollapsed four-dimensional Euclidean/OS theory with same H, dense local physical sector, strict positive gap in real units, nontriviality and the externally prescribed compact simple gauge-group scope.

No independent abstract J calculus, generic new KP/RG proof or artificial coarse Wilson measure is an admissible replacement.

---

## 2026-11-06 follow-on: finite original Wilson two-source jet (Y.01/Y.02)

**Golden source:** `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteTwoSourceJetExact.agda`, in parent [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Independent exact reference:** `scripts/check_ym_original_wilson_two_source_jet_reference.py`. Canonical TOE import, dedicated physical root `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, and targeted Agda CI now name the two finite source owners. The physical root is deliberately not `--safe`, because the legacy real/Haar analytic authorities are a transitive proof boundary. No Agda kernel or transitive trust receipt has been observed.

| Exact ID | Source term | Status and remaining physical payment |
| --- | --- | --- |
| `Y.FIN.01` | `originalWilsonDensityIsSelectedWilson`, `originalWilsonPartitionIsSelectedProductHaar`, `originalWilsonFiniteIntegrationLaws`, `originalWilsonUnitNumeratorIsPartition`, `originalWilsonInsertionNumeratorAdd`, `originalWilsonExpectationOfUnitIsOne` | Source-written: literal changing-cutoff SU(N) Wilson/Gibbs density and partition are anchored to the *same* previously constructed finite product-Haar measure; finite numerator additivity and unit partition follow from existing cylinder algebra. The unit-normalization proof additionally takes an explicit positive-denominator division-cancellation law; one-link compact Borel Haar realization is still an explicit input. |
| `Y.FIN.02` | `originalWilsonMomentAlgebra`, `originalWilsonNormalizedJet`, `originalWilsonLiteralJetDirections` | Source-written: define the formal two-source coefficients directly from one original finite Wilson normalized expectation; no independent moment/covariance object. The *analytic derivative* of the actual continuous-Haar source functional is not inferred. |
| `Y.FIN.03` | `originalWilsonMixedJetIsSameFiniteCovariance`, `originalWilsonMixedJetIsOriginalConnectedCumulant` | Source-written: literal finite formal mixed-log jet equals the same Wilson connected covariance by the original cumulant compiler. Kernel acceptance pending. |
| `Y.FIN.04` | `check_ym_original_wilson_two_source_jet_reference.py` | Exact rational BIDI reference: 19,683 exhaustive three-state cases and six simultaneous relabelings; changed-measure negative control rejected. This is not an SU(N) Haar integration or Agda check. |

| `Y.FIN.05` | `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.originalVariableN3IsNativeR445FineMeasure`, `originalN3CumulantIsNativeBlockedFineCovariance`, `originalN3LiteralMixedLogJetIsNativeBlockedCovariance`, `originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` | Source-written: at actual side-four n=3 the variable-cutoff Wilson measure is definitionally the original R445 1024-link fine Gibbs law. Both source marks pull back along the original non-Abelian native block; the finite jet equals the actual *weighted* R445→R320 pushforward covariance. No bare-coarse Wilson-law assertion or analytic CMP116 source bound. Kernel pending. |

**Revised original physical max-cut (do not promote from Y.FIN):** `Y.01` identify the entire real Wilson/gauge-fixed E/R/B/V/ghost/counterterm source with the selected CMP119/122 density/physical T-operation at every renormalization scale, not just the original finite Wilson action. `Y.02` prove that selected positive-time gauge-invariant local/loop insertions are admissible CMP119/116 analytic J directions, identify the genuine differentiated `log Z` with this formal jet, and preserve root/distance/normalization. `Y.03` derive *actual* cutoff/volume-uniform source decay, RG/continuum tails and reflection-compatible limits. `Y.04` construct the same limiting OS Hilbert/Hamiltonian and quantitative nontriviality/Clay scope. Reuse the CMP119/122/116, R344/R467/R482, Bishop/T5 and original Wilson–Gibbs owners rather than copying them.

**Acceptance:** new formal theorem = `SOURCE_PENDING_AGDA`; reference arithmetic = `VERIFIED_REFERENCE`; original CMP116 source applicability and physical estimates = `OPEN_PHYSICAL`. CI is a checker command, not a green receipt. Parallel-checker exact-head execution and transitive axiom audit remain required.

---


## 6 November — canonical R344 shared marked CMP116 half-rate direct weld

The *existing* `BalabanCMP116SharedMarkedDirectCalibrationRound344Exact` proves the shared-Hessian shell's conditional geometric $\frac14 C_H 2^{-d}$ bound, with selected physical source distance/time and (C_H≤1) as proof inputs. Two new terms `sameOriginalSharedMarkedHalfRateFiniteDecay`, `sameOriginalSharedMarkedHalfRateYieldsGap` (R344→R342→R467→R482) are source-written in `YMClayCMP119122116SelectedProducerWeldExact.agda`, Agda unverified. The actual original Wilson-Haar marked J applicability, uniform physical rate and OS limit are not derived from a name match. Exact four-cut Y.01–Y.04 is in `Docs/physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md`. Source contract audit now 12 donor owners / 6 bridge proof terms.


---

## 6 Nov 2026 — CMP119/116/122 source archaeology upgraded to exact reuse

**Do not regenerate Bałaban's mathematics.** Existing repo already owns CMP119 beta-driven full density + anchored *normalized* expectation, CMP122 complete-density UV/boundary reinjection, CMP116 finite differentiated/selected two-J localization, and R342→R467→R479/R482 positive transfer-gap compilers. New `YMClayCMP119122116SelectedProducerWeldExact.agda` imports and composes these on one source: beta coupling + localized CMP116 potential, R342→R467 finite same-selected covariance, and R342→R482 positive-gap rate without independent positivity token. No Agda compiler receipt or physical Wilson instantiation claimed. Source-owned statements are distinguished from original SU(N) Wilson, gauge/ghost physical density, original marked-J dictionary, source uniform physical rate and reflection-positive *crossing* R-operation.

Four actual same-Wilson physical payments **Y.01–Y.04** are specified in [CMP119/116/122 source max-cut](../physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md) and [current phases](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). New fail-closed source/CI contract: `scripts/check_ym_cmp119116122_same_source_contract.py`. The optional physical Dobrushin/Perron route is not a compulsory additional CMP116 source leaf.

---

## 6 November 2026 — same-original-Wilson constructive 4D continuum steelman / BIDI max-cut

**Primary theorem proposal:** [YMClayConstructive4DContinuumSteelman20261106.md](../physics/YMClayConstructive4DContinuumSteelman20261106.md). It explicitly derives the hypothetical nontrivial 4D continuum from ONE original compact-simple-G Wilson family, not six unrelated records, and proposes source-specific bounds for same-observable UV Cauchy limits, IR/crossing tails, literal CMP116 mixed-J decay, OS reconstruction and non-Gaussian survival. The existing R443/R445/R320/R333 owners are reused; unification #1460 remains downstream.

**New golden producer:** `DASHI/Physics/YangMills/YMClayRGLossBudgetToNonGaussianExact.agda` (source-written, **Agda kernel pending**): `finiteRGLoss`, `referenceChargeBelowCurrentPlusLoss`, `referenceRGUniformNoncollapse` from a reference `eta+B≤c0` and actual `c_n≤c_{n+1}+δ_n`, `sum_{k<n}δ_k≤B`; `asOriginalT5Nontriviality` instantiates the EXISTING T5 uniform fourth-cumulant lower theorem with this **derived** finite bound; `continuumRGChargeIsNonzero` imports existing T5 nonzero result. This does not construct the original source-specific charge/limit, and cannot assign a fictitious fourth-cumulant sign.

**Physical RG insight to test, not assert:** after actual 4D marginal and source renormalization, an original Wilson/CMP119/122 one-step residual may obey `δ_n≤A/((n+1)(n+2))+C 2^{-(n+1)}+h_n`, `Σ h_n≤H`; this gives `q≤q0+A+C+H<1` via the *existing* `YMClayPhysicalRGDriftToUniformInfluenceExact`, while bare O(g²) harmonic sums diverge. The actual Ward cancellation/marginal subtraction and full large-field/marked-J source error remain to be proved.

**Executed independent exact rational BIDI controls** (all illustrative, NOT physical): 192-step RG noncollapse, 64 exhaustive bounded charge configurations and 5 negative cases; 4×4 transfer Hankel Gram PSD, 128-step noncollapse and 7 false-positive negative controls; the UV rational n^-2+geometric+holes sum checked at depths 1,2,4,8,16,64,256,512, with a divergent harmonic control. The fixture `q0=1/4, A=1/16, C=1/32, H=1/64` gives `q=23/64`; NO Wilson measurement or Agda acceptance is inferred. New scripts `check_ym_rg_noncollapse_steelman.py`, `check_ym_clay_continuum_bidi_controls.py`, `check_ym_marginal_subtracted_uv_tail.py` committed and targeted by CI. Golden TOE root imports the new Agda module.

**Exact deliverable IDs (do not rename; promote only with physical proof receipts):**
- `CLAY4.F1`
- `CLAY4.A1`
- `CLAY4.A2`
- `CLAY4.A3`
- `CLAY4.B1`
- `CLAY4.C1`
- `CLAY4.C2`
- `CLAY4.D1`
- `CLAY4.D2`
- `CLAY4.D3`
- `CLAY4.E1`
- `CLAY4.E2`
- `CLAY4.E3`

**Status:** `CLAY4.D2` source-written mathematical compiler, Agda pending; `CLAY4.D3` derived conditional transport to T5, Agda pending; `CLAY4.F1` source-written original closed 1024-label candidates, kernel pending. `CLAY4.A1/A2/A3/B1/C1/C2/D1/E1/E2/E3` are physical same-source analytic or semantic construction work, NOT realized original continuum theorems. No CLAY endpoint acceptance claimed.

**Highest alpha execution order:** original one-step marked source/Dyadic Cauchy `A1/A2` and two-marked physical CMP116 shell `B1/C1/C2` in parallel, then one fixed-scale nonGaussian `D1/D2/D3`, exact original RP/OS/E(4) `E1/E2` and per-G `E3`; native `F1` kernel independently. Fail on unproved physical input rather than selecting a toy model.

---

## 2026-11-06 — YM proof-source / RG budget supplement

See [phase-specific exact update](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). F1 three original 1024-link equality proof attempts source-written, **no Agda receipt**. New original physical-cube RG arithmetic derives q=q0+B, with 128-step exact rational reference but actual continuous SU(N)/CMP116/OS physical coefficients and compact-group coverage OPEN. Files: `YMClayNativeClosedThreeEqualitiesCandidateExact.agda`, `YMClayPhysicalRGDriftToUniformInfluenceExact.agda`, `YMClayRGDriftOriginalGibbsInstantiationExact.agda` and `scripts/check_ym_rg_drift_budget_reference.py`. #1460 remains separate physical observer/KK lane; no child import. Full source contracts in `Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md`.

---


---

## 6 November 2026 — physical-cube CMP116/Dobrushin/Perron steelman, not generic bare-link repetition

**Primary new implementation and physical theorem spec:** [Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md](../physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md), wired into [phases/deliverables](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). The prior finite 1024-label C3/pair selection proofs remain open for kernel acceptance; this physical lane runs in parallel. Key genuine theorem is `PCUBE.P04`: find one (0≤q<1), independent of a,L, for weighted conditional Dobrushin matrix of the SAME original blocked compact SU(N) Wilson Gibbs state at fixed physical `ell`; source-native CMP116 marked-J / rooted-polymer is the competing route, and R467 source specialization already exists. Existing direct R479/T5 same-H spectral compiler should be reused. `YMClayPhysicalCubeDobrushinFromGibbsExact.agda` formalizes the exact conditional row/observable transport; no new coarse probability law is declared. No proof of the strict actual physical `q` or continuum mass gap is claimed.

---

# 6 November 2026 — canonical active execution queue (replaces repeated six-gate summary)

**ACTIVE PHASES, DELIVERABLES, ACCEPTANCE AND EXACT LEMMAS:** [YMClayExecutionPhasesDeliverablesExactLemmas20261106.md](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). This file's historical milestones remain preserved below. Do not mistake original source-written owners for kernel acceptance or proof of the full mass gap.

**P0 actual execution:** new `YMClayNativeOriginalSortMembershipCorrectExact.agda` contains source-written (1) membership-indexed `bubbleDesiredHeadWhenMember`, (2) inductive `AllSelectable` and (3) `originalSortToTargetCorrect`, on the actual original sorter. The next unproved original-target producers are C3 selectability and pair/spectator selectability+length. Exact native Python reference has passed 5,914 exhaustive distinct small permutations, all 1,024 original C3 and blocking steps, 46,592/41,792 swaps, both negative invalid-target controls; **not Agda**. `scripts/check_ym_sort_selectability_reference.py` recorded. Agda not installed in current local runtime; this source is **UNTYPECHECKED**.

**P1 finite source:** reuse original positive/signed Wilson plaquette, finite real Fubini, weighted Haar fibre laws F17–F22. Native SU(N) 6-plane C3 source composition exists. Still need original `Variable.periodicSUNGibbsDensity` same-decoder equation and separate selected CMP119 E/R/B/V action; true compact measurable Haar remains open.

**P2 physical:** R445 physical scaling, reflection compatibility, uniform estimates/continuum, R320 actual CMP116 differentiated mixed-J rooted-shell decay, R333 selected RP/OS same H positive gap, and external Clay all-compact-simple-group solution are **OPEN MATHEMATICS**. Original 219 field names remain bare Set, not 219 proved witnesses. No six-gate status was falsely decremented.

---

## 2026-11-05 — R443 original weighted Wilson–Gibbs spatial C3 and SEM.P02 nonvacuous group scope

- **R443.F09 SOURCE / KERNEL PENDING:** `YMClayOriginalWilsonC3WeightedHaarTransferExact.agda` defines the density with the **same original** `Variable.periodicSUNGibbsDensity`, the canonical 1024-positive-bond decoder and the original one-link product Haar. Its conditional source theorem derives **weighted** spatial C3 numerator and normalized expectation invariance from the ONE closed native C3 label equality **and** literal physical action density C3 covariance. It additionally constructs selected `Constructed.actualPeriodicProductMeasure` and proves the actual original physical cylinder numerator is the original 1024-vector numerator, and physical partition/normalized expectation are the same (source-written, using original `mulOneʳ` and `Congruence.productIntegralCongruent`). Thus no second Gibbs/partition is introduced. **Still OPEN:** kernel-accept the original C3 equality, prove the selected physical CMP119 E/R/B/V action C3 equality, genuine continuous SU(N) Borel Haar on the correct integrable tests, real scalar/trace instantiation, uniform RG/CMP116/OS/Clay.
- **SEM.P02 SOURCE / KERNEL PENDING:** `YMClayCompactSimpleScopeBidiNoVacuitySafeExact.agda` supplies a standalone `--safe` mathematical firewall: the selected internal group universe cannot be empty/one arbitrarily chosen group and claim all externally specified compact simple G. It requires a physical external group witness, bidirectional index map, exact group/equivalence and actual physical predicate meaning for both all-group implication directions. **Actual compact-simple classification/physical all-G transport OPEN.**
- **Independent local exact noncommutative reference executed:** original (4^4\) torus/1024 positive links with Q8 subgroup of SU(2); 32 original Wilson action C3 invariances, 32 independent local gauge invariances, 32 C3-cubed, 32 exact C3-symmetric weighted-orbit numerator equalities PASS. All 32 deliberately anisotropic-weighted C3 symmetry assertions FAIL, furnishing the correct negative control. `scripts/check_ym_original_c3_weighted_wilson_q8.py`. This does **NOT** verify full selected CMP119 E/R/B/V, continuous Haar or Agda.
- **Agda source audit correction:** original §proof-relevant Set-anchoring§ record's universe changed to `Set₁`, because equality between `Set`-valued propositions lives in `Set₁`; source-written and GitHub readback, **exact-head typecheck still pending**.
- Ledger currently **67 producer entries** (prior 66 + R443.F09). Original 219 named `Set` fields and 521 hint edges are unchanged, **0 individual physically interpreted field proofs promoted**. `Docs/roadmaps/YMClaySteelmanBidirectionalExactRemainingMaxCut20261104.md` carries full steelman/bidi. No writes to #1460 or ESD.

## 2026-11-04 — exact Yang–Mills 219-field / Clay-vocabulary semantic firewall and steelman-bidi

**Source/connector audit PASS (not Agda):** original 219/219 field declarations literally have type `Set`, i.e. a chosen proposition rather than proof of that proposition. Original owner blobs are pinned and unchanged; all 219 individual physical proof statuses remain `NOT_AUDITED`. The new bidirectional audit index `Docs/roadmaps/YMClay219ProofRelevantBidirectionalAudit20261104.json` contains **521 invertible candidate-gate hints** (R443 68, R445 188, R320 104, R333 105, CLAY 56), **66 unique producer rows** (original 63 plus SEM.P01–P03), no fabricated lemma witness.

**New Agda source:** `YMClayProofRelevantFieldAnchoringSafeExact` proves the general no-promotion/anchoring transport for a physically fixed selected predicate; `YMClayOriginalCMP109NamedSetNoPromotionExact` demonstrates the actual original five CMP109 names can choose uninhabited types without providing physical proofs; `YMClayParametricVocabularyNoClayPromotionExact` constructs a deliberately trivially satisfiable parametric `ClayYangMillsSolution` record, illustrating why the **15 selected carriers / 34 semantic predicates / 13 data fields** must be externally physically anchored. This is a negative semantic countermodel, absolutely NOT an actual Clay or YM theorem. New source has no local holes/postulates; exact-head Agda/kernel and transitive trust remain PENDING.

**Exact remaining / steelman / bidi:** `Docs/roadmaps/YMClaySteelmanBidirectionalExactRemainingMaxCut20261104.md` gives 39 prioritized mathematical producer statements spanning the original 1024 C3/bond proofs, physical compact SU(N) measurable Haar, exact 1024 Wilson-weighted effective-density same-object weld, reflection-compatible all-scale RG, CMP116 uniform differentiated J-rooted-shell control, same OS reconstructed physical H and gap, all compact-simple group scope, and external Clay physical semantics. Six independent exact finite negative controls passed (positive weight not RP; finite gap not uniform; selected observable decay not full spectral gap; constants not measure equality; C3 Haar not weighted action invariance; one gauge group not all groups). Preferred T78 five-input compiler is conditional sufficiency only, **NOT an iff** or official external proof.

**Next physical work remains open:** one closed R443 C3 vector equality + two closed R445 pair/spectator equations, exact typechecking, true measurable Borel SU(N) Haar and selected integrands, full original Gibbs source/effective density equality, uniform UV/IR RG and CMP116 source estimates, RP/OS/same-H positive gap and nontrivial all-group 4D QFT. None is discharged by this audit.

## 2026-11-04 — R443.F08 and R445.F17–F22 weighted effective-density/native permutation max-cut

**Actual work on #1444 only; #1460 unification untouched.** [New original YM weighted effective-density dossier](../physics/YMClayOriginalNativeWeightedEffectiveDensityMaxCut20261104.md).

- `YMClaySUNWeightedHaarPairFibreDisintegrationExact` F17: source-written **actual original SU(N) group operation** plus original one-link right Haar, Fubini, linearity prove the **weighted** noncommutative pair equality `∫dUdV w(U,V)F(UV)=∫dW [∫dV w(WV^-1,V)]F(W)`, the SAME fine/coarse partition and normalized pairing, plus conditional strict coarse density positivity. Arbitrarily coupled fine weights, no bare Wilson promotion.
- `YMClaySUNWeightedDisjointPairFibreReparamExact` F18–F19/F22: finite induction constructs the original all-pairs `Uj,Vj ↔ Wj,Vj` weighted measure reparam, Fubini groups all coarse variables before **all** fibre variables, and an **explicit all-pairs** derived effective coarse density / weighted pushforward numerator. Full arbitrary spectator dependence is retained, with selected original numerical arities **64 pair-links + 896 spectator links**. Strict positive original one-link integration plus positive weight prove pointwise derived effective density and coarse partition strictly positive; no new coarse positivity axiom.
- `YMClayFiniteNativeAdjacentWordInverseExact` F20: original typed adjacent swap, ordered original `LinkPermutation` word compiler and **two-sided inverse**, source-written on arbitrary original link vectors.
- `YMClayNativeC3AdjacentSortProgramExact` R443.F08: construct the actual original 1024-link C3 target **program** from original bond labels; **one CLOSED canonical-label equality remains kernel-open**, not filled by fake `refl`. The original F06 theorem transports a future certificate to all SU(N) links.
- `YMClayNativeSideFourPairSpectatorSortProgramExact` F21: original F15/F16-selected 128 fine-link labels plus the full 896 original spectator complement; reuse the same original bubble-sort `LinkPermutation 1024` generator, with precisely TWO finite closed Agda goals (length and equality). Their acceptance would enable original 1024-link product Haar reindex into the derived F19 effective density *when physical one-link Haar is established*.

**Executed exact independent tests:** 1800 weighted pair + 1800 spectator-coupled cases + non-bare control; 117 all-pair reparam cases / 1,184,769 original fine rows; 81 all-pair derived density/partition cases; original 46,592 C3 swaps, original 41,792 side-four pair/spectator swaps, original inverse/C3³/digest/negative controls. All PASS in local Python reference. **Not Agda kernel acceptance;** one F17 parenthesis syntax issue was discovered and repaired via static audit. New files have no local postulate or hole; inherited `RealAnalysisAxioms` axioms and selected physical continuous compact Borel Haar remain OPEN.

**Physical maximum cut remains:** accepted original C3/side-four native closed equalities and correct 1024 decoder with real SU(N) Borel Haar → selected actual **weighted Wilson–Gibbs** effective coarse density/disintegration → reflection-compatible all-scale changing-cutoff RG and uniform analytic estimates → same-source differentiated mixed-J CMP116 rooted-shell decay → physically reconstructed same-H OS strict gap/ H6/Clay. Nothing in the present finite F17–F22/ F08 source upgrades Clay or resolves R320/R333. Canonical ledger now R443.F01–F08 and R445.F01–F22, 63 producer rows; original 219 field inventory individually unaudited.

### 2026-11-04 — F15/F16 actual original selected side4→side2 pair and canonical reindex frontier

`YMClayNativeSideFourTwoLinkPairSameObjectExact` proves the **actual original** `Block.nativeBlockedPositiveLinks {m=1} {l=1}` is the literal right-associated 2-link ordered product of original fine-bond values at the original fine-block origin and its positive successor. Only the original `Bond.identityRight` is used to remove the empty-path identity. Specializations select the **identical original SU(N)** `SUNBlock.nativeSUNBlockLinks` and the **actual selected weighted Gibbs** `Push.actualBlockedLinkMap`. This removes a specific pointwise same-object bridge, not the global original 1024-coordinate reindex.

`YMClayNativeSideFourPairDistinctCertificateExact` reuses original `Codec.originalPositiveBondFinite` for 64 selected coarse bonds and 1024 fine bonds plus original `Torus.productDecidableEquality`; a concrete 128 selected fine-label duplicate-decision and `refl` closed count/distinctness goals are SOURCE-WRITTEN but **Agda kernel evaluation pending**. Independent `scripts/check_ym_native_1024_pair_spectator_reindex.py` executed: 1024 native labels → 128 pair-selected +896 spectators, inverse, exact `41,792` adjacent swaps, digest `49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada` and wrong-order/duplicate controls PASS. The **next exact finite gate** is the typed original `Product.LinkPermutation 1024` and canonical label-vector proof; no finite counting reference can replace kernel acceptance. F13 unweighted Haar now covers arbitrary ordered length L and disjoint L blocks, but not continuous Haar existence, weighted effective Gibbs action/conditional disintegration, uniform CMP116 estimates or same OS strict gap. Full 219 Clay fields not audited; F01–F16 are producer rows, not a proof of Clay. Another worker owns TSVF/KK #1460.

## 2026-11-04 — R445.F13/F14 original Haar pair & actual blocked covariance (source-written)

**New same-source finite reduction:** [YM R443/R445/R320 Haar-blocked same-object dossier](../physics/YMClayOriginalHaarPairsToR445R320SameSourceMaxCut20261104.md). `YMClaySUNHaarDisjointPairBlockingExact` derives `∫dU dV F(U·V) = ∫dW F(W)` for noncommutative original SU(N) links using existing `Bilateral.oneLeftInvariant`, original one-link Haar normalization, scale and integral congruence; extends to all disjoint ordered pair-vectors plus any number of independent spectator links, no new Haar axiom. Native selected original 4D geometry reference: 1024 fine positive bonds, 64 coarse bonds, 128 distinct paired bonds, 896 spectators. Independent exact Q8 tests: 64 single-block functions, 14 arbitrary nonfactorized n≤3 disjoint-vector functions, plus all native periodic selected bonds and endpoints passed. **Source-level only; Agda kernel pending.** To apply to the full original side-four source still requires kernel-accepted exact 1024-label pair/spectator permutation, and true measurable compact SU(N) one-link Haar.

`YMClaySUNR445BlockedPushforwardR320CovarianceExact` reuses the **actual** original side-four SUN Wilson-Gibbs normalized measure and `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact.actualBlockedLinkMap` to prove definitional covariance agreement for arbitrary coarse F,G. No new coarse bare Wilson density, auxiliary measure or arbitrary covariance is postulated. Weighted Wilson interactions COUPLE spectators, so the unweighted Haar discard theorem does **not** establish effective-action density or conditional disintegration. Changing-cutoff/volume CMP116 mixed-J log partition differentiation and rooted-shell uniform decay, physical OS reflection positivity, strict R333 continuum gap and H6 nontriviality remain OPEN. No cross-writes to the separately owned TSVF/KK #1460 lane. Retains original Bałaban/Wilson source ownership. Golden claims remain blocked by transitive `RealAnalysisAxioms` and absent Agda compiler receipt.

## 2026-11-04 — R445.F12 exact existing finite pushforward/pullback/reopening weld

**Same theorem owners, no duplicate probability theory.** `DASHI/Physics/YangMills/YMClayFiniteRGExistingPushPullReopeningWeldExact.agda` applies `DASHI.Core.SectionedProjectionProvenanceBridgeExact.pullbackObservable` to the *same* projection of `BalabanFiniteProbabilityPartitionDisintegrationExact.FiniteCoarsePartition`, takes its real constructor `compileFiniteRGReopeningStep`, and uses the existing `BalabanFiniteRGObservableReopeningExact` finite expectation transport.

The source-written new proof terms are `originalKernelPullbackPointwise` (actual matches/project fibre support), `originalReopeningOfPullbackIsCoarse` (`T(f o project) = f`), `originalReopeningFibreConstant` (explicit fine-observable factorization through coarse), `originalFinitePushforwardPullbackPairing` and `originalFiniteFibreConstantExpectation` (`E_fine[f o project] = E_coarse[f]`). These are reductions on one original rational coarse-fibre partition, not a second pushforward or conditional kernel.

**Independent finite reference only:** `scripts/check_ym_existing_pushpull_reopening.py` executed on 2,400 deterministic exact-rational partitions; 22,862 fine states and 12,911 coarse fibres, all support/normalization/disintegration/pullback/expectation tests passed. Agda kernel NOT RUN, no `--safe` transitively accepted claim.

**Fail-closed physical boundary:** the selected original physical SU(N) side-four → side-two Gibbs pushforward remains in `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact`, with its own continuous matrix-link configurations, one-link measurable Haar inputs and original Wilson density. Its identification with an actual measurable conditional distribution, effective coarse Radon–Nikodym density/action and the rational finite `FiniteCoarsePartition` carrier is NOT established. Generic finite identities do not close R445.P04/P06/P07, physical OS reflection compatibility, CMP116 R320 mixed-J decay, R333 positive continuum mass gap, H6 nontriviality or Clay. R443 actual Haar and C3 witness remain. F12 is SOURCE/KERNEL PENDING and canonical producer-level ledger advances to 52 entries, with all 219 original submission fields unaudited.

## 2026-11-04 — R445.F10/F11 original all-coarse SU(N) gauge-lift on selected finite Gibbs pushforward

**Real source continuation, not a Clay promotion.** `YMClaySUNSideFourBlockedFineHaarObservableExact.agda` now source-writes the original side-four → side-two coarse-site projection and the explicit lift `liftOriginalCoarseGauge` of **any** side-two SU(N) site gauge to a side-four gauge. `selectedCoarseSiteAtBlockOrigin` uses original Bałaban M=L=2 split/unblock/site roundtrips; `blockLiftedCoarseGaugeAt` proves its restriction is the original coarse gauge. Using selected `Endpoint.sideFourSUNBlockGaugeCovariant`, it derives `selectedBlockedCoarseGaugeEquivariant` on the **actual ordered non-Abelian** link block. Via selected one-link product-Haar congruence plus the existing original fine Gibbs gauge theorem, `selectedPushforwardAllCoarseGaugeInvariant` proves that the fine pushforward expectation of any pointwise coarse observable is invariant under every coarse gauge; the original coarse Wilson action and Gibbs-density specializations are derived rather than separately assumed.

**Reference:** `scripts/check_ym_blocked_all_coarse_gauge_lift.py` exact Q8 finite test executed locally with exit 0: 3,256 identity checks for 40 deterministic noncommutative trials, and 40/40 deliberately wrong target-inverse controls rejected. This checks finite conventions only; the source-written new Agda theorems were NOT typechecked, and imported `RealAnalysisAxioms` postulates have NOT been cleared.

**All-scale reuse:** `YMClayNativeAllScaleBlockedCoarseGaugeLiftExact.agda` proves every original M×L Bałaban coarse site gauge lifts to the original fine site carrier and restricts exactly on block origins. The actual non-Abelian blocked-link coarse gauge theorem is derived **conditionally** from the unchanged all-scale `BlockEndpointCompatibility` arithmetic hypothesis; it remains OPEN. `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` now exports selected `actualPushforwardAllCoarseGaugeInvariant` for the original weighted/normalized coarse-cylinder functional. Existing independent F08/F09 finite-functional and finite non-bare-Wilson theorem owners are retained; identifiers reconciled to F10/F11 for this contribution.

**Critical effective-action boundary:** the selected blocked expectation remains `E_fine[F(B(U))]`. Its gauge invariance does NOT prove the pushforward has a bare Wilson Gibbs density with respect to coarse Haar, or yield its full effective action, normalized conditional disintegration, preservation of OS reflection positivity under this block, running beta/spacing, uniform UV/IR estimates, R320 mixed-J CMP116 decay, R333 strict same-OS-H gap, or the Clay solution. Existing finite rational disintegration theorem owners `BalabanFiniteProbabilityPartitionDisintegrationExact` and `BalabanFiniteRGObservableReopeningExact` are reused as algebraic precedents, not falsely promoted to continuous physical SU(N) disintegration. The 219 submission fields remain individually unaudited; new current producer ledger rows are R445.F10/F11 (51 total, including independently owned F08/F09). Keep #1440 parent, #1444 physical YM, #1460 downstream TSVF/KK without circular imports. Preserve Wilson, Bałaban, Haar/Fubini and previous DASHI proof-source attribution.

## 2026-11-03 late — YM R445 same-SU(N) blocked Wilson and finite fine-Gibbs pullback (source-written)

After checking the newest open PR heads and changed files, the parent #1444 and downstream #1460 have complementary, **not interchangeable**, R445 finite results. #1460's `YMClayNativeBlockedSU2PathHolonomyGaugeExact` constructs general blocked-offset/composable rational-SU(2) paths and actual real-trace closed-loop invariance; it is downstream. Parent #1444 now has `YMClayNativeBlockedPositiveHolonomyGaugeExact` (generic original group), `YMClaySUNNativeBlockedPositiveHolonomyExact` (original all-SU(N) carrier), `YMClayNativeSideFourTwoBlockEndpointExact` (specific side-four 2x2 endpoint) and two newly added **original physical observable** owners:

1. `YMClaySUNSideFourBlockedWilsonGaugeExact.agda` builds, on the ORIGINAL side-four fine SU(N) Wilson field, the ordered two-link coarse field at side two, the selected coarse-periodic Wilson plaquette, its real trace, the six-positive-plane deficit, beta-weighted Wilson action and Gibbs density. Source-written Agda proofs derive fine-site-gauge invariance through the **same** original coarse `Variable.periodicSUNGaugeTransform` and the previously proved `Pointwise.variablePositivePlaquettePointwise`, `variableSixWilsonDeficitPointwise`, `variableWilsonActionPointwise`, `variableGibbsDensityPointwise`, and native gauge invariance. No whole-field function extensionality.
2. `YMClaySUNSideFourBlockedFineHaarObservableExact.agda` uses exactly `Constructed.actualPeriodicProductMeasure theory ... n=3 betaFine ...`, the original source fine Wilson/Gibbs density, original one-link Haar and bilateral gauge algebra, and the **same** native SU(N) block. It proves pointwise coarse observables pull back to fine pointwise observables and derives the normalized original fine-Gibbs expectation gauge theorem for generic coarse observables, plus selected coarse Wilson action and coarse Gibbs density. This is a **conditional** finite product-Haar theorem, not constructed compact measurable SU(N) Haar.
3. These are direct R445.F06/F07 source reductions, re-exported by `DASHI.Unified.BalabanRGTOERegression` and registered in [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md). The current ledger now has 47 producer-level rows. The source-extracted 219-field A–I submission inventory is unchanged and still per-field `NOT_AUDITED`.

**Fail-closed distinction:** `E_{fine,betaFine}[F(B(U))]` is the **definition of a blocked-observable pushforward functional** under map B. It does NOT assert that the pushforward of the full fine Wilson Gibbs measure equals `Z_{coarse}^{-1} exp(-betaCoarse S_W(U_{coarse})) dH(U_{coarse})`: real non-Abelian RG typically generates effective multi-link interactions/counterterms. Neither finite gauge invariance nor product-Haar symmetry supplies uniform R445 moment/tail/refinement/OS reflection estimates. No imported `RealAnalysisAxioms` postulates are cleared, Agda kernel acceptance is still pending, and the R320 mixed-J physical decay, R333 physical same-H strict gap, 4D Clay existence/nontriviality remain open.

**Next exact payments:** R443.F07 Agda adjacent-swap program and single 1024-label equality; physical SU(N) Haar on the defensible measurable/integrable Wilson test algebra and selected R124 E/R/B/V; R445 all-size modular endpoint, actual nonlinear Wilson Gibbs RG pushforward/disintegration and reflection-compatible cylinders, beta(a)/volume and uniform physical limit estimates; R320 CMP116 source-differentiated exponential rooted-shell bound; R333 same-OS-generator dimensionful gap and full Clay endpoint. Credit Wilson, Bałaban, Haar/Fubini, Osterwalder–Seiler, Menotti–Pelissetto, Osterwalder–Schrader and original DASHI code owners; preserve #1460 independent worker's rational SU2 closed-path provenance.

## 2026-11-03 late — latest YM PR/branch audit + native blocked SU(N) link max-cut

**Latest live GitHub PR heads checked:** #1440 `6e9bcb01fd95ed935ee2e40ff7326df7df575f6c` (Route-S R320/R333, parent); #1444 remains current four-dimensional physical YM owner (this branch); #1460 is an independently moving downstream Lorentz/TSVF/KK OS-clock/compatibility branch, at `afe6882036ad090b284a4bb100c821a19d74a1ac` during the initial audit (subsequent head may move). Other newest repository PRs #1461–#1464 are not claimed as R443/R445/R320/R333 physical-YM theorem owners. The existing `dashi_lean4` PR #15 (`6c106f9980d98e4a1205a3b784373ac914390c93`) provides a real SU(2) Haar **donor**, but not an Agda same-carrier/kernel-accepted Haar proof.

**New genuine R445 finite physical source owner**:
- `DASHI/Physics/YangMills/YMClayNativeBlockedPositiveHolonomyGaugeExact.agda` defines the exact positive-direction `positiveSteps` and `positiveDirections` on the **original** four-torus, constructs the ordered **group-valued** `positiveHolonomy` and `nativeBlockedPositiveLinks` from the existing Bałaban 4D block origin `YMClayNativeBlockedPeriodicBondWeldExact.unblockNativeSite`. Induction proves `positiveHolonomyGaugeCovariant` under `Bond.transformedBondBase`, original `positiveHolonomyIsSelectedPath`, and pointwise-link congruence with **no unrestricted function extensionality**. A single `BlockEndpointCompatibility` arithmetic proposition isolates the all-`M×L` coarse-endpoint equality; when given, `nativeBlockedGaugeLawOnCoarse` derives the actual coarse-source transformation.
- `DASHI/Physics/YangMills/YMClaySUNNativeBlockedPositiveHolonomyExact.agda` instantiates precisely `SUN.CertifiedSUNMatrixTheory`, `Native.sunExactSignedLinkGroup`, `Variable.SUNPeriodicLinks`, `Variable.periodicSUNGaugeTransform` and `Variable.periodicSUNRealization`; the non-Abelian block field is **not** a separate toy gauge algebra.
- `DASHI/Physics/YangMills/YMClayNativeSideFourTwoBlockEndpointExact.agda` source-writes eight actual selected side-four, block-two/coarse-two finite endpoint clauses and obtains `sideFourSUNBlockGaugeCovariant` for original 1,024 fine positive links → 64 coarse positive links. Its eight `refl` terms are **Agda-kernel unverified**. All-M,L exact endpoint, blocked Wilson plaquettes/action, Gibbs pushforward and measure cylinder, reflection-compatible half-spaces, physical spacings, CMP116 mixed-J and R333 OS gap are still open.
- `scripts/check_ym_native_blocked_positive_holonomy.py` executed an independent noncommutative Q8 reference over `(M,L)=(1,3),(2,2),(2,3),(3,2),(4,2)`; original fine path/gauge cancellation, periodic coarse endpoint and deliberately bad omitted target inverse were checked. Side-four M=L=2 checks 64 coarse edges corresponding to 1,024 original fine edges. This is **reference-only** and is not a proof of a continuum SU(N) measure or Agda code.

**Current exact-lemma ledger**: [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md) adds R445.F04/F05 and updates P01/P02 to source-written finite closure with separate all-scale physical/measure leaves. This does not decrement frozen physical research families A–D or discharge the 219 full submission fields automatically. The latter inventory remains [YMClaySubmission219FieldInventory20261103.json](YMClaySubmission219FieldInventory20261103.json) with all 219 individual statuses **NOT_AUDITED**.

**Still exact P0/P1 max-cut:** R443.F07 Agda adjacent-swap program + original 1,024-label equality; physical continuous SU(N) Haar/integrable Wilson class/real matrix identification and selected CMP119 E/R/B/V; R445 all-scale block-endpoint, same-Wilson action/refinement and actual Gibbs measure disintegration/OS; uniform UV/IR estimates; R320 physical selected mixed-J differentiated rooted-shell decay; R333 the SAME OS Hamiltonian in physical units with strictly positive surviving spectral gap, complete nontriviality and the full Clay Jaffe–Witten endpoint. Do not equate a TSVF branch's physical clock with OS time translation by proclamation.

**Verification:** connected GitHub file writes/readback, source/import and concrete cross-PR read checks, and local Python Q8 execution only. Agda binary unavailable here. No exact-head kernel acceptance, transitive zero-postulate clearance, physical Haar, physical Wilson RG limit or Clay mass-gap proof. Attribute Wilson, Bałaban, Haar, Osterwalder–Seiler/Menotti–Pelissetto, Osterwalder–Schrader and original DASHI theorem owners.

**Late 3 November current R445 source:** The full exact group-valued 4D blocked-link holonomy, SU(N) adapter and selected side-four block-two/coarse-two endpoint/gauge law are now source-written. The **all-size** endpoint, real Wilson Gibbs measure disintegration, RP and cutoff-uniform physical estimates are not thereby proved. See the canonical exact ledger and receipt below.

**R443.F07 executable reference update:** `scripts/check_ym_native_c3_adjacent_swap_word.py` deterministically synthesizes the selected spatial C3 adjacent-swap word; for the side-four original 1024-link list, an independent reference execution produced 46,592 adjacent swaps and verified the resulting permutation. This is a finite reference receipt, not the Agda `LinkPermutation`/`onCanonicalLabels` proof; F07 remains OPEN.

## 2026-11-03 — AUTHORITATIVE current YM exact-lemma reconciliation

**Per-field canonical inventory:** [YMClaySubmission219FieldInventory20261103.json](YMClaySubmission219FieldInventory20261103.json) now literally lists the 219 A–I source record-field names, IDs and source blob SHAs, and `scripts/check_ym_219_field_inventory.py` detects source drift. This is a verified 219-field enumeration, NOT individual theorem discharge or Clay closure. The current 43-entry producer-level R443/R445/R320/R333/Clay/TRUST lemma matrix remains in [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md).



**Read this before historical append-only sections:** [YMClayCurrentExactLemmaLedger20261103.md](YMClayCurrentExactLemmaLedger20261103.md) is the canonical current *source-status* ledger for R443/R445/R320/R333/Clay. Its IDs are stable for the current max-cut: R443.F01–F07/P01–P05; R445.F01–F03/P01–P09; R320.P01–P06; R333.P01–P07; CLAY.P01–P03; TRUST.K01–K03. The older 219-field submission inventory and frozen four-family research scoreboard remain separate uncompleted formulations of the same Clay endpoint, not five additional official Clay problems.

**New actual code**: `YMClayNativeC3SingleVectorPermutationCertificateExact.singleVectorC3ImpliesAllVectors` derives the formerly universal 1024-coordinate `ExactC3AdjacentSwapWitness.matchesNativeVector` from ONE exact equality on the canonical original bond-label Vec. `YMClaySUNConstructedNativeC3SetoidHaarExact.adjacentSwapFromOneVector` and `originalNativeC3GibbsHaarInvariantFromOneVector` attach this to the **existing original native SU(N) Wilson/Gibbs Haar consumer**. R443.F07 — finding the actual `LinkPermutation 1024` program and proving the one label-vector equality — is still OPEN. Constructing genuine compact Haar remains a separately OPEN physical R443.P01–P03 input, not solved by C3 combinatorics.

**Verification**: GitHub readback only. `agda --safe` and whole-TOE kernel check NOT RUN; imported `RealAnalysisAxioms` contains postulates, including in historical locally `--safe` modules. All new Agda terms remain SOURCE (not kernel accepted). Do not infer the selected CMP116 physical mixed-J decay, same-H OS physical gap, R445 continuum, or Clay completion from the finite index equalities. #1440 is Route-S parent, #1444 is the YM implementation, #1460 TSVF/KK is downstream and **not** an OS/mass-gap premise.

## 2026-11-03 — YM R443 native C3 and R445 physical blocked-lattice max-cut (PR #1444)

**Docs → TODO → code → changelog synchronization.** Parent #1440 is the Route-S R320/R333 consumer; #1444 is the physical four-dimensional Yang–Mills construction; #1460 is a downstream TSFV/history/KK consistency and same-clock comparison only. The 2014/2017 TSVF macroscopic-robustness proposal, branch-reversal and operational time arrows **do not** provide the Osterwalder–Schrader (OS) temporal reflection, a positive Yang–Mills transfer matrix, a physical four-dimensional continuum, or an OS Hamiltonian gap by themselves.

**R443 finite C3 paid in source (Agda acceptance pending):**
- `DASHI/Physics/YangMills/YMClayFiniteNativeBondReindexingSafeExact.agda`: generic **original positive bond** Vec reindexing and pointwise lemma, with identity, composition, two inverse lemmas and triple-order law. Imports only the existing safe finite original torus/codec; no real-number/Haar/RG assumptions.
- `YMClayNativeSideFourC3VectorWeldExact.agda`: instantiates the **literal existing** `CMP119FlatSide4SpatialC3FieldCovarianceExact` axes/site `(x0,x1,x2,x3)→(x0,x3,x1,x2)` and `YMClayNativeRationalSU2Side4C3CarrierWeldExact.nativeForwardC3Bonds` on the actual original **1024 positive-bond** Vec. Constructs the forward/backward coordinate maps, their exact two-sided inverses, `bondOrderThree`, `nativeForwardIsVectorAt`, `nativeForwardEncodesExactly`, `forwardVectorOrderThree` with no global function extensionality.
- `YMClaySUNConstructedNativeC3SetoidHaarExact.agda`: supplies the old `SUNNativeSetoidBondCodec` encoding/decoding and `c3DecodeAt` from these **already constructed** finite sources. The remaining EXACT finite R443-C3 input is ONE `ExactC3AdjacentSwapWitness`: `Product.LinkPermutation 1024` and `∀v, permuteLinks program v ≡ NativeC3.forwardVector v`. This is a *finite syntactic-adjacent-swap proof*, not an additional physical C3 field or Haar invariance axiom. When supplied, the existing `nativeSUNPhysicalGibbsSetoidHaarC3` immediately transports actual real SU(N) Gibbs/C3 integrals conditionally on its one-link Haar/Fubini source.
- `scripts/check_ym_original_c3_bond_vector_reference.py` independent integer reference passes sides 1–5. At side four it finds **16 fixed positive bonds and 336 three-cycles**; all 1,024 labels are covered. Wrong-axis control intentionally disagrees. This is a reference experiment, **not** Agda/kernel acceptance or construction of the adjacent-swap proof.

**R445 genuine original blocked-lattice carrier paid in source (Agda acceptance pending):**
- `YMClayNativeCyclicFinIsoSafeExact.agda` proves the original `Torus.CyclicIndex N` ↔ stdlib `Fin N` two-way iso, without real analysis.
- `YMClayNativeBlockedPeriodicBondWeldExact.agda` composes that with the **existing** `P06FaceCubeTorusGeometry.Cube4` and `BalabanBlockedPeriodicLattice.finePoint/splitFinePoint`, obtaining exact two-sided `blockNativeSite/unblockNativeSite` and `blockNativeBond/unblockNativeBond` for the original `Torus.PositiveBond (M*L)` and the actual four-dimensional block coordinates. It never substitutes a new lattice/gauge field. Important: this is **bond-label/site geometry only**, not a link-valued path block, a gauge-equivariant Wilson coarse action, a disintegration of the physical SU(N) Gibbs measure, reflection compatibility, beta(a) calibration, or continuum stability. `scripts/check_ym_original_blocked_bond_reference.py` independent integer tests for (M,L)=(1,1),(2,2),(3,2),(2,3),(4,2) pass both roundtrips. At M=L=2, 256 fine sites and 1024 original positive links are recovered.
- New owners imported/re-exported from `DASHI/Unified/BalabanRGTOERegression.agda`. Golden `{-# OPTIONS --safe #-}` is used only on the isolated finite codec/reindex/Fin equivalence; physical adapters which depend on `RealAnalysisAxioms` are explicitly **not promoted** to an assumption-free result.

**Exact remaining active max-cut**: (P0) compile the actual 1024-coordinate C3 action into `LinkPermutation` and prove `matchesNativeVector`; instantiate *continuous compact SU(N)* normalized Haar on the selected measurable integrable test algebra (avoid the existing total-all-functions `OneLinkProductHaar` paradox), with SU(2)/matrix/Bishop real and `Integrable` compatibility, positive/linear Fubini and rigorous full-support partition positivity; (P0/P1) construct original **group-valued block edge path product** from the now proved native blocked labels and establish gauge naturality, selected Wilson/reflection-positive cylinder compatibility and genuine pushforward/disintegration for each changing fine/coarse lattice; (P1) beta(a), volume/spacing and actual physical R445 tails, moments, tightness, continuum and infinite-volume OS closure; (P1) selected CMP119 R124 E/R/B/V source and CMP116 mixed-J rooted-shell decay on the SAME measures; (P1) actual R333 same reconstructed OS Hamiltonian uniform positive spectral gap and nontriviality. The older Bałaban Gate4 UV iteration/closure record remains *conditional on one-step physical analytic inputs*. Independent lower-dimensional or KK/TSFV finite results cannot be promoted to Clay's four-dimensional pure quantum YM proof.

**Trust / verification boundary:** This is GitHub source-written and readback-checked, with independent deterministic integer references executed. Agda is unavailable locally: no exact-head Agda typecheck, full transitive `--safe` audit, or zero-postulate proof certificate was executed. `DASHI/Foundations/RealAnalysisAxioms.agda` explicitly postulates its `ℝ` and analytical facts; the native physical source chain inherits that authority, regardless of local `--safe` annotations. Original authorship: Wilson (lattice gauge action), Tadeusz Bałaban (periodic geometry/RG), Haar/Fubini, Osterwalder–Seiler/Menotti–Pelissetto (lattice reflection positivity), Osterwalder–Schrader (reconstruction), and original DASHI theorem owners.


## 2026-11-03 — YM max-cut continuation: safe finite gauge split and true moving-cutoff family

**New, reused source owners in PR #1444** (do not pull downstream PR #1460 back into parent):
- `DASHI/Physics/YangMills/YMClayNativeFiniteGaugeVectorNaturalitySafeExact.agda`. Pure finite `{-# OPTIONS --safe #-}` source, relying on the original finite torus, duplicate-free bond enumeration and generic `CompactLieGroupCore.Group`. Proves `vectorGaugeEncoded`, `vectorGaugeDecodedAt`, `originalGaugeDecodedAt`, and `encodeGaugeNatural`. Parameters are the actual finite periodic side, group laws and the original positive-bond target; no real-number/Haar/OS/RG assumptions. Existing postulate-free `BalabanFiniteEnumerationDistinctExact` and `CompactLieGroupCore` were promoted to `--safe` for this isolated chain. Source-written; compiler **not available/acceptance pending**.
- `YMClaySUNConstructedPeriodicGaugeCodecExact.agda` now imports the finite source. Its `safeVectorMatchesBilateral` identifies finite group-coordinate action with the original bilateral SU(N) one-link action; `safeNativeGaugeDecodeAt` supplies the original `OriginalPeriodicGaugeVectorNaturality.gaugeDecodeAt` field. The theorem remains a conditional physical adapter (true compact Haar not yet supplied).
- `YMClaySUNVariablePhysicalCutoffFamilyExact.agda` now constructs the actual dependent sequence `linksAt n`/ `physicalFiniteCutoffMeasure n` from the original periodic SU(N) Wilson action and **single shared one-link Haar authority**, with variable beta(n). It records exact `4(n+1)^4` link count, original same-source Gibbs density/partition, conditional partition positivity, native Wilson-action gauge invariance and normalised Wilson-deficit expectation invariance for every finite n. It does **not** force arbitrary sides into a common configuration carrier and cannot be conflated with `YMClaySUNMatrixSameFamilyR443R445Exact` (which changes beta on the fixed side-four space). The moving-family module is deliberately not declared golden because its real-analysis and Haar sources are postulated/conditional.

**Trust boundary found:** `DASHI/Foundations/RealAnalysisAxioms.agda` explicitly introduces postulated `ℝ`, arithmetic/order and other external-analysis facts. Any imported dependent physical source that passes through it cannot be described as **transitively zero-postulate Golden Agda** without an actual replacement/proof of the underlying constructive real analysis. Some existing modules have a local `{-# OPTIONS --safe #-}` pragma even though they import that source. This is an **unresolved Agda safe-import boundary**, not a kernel acceptance receipt. New `scripts/check_ym_golden_agda_trust_cut.py` traverses local DASHI imports and reports `--safe` mismatches and inherited postulates. It is a read-only **source scan**, never substitutes for `agda --safe` or the transitive kernel trust audit.

**Classical versus Euclidean quantum source:** The sourced classical equation `D_mu F^{mu nu}=J^nu` is an Euler–Lagrange/current statement. The selected 4D Euclidean Wilson path measure is `dμ ∝ exp(-S_E) ∏_b dH_{SU(N)}(U_b)`. One cannot infer the physical measure, reflection positivity or a positive mass gap from the classical equation. Clay's **pure gauge** sector does not inherit matter-source quark currents merely because an unrelated classical statement allows `J ≠ 0`. See the existing `DASHI.Physics.Closure.YangMillsFieldEquationReceipt`, `YMStrictSelectedStationarityToSourceEquation`, `BalabanP33LiteralCovariantDivergenceDifferenceExact` and Wilson/OS owners; no duplicate field equation is introduced here.

**Exact remaining P0/P1 physical cut:** instantiate actual continuous compact SU(2)/SU(N) Haar on a selected measurable/integrable test algebra (the present `OneLinkProductHaar` is total on all functions, while `CompactLieAnalyticPackage.NormalizedHaarTheory` uses an explicit `Integrable` predicate); match the selected real/matrix/carrier; construct C3 permutation witness on the actual bond Vec; align `beta(a)`, spacing, volume, CMP119 R124 E/R/B/V physical sources, original changing-lattice cylinder/refinement, uniformly bounded moments/tails and continuum. Then the original CMP116 mixed-J rooted-shell estimate, same OS Hamiltonian R333 spectral lower bound, nontriviality and Clay scope remain independently required. Older Bałaban Gate4 UV iteration still requires its one-step analytic and physical continuum/OS inputs. No 5D/KK reduction, classical sourced equation or finite reference checker proves these.

**Verification:** GitHub commits/readback for the new sources and imports; local original-bond Python rational fixture from the prior YM round. The **new** Agda modules have not been kernel-checked in this session (Agda executable unavailable), and the recursive trust scanner is not itself a proof. Attribution to Wilson, Haar/Fubini, Balaban, Osterwalder–Schrader, original DASHI owners; independent KK/TSFV worker is downstream only.

### 2026-11-03 — generic all-L positive-link counting payment

`YMClayNativePositiveBondEnumerationVectorExact` also proves `listLengthMap`, `listLengthAppend`, `listLengthCartesian`, `listLengthAllCyclic`, `originalSiteCountFormula`, and `originalPositiveBondCountFormula`. Thus the **actual canonical** original periodic configuration has exactly `((L*L)*(L*L))*4` positive bonds for every finite side `L`; the 1,024-link side-four equation is now derived from the generic count. These theorems are finite enumeration/coordinate laws, not cutoff-independent physical moment bounds. Source-written, kernel check pending.

### 2026-11-03 native finite bond codec independent exact-rational fixture

Committed `scripts/check_ym_native_periodic_bond_vec_codec.py`. The local execution of this same script (standard Python `fractions.Fraction`, no external dependencies) passed: side 2 (16 sites / 64 bonds), side 3 (81 sites / 324 bonds) and side 4 (256 sites / **1,024 bonds**); for every bond, field→vector→field, vector→field→vector, and original `(gamma_x U) gamma_y^{-1}` versus vector `gamma_x (U gamma_y^{-1})` agree exactly. Wrong target inverse disagreed on 52, 256, 820 bonds respectively, and a duplicate-label enumeration fails the vector roundtrip as expected. These diagnostics cross-check enumeration order and group-product association, **not** Agda kernel acceptance, compact Haar, all-observable integrability, R445 physical limits, CMP116 or OS.

This narrows the literal R443/R445 finite **codec + gauge naturality** from assumed record inputs to source-written canonical enumerations. Still NOT paid: the selected C3 product permutation syntax/witness, continuous compact one-link Haar and scalar-carrier weld, selected CMP119 R124 metric insertion, continuum/UV estimates and same-H gap.


### 2026-11-03 — P0 original bond codec + native gauge naturality (YM PR #1444)

**New Golden Agda source-written theorem owners:** `YMClayNativePositiveBondEnumerationVectorExact` and `YMClaySUNConstructedPeriodicGaugeCodecExact`. The first reuses the original `BalabanPeriodicTorus4Carrier.periodicTorus4Finite`, `productFinite`, and `BalabanFiniteEnumerationDistinctExact.cartesianDuplicateFree`. It constructs the ORIGINAL positive-bond list for **each actual periodic side L**, computes its length, proves duplicate-freeness and defines exact field-to-Vec/Vec-to-field codecs. `originalBondsDecodeEncodeAt` proves pointwise function roundtrip; `originalBondsEncodeDecodeExactly` proves the vector roundtrip from duplicate-free membership, without unrestricted function extensionality. `originalSideFourCountIs1024` pins the literal side-four 4×4⁴ count.

The second owner supplies the previously **uninhabited** `YMClaySUNVariablePeriodicGaugeHaarExact.OriginalPeriodicGaugeVectorNaturality` on the actual periodic SU(N) field at every n. It constructs coordinatewise `gamma(source)` and `inverse(gamma(target))` via the original bond enumeration; `actualGaugeVectorEncoded` / `actualGaugeVectorDecodedAt` match the existing finite vector gauge action with the original bond-function transform. The critical associativity step maps `(gamma(x) * U) * inverse(gamma(y))` to `gamma(x) * (U * inverse(gamma(y)))`. As a result, `actualPeriodicGaugeHaar`, `actualPeriodicGaugeNormalized` and `actualSixDeficitGaugeNormalized` reuse the selected **same finite measure** and existing bilateral one-link Haar theorem without independent decoder, global Haar invariance or gauge-vector naturality fields.

**Remaining R443 analytical inputs:** the existing abstract `CertifiedSUNMatrixTheory` needs an actual chosen compact real/complex group with normalized real trace and compatible real scalar; `OneLinkProductHaar` / `OneLinkSUNBilateralHaar` / ordered and strictly-positive integration still require an applicable *continuous compact Haar* source and measurable/integrable test algebra. The all-bond C3 permutation/selected-observable naturality is distinct from the gauge naturality constructed here. A finite Vec roundtrip is **not** physical compact Haar. **Remaining R445**: cutoff-refinement/cylinder compatibility, selected CMP119 E/R/B/V beta and metric insertions, uniform moments/tails and continuum convergence. **Remaining R320/R333**: actual physical mixed-J CMP116 rooted-shell decay, same H2/OS reconstructed continuum Hamiltonian and strictly positive uniform gap/nontriviality; the full Clay scope remains open.

**PR stack and dimensional safeguard:** `#1440` (Route-S) is the base of `#1444` (this finite YM source); `#1460` (Lorentz/TSFV/KK) is stacked on `#1444` but owns separate conditional signature and KK reductions. The downstream `YMClayFiveSectorBidiSteelmanExact` proves finite ten-plane Nat accounting and exhibits an uncancelled fifth-axis curvature example. That is a useful **negative-control requirement for any 5D→4D physical action comparison**, not an extra premise of pure 4D YM and not a proof that the KK fields decouple. Do not import downstream PR #1460 into the parent proof graph. Older Bałaban UV work (#568, `BalabanClayGate4CombinedRGUVIterationExact`, `BalabanClayConcreteUVToMassGapDependencyExact`) retains analytic one-step and OS/continuum physical inputs; no finite codec closes those.

**Verification/accounting:** Connector source readback and syntactic no-hole/no-local-postulate inspection were performed. Agda `--safe` typecheck, complete trust/axiom audit, Lean same-object acceptance and CI were **not executed**. This is a source-written *finite* closure, not a physically accepted continuum or Clay proof. Attribution: Wilson, Bałaban, Haar/Fubini, Osterwalder–Schrader, canonical DASHI enum and matrix proof owners, and the other worker's independent five-sector audit.


### 2026-11-03 — R443/R445 every-n native gauge and Haar numerator theorem

Added `YMClaySUNVariablePeriodicGaugeHaarExact.agda` atop the new variable-size product-Haar source. It reuses `YMClaySUNVariablePeriodicGibbsGaugeExact.periodicSUNGibbsDensityGaugeInvariant`, `YMClaySUNProductHaarGaugeFromOneLinkExact.productHaarNativeGaugeInvariant` and `YMClaySUNVariablePeriodicBondPointwiseExact.variableGibbsDensityPointwise`. The owner proves `periodicProductGaugeHaarInvariant`, `periodicGaugeNumeratorInvariant`, and `periodicGaugeNormalizedExpectationInvariant` for every actual periodic cutoff and every explicitly pointwise-congruent cylinder observable. It derives *whole finite product integral* local gauge invariance from one-link left/right invariance without a second independent full-lattice Haar axiom.

`OriginalPeriodicGaugeVectorNaturality.gaugeDecodeAt` remains a typed physical input **at each original positive bond**. The native vector decoder, gauge factors, measurable one-link continuous Haar and same carrier scalar transport are not yet inhabited. This result does **not** establish exact varying-cutoff cylinder refinement, CMP119 E/R/B/V selected metric insertions, uniform R445 moments, physical CMP116 R320 bounds, or R333 continuum OS spectral positivity. Preserve the Golden Agda source-written / kernel-pending boundary.


### 2026-11-03 — original variable-periodic Wilson–Gibbs product-Haar finite cut

New source-written golden owner: `DASHI/Physics/YangMills/YMClaySUNVariablePeriodicProductHaarExact.agda` (on YM PR #1444). Unlike the earlier fixed side-four family, this module is parameterized by **every actual periodic lattice size** `n` and reuses the original `YMClaySUNVariablePeriodicGibbsGaugeExact` six-positive-plane action and Gibbs density. It constructs the finite physical measure from `YMClayFiniteProductHaarPermutationExact.productIntegral` of **one** link source, without an arbitrary independent full-field integral at each n.

Source-written statements: `periodicProductHaarUnit`, `periodicActualDensityStrictPositive`, `periodicProductPartitionStrictPositive`, `periodicProductIntegrationLaws`, `periodicProductDensitySameObject` and `periodicProductPartitionSameObject`. One-link normalization/Fubini/linearity/positivity propagate to every finite product; Gibbs partition positivity follows from selected one-link *strictly positive integration* rather than assuming a nonzero partition. The corresponding exact owner is imported and re-exported by `DASHI.Unified.BalabanRGTOERegression`.

**Not paid:** `OneLinkProductHaar` is a total test-functional interface, not by itself genuine continuous SU(N) Borel Haar. The per-n native vector decoder, true native bond count/order (side four: 1024 links), full-support measurable test class, concrete SU(N)/Bishop-real/legacy real weld, selected CMP119 R124 E/R/B/V metric insertion and counterterms, cutoff-refinement/cylinder consistency, physical R445 uniform moments/tightness/limits, selected R320 CMP116 differentiated mixed-J decay and R333 same-H OS spectral separation/H6 remain open. The constructor has **no source-written cross-cutoff consistency assumption disguised as proof**. GitHub write/readback is not Agda kernel acceptance, and imported foundational postulates remain outside zero-axiom trust.

Recommended next max-cut: (P0) inhabit actual selected compact one-link Haar + side-four and variable-size original bond decoder, then propagate same Gibbs measure into the exact CMP119 selection; (P1 independent) physical R445 uniform marked moment and source compact-containment; (P2) selected CMP116 source-envelope estimate; (P3) OS physical mass gap/nontriviality.
### 2026-11-02: reconcile all prior plaquettes + variable-size SU(N) source

The source search found an older **canonical** `SUNWilsonAction` / `SUNWilsonClassFunction` owner. The new `YMClayNativeSixPlaquetteSUNWilsonActionWeldExact` builds a typed original signed-word `Path` and **proves** exact native original-positive-six-plane action equality with that canonical owner at each side-four site, globally, and after beta weighting. The trace-cyclicity-derived `SUNMatrixRealTrace` is now projected into the old canonical `SUNWilsonTraceAuthority`. `YMClaySUNVariablePeriodicGibbsGaugeExact` lifts original finite periodic SU(N) Wilson/Gibbs action and full local gauge invariance from fixed n=3 to **every original periodic lattice n**, using the real existing site enumeration rather than an abstract cutoff index. Source-written, Agda kernel not run; **no physical compact Haar, uniform R445 estimates, selected CMP116 R320 decay or same-H R333 gap is inferred**. Full search/ownership/attribution and exact remaining leaves: [source audit](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md).

### 2026-11-02: full native SU(N) finite gauge invariance (source-written)

`YMClaySUNMatrixSixPlaneGaugeInvariantExact` now reuses the selected native group gauge transformation, transformed-link/word equality, source positive-plaquette gauge cancellation, certified SUN matrix trace class function, original six-plane real site sums and literal beta-weighted Gibbs exponential. It proves the full original six-plane action **and same Gibbs density** are locally gauge invariant, not merely an individual plaquette. This removes any independent finite Gibbs gauge-invariance leaf, conditional on actual SUN matrix/trace theory inputs. Independent SU2 quaternion numerical fixture passed all 1536 original six-positive plaquettes (256 sites/1024 links) with max real-trace error 7.77e-16, action before=after 1538.045855541643. Source-written theorem remains uncompiled; fixture is NOT kernel certification. R443 normalized continuous Haar/Fubini + literal native bond-vector codec, R445 changing-cutoff physical tails, R320 CMP116 selected decay and R333 same-H OS uniform gap remain open.

### 2 November 2026 — physical SU(N) matrix-link and product-Haar max-cut

Canonical exact-lemma/source-owner crosswalk: [YMClaySUNMatrixR443R445R320R333MaxCut20261102](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md). This tranche **reuses** the existing `SUNMatrixCarrier`, `CompactLieGroupDerived`, original signed periodic Wilson owners, canonical CMP119 expectation and R278 covariance, R320 CMP116 physical source and R333/round557 OS consumer. It does not add a parallel rational/quaternion Haar source or assert a Clay solution.

**Source-written Agda (kernel/CI deferred):** `YMClaySUNMatrixNativeSignedWilsonExact`, `YMClaySUNMatrixWilsonTraceGaugeExact`, `YMClaySUNMatrixSixPlaneGibbsDensityExact`, `YMClaySUNMatrixSameFamilyR443R445Exact`, `YMClayFiniteProductHaarPermutationExact`, `YMClaySUNMatrixProductHaarC3Exact`, `YMClaySUNMatrixR445R320SameCovarianceExact`. These derive original signed SU(N) matrix Wilson holonomy/C3, gauge trace invariance from matrix trace cyclicity, literal six-positive-plane real Gibbs density, no-free-equality finite expectation, finite product-integral permutation invariance from two-link Fubini, C3 integral invariance under an explicit bond-to-vector permutation codec, and same-source R278 covariance from the finite real matrix Gibbs family.

**OPEN, exactly:** (R443) actual instantiated continuous SU2/SUN matrices, physical ReTr/N, one-link normalized compact Haar/Fubini and the 1024-positive-bond enumeration/C3 codec, selected beta/counterterms and Gibbs normalization; (R445) true *varying-lattice* UV and volume continuum, uniform moments/marked tails and physical cylinder consistency; (R320) selected CMP116 mixed-source derivative rooted-shell physical estimate with uniform domain and constants; (R333) the *same* OS reconstructed physical Hamiltonian with uniform strictly positive continuum/infinite-volume spectral gap, OS/Wightman nontriviality and Clay compact-simple-group scope. The previous n=3 rational fixed-volume 0..3072 bound is not a continuum-uniform estimate. **No physical source is promoted from a conditional record.**

### 2 November R445 native fixed-volume majorant

New source-written (kernel not yet run): `YMClayR445NativeSixDeficitUniformFiniteBoundExact` reuses the native normalized SU(2) trace inequalities, original six positive plaquettes and side-four rational sums. It proves the **literal rational action bounds** `nativeSixDeficitNonnegative` and `nativeSixDeficitAtMost3072` for every `RationalSU2BondData 3`. The constant is exact: six planes × 256 sites × maximum Wilson deficit 2 = 3072. This pays the finite R445 original-six Wilson majorant mentioned in the 1 November backlog. It is **not** a uniform bound across increasing lattice volumes/cutoffs, and says nothing by itself about compact Haar integrability, stochastic tightness or a continuum OS mass gap.

### 2 November 2026: R443 auxiliary-gauge marginalisation / source cut

**Source-written, exact-head Agda compilation pending.** `YMClayR443BondMarginalC3Exact` now factors the original native six-plane Wilson deficit through the actual n=3 bond field, proves its C3 square without the auxiliary `siteGauge`, constructs a pushforward finite measure on bond-only observables, derives that measure's integration/partition laws from the already-selected Gibbs source identity and source integration laws, proves normalized expectation equality, and reuses the existing R443→R431 numerator C3 compiler on that bond-only carrier.

This **pays the auxiliary-coordinate algebraic marginalisation** subcut; it does not pay compact SU(2) Haar. Rational norm-one quaternions form a proper countable subgroup of full compact SU(2). A normalized compact-group Haar law cannot be obtained just by naming an arbitrary integral on rational points, or by pushing it along the bond projection. The next R443-Haar source is a *different* compact-real link carrier, with a proven rational-to-real holonomy/action comparison and an actual compact product-Haar/change-of-variables construction. Do not report `NativeSixPlaneHaarBoundary` as a constructed physical Haar law.

The remaining high-alpha chain is: **real compact SU(2)/SU(N) source + Haar Gibbs ↔ same-action Wilson comparison → varying-cutoff R445 convergence/observable tails → selected R320 decay → same OS Hamiltonian R333 uniform positive gap → nontrivial full four-dimensional Clay scope.** n=3 is a fixed side-four lattice, not a UV scaling trajectory. K0 compilation remains deferred to the user.

### 1 November selected gauge/Wilson coarse-fine theorem contract

`YMClayVoyagerCovariantWilsonCoarseFineBidiExact` now proves a conditional
same-fine-carrier Wilson gauge-invariance result by *both* selected physical
commuting squares: `block∘gaugeFine=gaugeCoarse∘block` and
`Wfine=Wcoarse∘block`, plus gauge invariance of coarse Wilson. The second
equality is a strong test target, NOT automatically true for generic RG
blocking; correct coarse effective observables may need retained fibre or
quantitative defects. Do NOT turn this into an unconditional physical
theorem. The canonical OS-form pullback uses the distinct existing
`BalabanWilsonTransferBlockingExact` owner.


## 2026-11-01 further Yang-Mills symmetry/source recut

Full cross-repo source map: `Docs/physics/YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md`.

Highest-priority pre-existing *theorem-bearing* direct physical C3 owners were omitted in the first video pass:
`BalabanC3MonsterEquivarianceAuditExact`,
`CMP119FlatSide4SpatialC3FieldCovarianceExact`,
`CMP119ClassicalCurvatureSpatialC3CovarianceExact`,
`BalabanWilsonD4SubsetCharacterExact`, and
`BalabanWilsonTransferBlockingExact`.
The literal four-axis site/bond/curvature C3 action is already source-written;
the full nonlinear generated-action R144/OS/R445 same-object lift and
intermediate equivariance are NOT inhabited. The target is selected SU2/compact
simple physical Wilson source, not a generic 369 observer.

Original jCOARSE/jFINE and `CoarseFineFabricCalculusExact` are genuine prior
projection nonfactorability theorems. `CompactLieLatticeGauge` is a **different**
genuine group-valued Wilson holonomy owner; `Base369Ternary27StratifiedFibreHolonomyExact`
is an explicitly-labelled finite holonomy *analogue*. The particularly
strong Agda #1249/Lean #84 donor supplies path graph 27/729/19683 gauge
covariance/negative flux controls. Import only after same-source field,
plaquette, gauge-group, blocking and Wilson-observable identities are proved.

Complex `i` = 90° real-linear J on an oriented 2-plane, NOT a third spatial
coordinate; source `ConcreteComplex` / `OrdinaryComplexPolar`, new finite
`YMClayVoyagerImaginaryC3DimensionBidiExact` quarter-turn/C3 discriminator,
`PolynomialMonodromyTernaryQuaternionBridgeExact` from branch Agda #1414
(quaternion Spin(3)). Wick, SO2, SO3 and SU2 must remain distinct maps.

`dashifine` 26/31 signature experiments and canonical Agda
`OrbitSignatureDiscriminant` / `CausalOrderLorentzClosure`: conditional
3+1 normal form but the selected tag 31 is included in the profile input;
independent tag-free derivation from physical data remains unpaid. The
`YMClayVoyagerDimensionSignatureForkExact` finite 2/3/4/5 YM coupling weight
and Creutz-5D/KK-5D/stochastic-time distinction do NOT prove dimensional
compactification, Lorentz selection or physical theory.

Probability `Markov` **inequality** in
`BalabanClayT5Path4MarkovProkhorovExact` differs from stochastic
Markov `transition`/invariant-law `YMClayVoyager2026CoverageExact`,
`DashiMarkov` transition sufficiency and
`FiniteStochasticBisimulationExact` coarse-kernel negative control.

Proposed YM spectral ζ must be constructed from same reconstructed
`H_OS`, with zero-mode removal/heat trace/Mellin domain and
infinite-volume trace regularization justified. Existing number-theory
Riemann ζ, modular j, Casimir ζ(-3) are *separate functions/objects*.
No zeta phrase in Voyager video.

**Do not demote the live P0:** same selected R445 measure/tail/moment and
R320/H1, actual R333/H_OS physical spectral attachment, OS/UV/IR
continuum, nontriviality and compact-simple-group scope.


## 1 November 2026: Voyager video completeness / source-calibration crosswalk

The chapter-by-chapter source-to-owner audit is
`Docs/physics/YMClayVoyager20260929CoverageAudit.md`. Golden Agda:
`YMClayVoyager2026CoverageExact.agda` (coverage/status, native P2
reuse, Route-S no-promotion, finite-versus-uniform gap theorem, stochastic
local/global/invariant-measure type separation), plus
`YMClayVoyagerR4HodgeBasisExact.agda` (six signed Euclidean four-dimensional
2-form basis directions and proof that `*^2 = +1` on those signed bases).
These are source-written proof candidates; **exact-head Agda kernel not run**.

Video topics indexed: Landau QED pole, Gross-Wilczek/Politzer beta sign,
Wilson blocking, lattice gauge/closed holonomy, strong-coupling area law,
Creutz 1979 **and distinct 1980** numerical studies, dimensional transmutation,
Balaban and MRS fixed-IR vs infinite-volume limitation, stochastic Parisi-Wu
and 2024 local 3D YM-Higgs, Chevyrev-Shen 2026 3D gauge-covariant
renormalisation uniqueness and 2D invariant YM Langevin law, classical
Donaldson/Freedman/Casson/Gompf instanton topology and exotic R4.

**Exact live highest-alpha payment remains unchanged:** actual R445
selected same-source physical 4D CMP119 Wilson measure/tails/moments, real
selected continuum family and OS axioms, R281/P3 literal spectrum =
reconstructed `H_OS` spectrum, nontriviality, uniform IR infinite-volume
gap and Clay group scope. Finite loop bounds and R320→R333 compilers are
not these inputs.

New finite classical Hodge result is **not** the metric Hodge-star of a
smooth 4-manifold: the missing lifts are linear extension, oriented metric,
2-form half projections, ASD/SD curvature, classical YM E-L implication,
instanton moduli and external smooth four-manifold topology theorems.
The existing `YMStrictSelectedHodgeAlgebraLaws` is finite 2D/selected and
must not be identified with this new flat Euclidean R4 basis. Likewise,
3D local-time Markov existence, equilibrium of the *same* 3D stochastic
flow and a 4D pure YM QFT are separate theorem targets.

**Attribution:** named original authors hold source claims; DASHI owns
source-written adapters only. No Monster/3B, ESD or Clay promotion.

# Clay Yang-Mills Proof Roadmap


### P2 rational-trace / same-algebra alternative (30 October extension)

The canonical `BalabanSU2RationalWilsonTraceBoundExact` proves
`-1 <= realPart(q) <= 1` for rational unit-quaternion SU(2) data.
`YMClayLiteralWilsonS2SameAlgebraBoundExact` now defines the proof-bearing
`RationalSU2TraceGramBoundSource` and the explicit projections
`rationalSU2TraceToSameAlgebraWilsonBounds` and
`rationalSU2TraceBuildsCanonicalS2`. Once one same-carrier `pointwiseUnitBoundGivesGramBounded` interpretation and `traceIsLiteralWilson` equality are exhibited, **all loopwise boundedness fields** follow from the existing literal configuration-dependent Wilson-path theorem. The resulting
canonical S2 inputs feed `YMClayLiteralWilsonP2ExpectationConvergenceExact`
and the already-proved three selected expectation-limit compilers. This removes a family of duplicate P2 per-loop boundedness proofs. The record now additionally requires `traceIsLiteralWilson`, an explicit equality on the SAME physical loop carrier. Boundedness is transported along that equality with `subst`; an arbitrary synthetic trace observable cannot be substituted into P2.

The exact
remaining P2 obligations are now the trace→Gram physical interpretation,
bounded-product closure, exact literal identity same-object equality, selected Euclidean
translate/support-time identity, and actual measure convergence on the same
physical theory. The rational-quaternion argument alone is **not** a proof
over full continuum Haar SU(2), nor an independent gauge-measure limit.



### Canonical rational Wilson-function donor (30 October late reuse correction)

Further source-tree archaeology found the existing
`BalabanLiteralRationalSU2WilsonBoundedAlgebraExact.agda` owner. It already
constructs **configuration-dependent** `RationalWilsonPath n` observables
using periodic bond holonomies, proves the complete pointwise unit bound
`literalWilsonPathPointwiseUnitBounded`, and proves one/multiplication
pointwise closure. The new P2 bridge now consumes this owner *directly*:
`physicalWilsonObservable : RationalWilsonObservable n → TestObservable`,
`traceIsLiteralWilson` on the actual path observable, and
`pointwiseUnitBoundGivesGramBounded` transport the existing theorem onto
the same physical `Gram.BoundedObservable` carrier. The bounded identity
follows from the existing literal unit observable and an exact same-object
identity equality, rather than being independently assumed.

This replaces the earlier fixed-quaternion-per-path approximation: path
holonomy necessarily depends on the configuration. The S2 adapter also fixes the literal SU(2) scalar ABI definitionally: `one = 1ℚ`, `groupRank = 1ℚ`, and scalar multiplication is rational multiplication, rather than accepting unconstrained numeric placeholders.

Generic
`Gram.BoundedObservable` multiplication closure is still a separate
stronger physical algebra input than rational-image pointwise closure. This
is the real remaining P2 implementation wall, alongside the physical
trace/Gram map and limit/time semantics.



### 30 October, subsequent source-first native-P2 max-cut

The stronger already-existing donor chain is now authoritative for **native**
rational Wilson paths:

```
BalabanLiteralRationalSU2WilsonBoundedAlgebraExact
  -> BalabanLiteralRationalSU2WilsonCylinderBoundDataExact
  -> BalabanLiteralWilsonNativeThermodynamicProducerExact
  -> BalabanLiteralWilsonNativePhysicalMeasureExact
  -> YMClayLiteralWilsonP2NativeMeasureExact.nativeWilsonP2Limits
```

The native physical-measure owner explicitly sets
`Gram.BoundedObservable = Σ majorant, QuantitativeBound` and
`Gram.multiplyObservable =` pointwise Wilson multiplication. Thus the earlier
generic `RationalSU2TraceGramBoundSource` with its separately provided
trace-to-Gram and generic multiplication closure is a **compatibility** route,
not a primitive P2 input in the native path.

In `YMClayLiteralWilsonS2SameAlgebraBoundExact`,
`nativeWilsonSameAlgebraBoundInputs` reuses the already-produced
quantitative Wilson path bound, unit bound, bounded products and native
physical-measure definitions. No new analytic closure is assumed in this
specialization. Moreover `nativeWilsonP2Limits` already constructs all
three actual convergence proofs **without** support-distance/time geometry;
support-distance belongs to P1. Its thermodynamic/expectation input package
still must be physically inhabited; the syntactic construction is not itself
a new four-dimensional measure-existence theorem.

**Normalization fix:** the canonical `literalRationalSU2WilsonCylinderBounds`
uses `groupRank = 1ℚ` for normalized Wilson traces. The new S2 adapter now
matches this exact source, rather than confusing normalized trace with the
matrix representation dimension two. This is a same-object semantic correction.

P3 donor search also found pre-existing
`YangMillsDirectSourceOSReconstructedSpectrumH3Exact` and
`YangMillsClayCMP119RealSameOSH3Exact`. Both retain the physical
selected-spectrum / actual reconstructed `H_OS` identification as a
proof-bearing input; no new synthetic H3 spectrum is introduced.




### R445 same-marked-moment source to native P2 (30 October continuation)

Existing `BalabanClayT5MarkedMomentProducerRound444Exact` and
`BalabanClayT5MarkedPreferredExpectationRound445Exact` already compile
one marked-polymer moment closure into the exact preferred diagonal
expectation producer on a selected thermodynamic family.
`BalabanLiteralWilsonNativePhysicalMeasureExact.nativeWilsonPreferredFromMarked`
now reuses that R445 input **on the same native Wilson thermodynamic
carrier**, then
`YMClayLiteralWilsonP2NativeMeasureExact.nativeWilsonP2FromMarkedSource`
constructs the actual three P2 expectation limits using the existing
`nativeWilsonP2Limits`. No second moment package, covariance shortcut,
support-distance theorem or independent trace-to-Gram interpretation is
introduced in the native route. Remaining inputs are the actual R445
`boundedObservableTail`, continuum-tail witness, selected moment
realization and physically identified native thermodynamic/measure family.
The real CMP119 and rational P2 carriers are not asserted equal by analogy.

The 2026 external literature scan included OpenAI's October 26 public
scientific-collaboration announcement, Bałaban's original CMP116 record,
and contemporary proof proposals; externally authored proof claims are
inspiration/search inputs, not kernel proof terms or guaranteed physical
witnesses. QIDs are discovery/provenance identifiers and do not substitute
for mathematical same-object equalities; the existing Ibrahim/QID and
Monster3B ownership fences remain unchanged.


## 2026-10-30 — Route-S H1 direct-source Pareto weld

The highest-value reuse cut is the **direct source/OS** mass-gap route, not a
repetition of the strong F1/F3/F4 Mosco path. The existing owners already
provide the exact compiler spine:

```text
R320 DirectSelectedT5MarkedDecayPayment (literal selected two-J inequality)
  -> YMClayRouteSH1DirectSelectedMarkedDecayExact.h1BuildsLocalizedR295
  -> R313.exactT5JMagnitudeFromR295 (with rational |·| meaning)
  -> R296.ExactT5JMagnitudePresentation
  -> R333.CanonicalBOSIndexedApplication + Completion
  -> OS.PhysicalMassGapCertificate on the SAME reconstructed H_OS
```

The new direct bridge in `YMClayDirectSourceOSMassGapFrontierExact` is an
explicit Agda composition of **existing** owners, not a new selected-source
inequality. It removes the apparent need to pay R295/R296 again after H1.
Its remaining actual inputs are R320 physical source localization, rational
absolute-magnitude interpretation, R333's physical Wilson/time, expectation
limit and same-H_OS spectral witnesses. P1/P2/P3 in the September closed-world
audit are the corresponding direct-route cut. The independent strong
F1-C/F1-D/P_a/E_a/Mosco obligations are **not** terminal prerequisites of
Route S, but remain available for the other Pareto lane.

Source roots and authorship: Tadeusz Bałaban, CMP 116 (1988), DOI
10.1007/BF01239022 (cluster expansions and differentiated localization);
R295/R313/R320/R333 are independently authored DASHI theorem interfaces and
compilers. A published paper, a typed import, a source-written proof and an
exact-head kernel check are distinct evidence levels. No physical source
witness is fabricated; no continuum or Clay promotion occurs from this weld.
The direct consumer is now smaller and can be attacked at its actual literal
Wilson P1/P2/P3 physical inputs; all-compact-simple-group and local-QFT
extension remains a separate terminal scope. Reference comparison: OpenAI's
26 October 2026 existence announcement is not an imported proof: its Yang–Mills
Lean artifacts were not publicly released as of this review.

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
Jaffe-Witten Yang-Mills existence and mass-gap problem would have to prove.
It is not a proof, and it does not promote any Clay, Wightman, Standard Model,
or terminal claim.

Current corpus correction: the live Clay-facing manuscript is now
`Docs/papers/live/Paper3YangMillsClayDraft.md`, and it sharpens the real
frontier. The finite self-adjointness and domination steps are internal to the
current draft. The older `H3a -> H3b -> no-spectral-pollution ->
thermodynamic/OS/Wightman -> mass-gap/uniqueness` continuum theorem chain is
now recorded internally at its owning theorem surfaces. The remaining live YM
frontier is therefore narrower: Clay-promotion authority, physical
Hamiltonian/mass-gap identification, statement-formulation equivalence, and
external acceptance/review. Read the roadmap below as a wider dependency
ledger, not as a more current statement than the live paper.

Current packaging correction: the repo now records the exact theorem-shape
authority chain `H3a -> H3b -> no-spectral-pollution -> RP/OS -> Wightman ->
continuum mass-gap transfer` in the proof-facing Agda boundaries. This is a
governance improvement, not a theorem promotion: the Yang-Mills frontier
remains authority-backed unless the full Balaban multiscale package is
internalized.

Current governance correction: YM is now the only major lane whose remaining
burden is still naturally missing-content-shaped rather than merely
promotion-evidence-shaped. The continuum theorem chain is explicit and wired;
the remaining load-bearing in-repo burden is the final Clay boundary rather
than H3a/H3b themselves, unless the repo stays authority-backed by design.

Reviewer-packet correction: the repo now also carries an explicit final
authority-packet layer for the same chain. The finite self-adjointness,
domination, and finite spectral-margin story is internal; `H3a`, RP/OS,
Wightman, and the final continuum transfer remain explicit external or
authority-backed steps. This improves submission grammar only and does not
change theorem ownership.

## Sprint 79 Current Fork

The live in-repo YM fork now has two ordered lanes. The UV-continuum lane comes
from Eriksson 2602.0077:

```text
Eriksson26020077Theorem16Conditional
-> BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
-> SquaredOscillationSummabilityForHalfPlaneBlocking
-> FixedFiniteVolumeBlockedObservableContinuumLimit
```

The open DASHI target in this lane is `AnisotropicAssumptionA`: the
squared-oscillation summability bound for the half-plane/spatial Balaban
blocking map `Q_hp`. The favorable spatial link count `3*L^(3k)` is only an
arithmetic balance until that bound is proved. This lane does not prove OS
reflection positivity, the thermodynamic limit, or a mass gap.

Sprint 80 narrows the immediate proof target to:

```text
BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
```

The conditional product is
`3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)<=3*C_local^2`. At `L=2,k=9`,
the anisotropic factor is `0.005859375` relative to `C_local^2`, and
`0.00146484375` relative to the isotropic `4*C^2` baseline.

Sprint 81 attempts the first item above from in-repo material and keeps it
fail-closed. Before `BalabanCMP98LocalOscillationBoundForQhp` can become a
proof object, the repo must define or import:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
```

Sprint 81A adds a conditional authority branch. Relative to an explicit
Balaban CMP 98 local-oscillation authority input, the in-repo arithmetic closes
`LipschitzToSquaredOscillationForQhp` and `AnisotropicAssumptionA`. The CMP 98
locality theorem itself remains an external authority input, so this does not
promote Clay/YM or a mass gap.

Sprint 81B records the support-interface blocker for the KP lane, and Sprint
81C defines the typed carriers for
`BalabanEffectiveAction`, `Polymer`, `PolymerIn`, `LinkKind`, `TemporalLink`,
`SpatialLink`, `PolymerSupport`, `SpatialSupport`,
`ResidualEffectiveActionTerm`, `ActivityDependsOnlyOnLinksInsidePolymer`,
`TemporalMeasureFactorizationLambdaOneReconciled`, and
`DefinedOnBlockedL2SpatialGraph`. The next theorem is
`EffectiveActionPolymersSpatialOnlyForA1`; only after that can the blocked
`eta=4` count be earned.

The separate KP/mass-gap lane has moved to the strong Gate-B carrier path.
The legacy weak `PolymerIn` bridge is refuted for the current carrier and is
kept only as a diagnostic guardrail.  The proof-critical lane is now:

```text
StrongActionTermTransferResidualDisjointness
-> StrongResidualPolymerMembership
-> StrongGateBToKPTheorem
-> KPEntropyAtBlockedScaleL2
-> AnisotropicL2WeightedKPCloses
-> AllDiameterWeightedKP
-> SmallFieldBoundsSurviveAnisotropicBlocking
-> BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
-> LatticeMassGapFromAnisotropicKP
-> ContinuumMassGapTransfer
-> OSWightmanReconstruction
-> ClayYangMills
```

The current route decisions are:

```text
UV: ANISOTROPIC_ASSUMPTION_A_PROVED_IN_REPO; NEXT_BLOCKER_FIXED_FINITE_VOLUME_BLOCKED_OBSERVABLE_CONTINUUM_LIMIT_CONDITIONAL
KP: STRONG_GATE_B_TO_KP_CLOSED; NEXT_BLOCKER_SMALL_FIELD_SURVIVAL
```

```text
q  = 0.23178189475262734
4q = 0.9271275790105094   closes on the strong blocked L=2 eta=4 lane
6q = 1.390691368515764    blocks fine-lattice spatial eta=6
8q = 1.8542551580210187   blocks generic 4D eta=8
```

`YMSmallFieldSurvivalAuthority` now splits the next gate into three in-repo
structural inputs, six imported analytic theorem slots, and one native
spatial-orbit slot.  Spatial-only blocking
compatibility, temporal-transfer compatibility, and polymer-activity
preservation are derived from the strong sector/KP stack.  The remaining
small-field blockers are `BalabanSmallFieldRegionStability`,
`BalabanFluctuationCovarianceBound`,
`BalabanPolymerActivityExponentialDecay`, `BalabanScaleUniformConstants`,
`GaugeFixingJacobianBound`, and `GaugeOrbitVolumeUniform`; the
`SpatialBlockingPreservesGaugeOrbit` slot is native/derived. Clay/YM promotion
remains false.

The downstream authority lane is decomposed rather than opaque:
`YMLatticeMassGapAuthority` now exposes four transfer/spectral-gap theorem
slots, `YMThermodynamicLimitAuthority` exposes five volume/continuum theorem
slots, `YMOSAxiomsAuthority` exposes five OS axiom theorem slots, and
`YMContinuumMassGapTransferAuthority` exposes four continuum spectral-transfer
slots.  These slots are the current authority lane; they are not internal
analytic proofs.

The immediate UV tranche is to prove or falsify:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
BalabanCMP98LocalOscillationBoundForQhp
LipschitzToSquaredOscillationForQhp
AnisotropicAssumptionA
SquaredOscillationSummabilityForHalfPlaneBlocking
```

The immediate KP tranche is to prove or falsify:

```text
EffectiveActionPolymersSpatialOnlyForA1
PolymerDefinedOnBlockedLattice
KPEntropyAtBlockedScaleL2
```

All later Balaban, small-field, lattice, continuum, OS/Wightman, and Clay
endpoint obligations remain open.

Weak-coupling bookkeeping correction for `2026-06-13`: the repo now has a
typed fail-closed polymer convergence package for the Paper 3 YM lane:

```text
YMLatticeAnimalCountingBoundReceipt
-> YMWeakCouplingRatioBoundReceipt
-> YMGeometricTailHalfBoundReceipt
-> YMPolymerWeakCouplingSumBoundReceipt
-> YMP7WeakCouplingPolymerConvergenceReceipt
```

This package records the `d=4` lattice-animal count surface `N_n <= (8e)^n`,
the tuned weak-coupling ratio surface `a = c_K / (4 g^2)`, the corrected
same-prime `p=7` threshold `c_K >= (4/3) log(24e)`, the geometric-tail
`<= 1/2` surface, the grouped origin-containing weighted polymer sum surface,
and the bridge back into the same-prime `p=7` Wilson activity lane. The repo
now uses that package to close the exact lane-local `p=7` local KP theorem
surface, then records lane-local strict absorption, uniform-volume KP, and
Balaban RG transfer as true in their owning receipts. It still does not prove
continuum Yang-Mills, mass gap, or Clay Yang-Mills.

Audit boundary: finite carrier spectral gaps, finite transfer-matrix gaps,
carrier string-tension diagnostics, and finite strong-coupling estimates are
evidence only.  They are not the Clay Yang-Mills theorem.  A Clay-level result
still requires a continuum Yang-Mills construction, Osterwalder-Schrader
axioms for the continuum gauge theory, reflection positivity at the right
continuum/infinite-volume object, an infinite-volume limit, and operator or
Hamiltonian convergence identifying a positive physical mass gap.  None of
those Clay-level obligations is proved in the current repository.

KP/RG/atom receipt boundary: `KPCouplingObstruction`,
`BruhatTitsBraidKPReduction`, and `AtomExtendedCarrierFrame` are governance
receipts, not Clay progress.  `KPCouplingObstruction` corrects the physical
`p=7` threshold to `beta_min ~= 10.13`, so the physical Wilson beta route fails
unless a separate RG bridge is supplied.  `BruhatTitsBraidKPReduction` may keep
the carrier RG beta branch conditionally passable under carrier hypotheses, but
that is not physical beta running, continuum tightness, OS/Wightman
reconstruction, or a mass-gap theorem.  `AtomExtendedCarrierFrame` is blocked by
an explicit `A > 0` positivity obligation before it can be consumed as analytic
input.

Spectral tower tranche boundary: the current tower distinguishes five
authority levels.  A0 is diagnostic/prose, A1 is finite diagonal
spectralizable evidence, A2 is a typed theorem target, A3 is calibrated
subclass decidability, and A4 is runtime/semantic/continuum/Clay promotion.
The PNF residual finite diagonal spectral severity receipt is A1 only: its
proof is spectralizable finite diagonal evidence, not runtime behavior or
semantic truth.  `SpectralTowerTheoremTarget` is A2, not theorem closure.  NS
FRACTRAN admissibility is A3 only for the Kolmogorov-calibrated subclass.  No
A4 continuum, Clay, runtime-semantic, or terminal claim is promoted here.
`YMContinuumGapFromCarrierConditionalReceipt` and
`YMFourStepsConditionalReceipt` record the Gate-3 reduction and four analytic
steps as conditional ledgers.  They do not construct self-adjoint continuum
YM, strict Mourre positivity, QFT ground-state uniqueness, weak spectral
measure survival, or a Clay mass gap.

Corrected math boundary: no current roadmap step may say that a gap
strengthens to `3.0`.  Where the CM/infinite-depth spectral comparison is
discussed, the honest Selberg-style lower-bound target is
`lambda1 >= 3/16`, still below Clay promotion.  Gate 3 remains the hard lift
from the carrier dictionary to `S'`, Chern-character compatibility, and the
real norm theorem.  K-theory/Bott language is a framing target only, not a
proof.  The PNF spectral-severity surface is finite diagonal evidence, and
any PNF-to-Z7 arrow remains open/lossy.  The two Clay reductions are
conditional ledgers only.

Spectral/Mosco receipt boundary: the new spectral receipt set must be read as
route organization and finite evidence, not as a continuum operator theorem.
For Gate 3, the blocking bridge is not merely "more spectral data."  It has
three named obligations: Mosco upper/density control for the selected carrier
core, a no-spectral-pollution theorem through the cutoff/depth limiting
process, and a mass-shell bridge that identifies the limiting operator
spectrum with the physical gauge-invariant mass surface.  Until all three are
proved, finite carrier spectral gaps, PNF spectral severity, and tower targets
cannot be promoted to L7/L8/L9, Wightman reconstruction, or Clay Yang-Mills.

NS two-phase diagnostic boundary: the current two-phase trace is empirical
diagnostic evidence only.  It falsifies the combined `Q_log` lane2+lane7
reading.  Scalar EV5 Lyapunov is rejected as the live criterion.  The current
candidate is vector-valued EV5, with lane7 read only as the dissipation
witness and lane2 read only as the bounded migration witness.  Those witnesses
are not an actual-flow Navier-Stokes transfer theorem, not a Serrin/BKM
estimate, not smooth regularity, and not Clay NS.  They may motivate future
projection and comparison tests, but they cannot discharge any YM Gate 3 or NS
Clay obligation.

Wave-pool/Gate3 boundary: the caisson/standing-wave picture is now recorded
only as a proof-search dictionary.  `CarrierMoscoConvergenceFromPhysicsReceipt`
keeps Mosco as a strong-resolvent/density route, not norm-resolvent
convergence.  `GreensFunctionConvergenceRateReceipt` records the finite
caisson convergence heuristic and the NS critical-index boundary, but leaves
the analytic bound open.  `CarrierPhaseStructureReceipt` records that YM can
quotient gauge phase in the physical Hilbert-space reading while NS cannot
treat high-prime phase loss as gauge.  These receipts explain why Gate 3 may
be easier for YM than NS; they do not prove Gate 3, OS/Wightman
reconstruction, or a Clay mass gap.

Codec atom / phase boundary: `CanonicalCodecAtomReceipt` records the common
codec form as coarse field plus sparse signed anisotropic atoms plus an MDL
residual budget.  This is a useful bridge because it identifies random-phase
residual synthesis as the implementation-level symptom of the same phase loss
that Gate 3 must control.  The receipt keeps the atom phase, orientation,
anisotropy, and twist fields visible, but it does not implement the runtime
codec, prove MDL matching pursuit, prove phase-aware decode stability, prove
Gate 3 density, or promote any NS/YM/Clay result.

Carrier phase/Gribov/BT-tree boundary: carrier gauge fixing is a
BT-tree/discrete-resolution statement inside the non-Archimedean carrier.  It
selects canonical representatives only at that finite/discrete carrier
authority.  Singer's continuum obstruction and the continuum Gribov-copy
problem remain open.  The `p=7` amplitude sector has a `Z/7` gap, while the
phase-unit sector is `Z/6`; these are different, incommensurable sectors and
must not be identified, divided through each other, or consumed as a single
phase/gap theorem.  Gate 3 must first prove trivial-sector density and the
continuum lift before any carrier representative, phase quotient, or finite
gap can be consumed by the continuum YM route.

Feshbach-Schur / fiber-gap boundary: the finite carrier fiber gap is only an
ingredient.  It may be used as local spectral evidence, but it does not by
itself establish a gap for the full tensor-product Hamiltonian.  The full
tensor-product route now has an explicit receipt,
`YMFeshbachSchurFiberGapBridgeReceipt`, which keeps promotion false until all
of the following are supplied: Gate 3 density of the selected carrier core in
the target Hilbert space, a Feshbach projection decomposition, invertibility
and lower control of the Schur complement on the complement, off-diagonal
relative bounds, and domain/core compatibility for the tensor Hamiltonian.
The existing `FiniteCarrierSpectralGapZ7Receipt` product-spectrum calculation
is therefore read as finite Cartesian-product evidence only, not as a physical
tensor-product Yang-Mills gap.

Balaban/RG induction gap: the preferred carrier-side YM attack is now the
KP/Balaban route.  This is not "Clay YM" as a solved claim.  It is the
concrete KP/uniform-volume obligation needed for a Balaban-style induction
step:

`H_k -> H_{k+1}` with Kotecky-Preiss polymer local-sum constants, small-field
bounds, large-field tail bounds, counterterm control, and block-averaging
error terms all uniform in lattice volume and stable under cutoff/depth
removal.

The repository now records this obligation explicitly in the Balaban,
polymer/KP, and carrier area-law receipts.  It is not proved or imported, and
`exactDecorrelation` must remain open unless supplied by a separate proof.
The naive 15-prime KP series fails; the admissible proof candidate must first
use a single-prime overlap reduction and then rebuild the KP local-sum bounds
from that reduced overlap surface.  The corrected reduction is only an
overlap-set statement: polymer activity is not multiplicative for
disjoint-prime polymers.  The cross term produced by the overlap split must
be bounded or recorded as an explicit obstruction before any KP/Balaban
local-sum estimate consumes the reduction.
Finite MDL/Fejer descent, finite strong-coupling bounds, and finite polymer
bookkeeping are only support surfaces.  The large/small field split is also
open: the ultrametric small-field sector is the carrier ball controlled by
existing finite estimates, while the large-field sector still needs a
tail-suppression estimate strong enough to feed the volume-independent RG
induction.

Braid boundary: there is no braiding inside one BT tree.  A product of
distinct commuting prime lanes is abelian bookkeeping, not a nonabelian braid
theorem.  Same-prime braid/Yang-Baxter remains an open target and cannot be
used as a proved input to the YM roadmap.

The current tower names the blockers through receipts such as
`ClayMillenniumClosureTargetReceipt`, `CarrierFactorVecInjectivityOSPositivity`,
`RGOperatorNormReceipt`, `RGBanachFixedPointReceipt`,
`OSPositivityFromRGFixedPoint`, `ScalarOSTransferMatrixReceipt`, and
`ClayBlockerUpdateReceipt`. `GribovFreeCarrierReceipt` is also available as a
carrier-only canonical-representative receipt: it consumes the concrete
`FactorVec` identity quotient, records uniqueness of the selected
representative in that identity fiber, and points at the existing
`factorVecQCoordinate` / p2-Lorentz coordinate-law primitives. It is not a
continuum Gribov theorem and it does not assert a smooth global gauge-fixing
slice. Newer finite-lattice receipts add a Wilson carrier lattice,
strong-coupling expansion, carrier string-tension estimate, finite
transfer-matrix gap, and an L2 status receipt. Those receipts give a blocker
map. The roadmap below decomposes the blocker into lemmas.

## Corrected Competitive Path

Historical broad roadmap context: the current competitive route is not "finite carrier pressure is below the
canonical dimension, therefore Yang-Mills has a mass gap."  In particular,
the local fact recorded by the pressure-below-15 surfaces,
`pressureBound = 14`, `canonicalDim = 15`, and `14 < 15`, is only a bounded
carrier diagnostic.  It is not a continuum spectral theorem and it cannot be
consumed as a Clay mass-gap proof.

Any credible DASHI-facing Clay YM path has to solve three hard problems as
mathematical theorems, in this dependency shape:

```text
H1 Balaban volume-independent induction
  -> H2 BRST reflection positivity
  -> H3 operator-valued spectral gap
  -> Clay YM existence and mass gap
```

After Sprint 79, the immediate H1 subproblem is narrower: prove the residual
KP graph is blocked-spatial, not fine-lattice spatial. `H1` still means a
genuine volume-independent constructive RG/cluster induction,
not a fixed finite-depth contraction receipt.  It must supply bounds uniform
enough for infinite volume and cutoff removal.

`H2` means reflection positivity for the gauge-fixed/BRST-compatible
continuum object, with the unphysical degrees of freedom controlled so that
OS/Wightman reconstruction is applicable to the physical sector.  Finite
Wilson reflection positivity or scalar-sector transfer positivity does not
discharge this step.

`H3` means a positive lower bound for the physical, operator-valued continuum
Hamiltonian or transfer generator, stable under the limiting process and
identified with the reconstructed gauge-invariant spectrum.  A scalar
inequality, finite carrier eigenvalue, transfer-matrix gap at fixed lattice
scope, or `14 < 15` pressure diagnostic is not this theorem.

The old `L1-L9` lemma map below remains useful as a decomposition of
existence and mass-gap obligations.  The governance rule is that no L7-L9
promotion may be recorded unless the H1/H2/H3 chain is explicitly discharged
or replaced by an equally strong theorem with the same continuum, positivity,
and operator-spectrum content.

## Dependency Graph

```text
L1 lattice YM measure
  -> L2 uniform correlator bounds
  -> L3 tightness of cutoff measures
  -> L4 continuum weak limit
  -> L5 OS axioms for the gauge theory
  -> L6 OS/Wightman reconstruction

L1, L2, L5
  -> L7 uniform transfer-matrix spectral gap
  -> L8 gap survives the continuum limit
  -> L9 physical mass gap in the reconstructed QFT
```

The existence block is `L1-L6`. The mass-gap block is `L7-L9`. A Clay-level
result requires both blocks.

## Lemma Status

| Lemma | Required mathematical content | Current carrier status | Existing receipt surface | Gap |
|---|---|---|---|---|
| L1 | Construct a lattice Yang-Mills measure at each cutoff/lattice spacing for compact gauge group `G`. | Partial target only. The carrier has finite FactorVec/RG scaffolding and finite gauge candidates, but no selected continuum YM gauge measure. | `CarrierRenormalizationGroupScaleReceipt`, `RGContractionReceipt`, `FactorVecAverageVsSumReceipt`, `RGOperatorNormFormalProof` | Need a genuine lattice YM action/measure tied to a carrier-derived compact gauge group. |
| L2 | Prove uniform cutoff-independent bounds on Schwinger/correlation functions, including reflection positivity and exponential decay where needed. | Partially inhabited only in the finite carrier strong-coupling regime. A corrected two-plaquette strong-coupling bound, carrier string tension `sigma ~= 5.27`, exponential plaquette decay at `beta = alpha1`, and a finite lattice gap are recorded as finite evidence only. | `StrongCouplingExpansionReceipt`, `UniformBoundStrongCouplingReceipt`, `StringTensionCarrierReceipt`, `LatticeMassGapFromTransferMatrixReceipt`, `YML2StatusReceipt`, `PolymerKPAsMDLReceipt`, `CarrierAreaLawBalabanSeedReceipt` | Need the KP/uniform-volume polymer obligation: volume-independent local-sum constants, small-field bounds, large-field tail bounds, counterterm control, continuum beta running, tightness as depth/cutoff is removed, dimensionful scale anchoring, infinite-volume control, and gap survival. |
| L3 | Prove tightness/compactness of the cutoff measure family as the cutoff is removed. | Uninhabited. RG contraction and Banach fixed-point receipts are finite/conditional and do not give continuum measure tightness. | `RGBanachFixedPointReceipt`, `OSPositivityFromRGFixedPoint`, `ClayBlockerUpdateReceipt` | Need compactness in the continuum constructive-QFT topology. |
| L4 | Extract a weak continuum limit and prove the limit is nontrivial. | Uninhabited. Continuum RG convergence is named open. | `ContinuumClayMassGapReceiptObligation`, `ClayBlockerUpdateReceipt` | Need interacting continuum YM, not just finite carrier limits or scalar transfer positivity. |
| L5 | Prove the continuum limit satisfies OS axioms: OS positivity, Euclidean covariance, symmetry, clustering, and regularity. | Partially inhabited only for finite scalar and finite ungauge-fixed Wilson-loop carrier inputs. The OS3 boundary is now explicit: ungauge-fixed Wilson positivity is finite-lattice evidence; BRST/Faddeev-Popov gauge fixing is not a positive-Hilbert OS3 proof because of the indefinite/Krein sector; ghost time reflection requires a graded sign/involution; carrier Gribov-free wording is only a representative choice, not a continuum Gribov-copy theorem. Full gauge OS, continuum reflection positivity, covariance, and infinite-volume OS control remain open. | `ScalarOSTransferMatrixReceipt`, `OSAxiomsContinuumStatus`, `WightmanReconstructionCandidateReceipt`, `YML5OSAxiomsForGaugeSectorReceipt`, `GribovFreeCarrierReceipt` | Need gauge-sector reflection positivity at the continuum/infinite-volume object, a gauge-invariant or quotient-compatible OS3 construction, ghost/BRST handling that lands in a positive physical Hilbert space, a real continuum Gribov-copy boundary, and restoration of full Euclidean covariance. |
| Gribov carrier guardrail | For any gauge-fixed route, distinguish carrier representative choice from a continuum Gribov-copy theorem. | Inhabited only for the local `FactorVec` identity quotient: the canonical representative is unique in the identity fiber and the coordinate projection primitive is recorded. | `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need an accepted continuum theorem for smooth YM connections before making any global gauge-fixing or Gribov-free continuum claim. |
| Phase/BT-tree guardrail | Keep carrier phase fixing, finite amplitude gaps, and continuum gauge fixing in separate sectors. | Inhabited only as non-Archimedean BT-tree/discrete-resolution bookkeeping.  The `p=7` amplitude `Z/7` gap is not the `Z/6` phase-unit sector. | `CarrierPhaseStructureReceipt`, `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need Gate 3 trivial-sector density, a continuum lift, and an independent continuum Gribov/Singer resolution before consuming this data in L5-L9. |
| L6 | Apply OS reconstruction to obtain a Hilbert space, fields, and Hamiltonian satisfying Wightman axioms. | Uninhabited. Reconstruction is a target/citation boundary only. | `ClayMillenniumClosureTargetReceipt`, `WightmanReconstructionCandidateReceipt` | Need L5 first, plus authority binding for all reconstruction hypotheses. |
| L7 | Prove the transfer matrix has a positive spectral gap uniformly in cutoff. | Uninhabited. Finite candidate gaps and selected finite PSD diagnostics do not give a uniform gauge gap. | `H0OSPositivityBaseCase`, `H0ExplicitMatrixReceipt`, `NormalisedH0OSPositivity`, `BalabanRGMassGapReceiptSurface` | Need a depth/cutoff-independent lower bound for the physical gauge Hamiltonian. |
| L8 | Prove the spectral gap survives the continuum limit. | Uninhabited. Requires L3/L4 and L7. Finite carrier gaps are evidence only. | `ColimitGapLiftOnHamiltonian`, `ContinuumClayMassGapReceiptObligation` | Need semicontinuity or a stronger operator/Hamiltonian convergence theorem for the infinite-volume continuum Hamiltonians. |
| L9 | Identify the limiting spectral gap with the physical Yang-Mills mass gap. | Uninhabited. The physical Hamiltonian/gauge group identification remains open. | `YangMillsMassGapBoundary`, `ClayMillenniumClosureTargetReceipt`, `Paper8UnificationBlockerMap` | Need a reconstructed physical Hilbert space and gauge-invariant one-particle/mass spectrum. |

## Feshbach-Schur Fiber-Gap Route

The admissible finite-to-full-gap route is now:

1. Record a carrier fiber spectral gap as evidence.  This is currently
   available for selected finite carriers, including the Z/7 cycle receipt and
   its finite product-spectrum caveat.
2. Prove Gate 3 density for the selected carrier core inside the target
   Hilbert space.  The current `Gate3NormDictionary` reaches a finite
   limit-71 inequality surface, but density remains false.
3. Supply the Feshbach-Schur operator hypotheses: projection decomposition,
   Schur complement invertibility, off-diagonal relative bounds, and domain
   compatibility for the full tensor Hamiltonian.
4. Only after those hypotheses can a tensor-product spectral lower bound be
   stated.  The current repository has no such bound and no Clay promotion.

This route is deliberately narrower than a Clay claim.  It is a local bridge
obligation for turning finite fiber evidence into a candidate operator theorem;
it still sits below L7/L8/L9 and below the continuum construction and
authority requirements.

## Current Honest Position

Update after the second roadmap-execution tranche: YM L1 is inhabited only at
finite carrier-lattice scope, and YM L2 is now partially inhabited only in a
finite strong-coupling scope. The tower has receipts for a three-site carrier
spatial lattice, depth as Euclidean time, a Wilson action with spatial and
spatial-temporal plaquettes, finite-lattice Wilson reflection positivity, a
strong-coupling plaquette expansion, a corrected connected two-plaquette
bound in the strong phase, a carrier string-tension estimate `sigma ~= 5.27`,
and a finite transfer-matrix gap.

This is not continuum Yang-Mills. The strong-coupling result is at carrier
`beta = alpha1` and records exponential decay in carrier units; it does not
construct the beta-to-infinity Wilson continuum trajectory, a dimensionful
physical mass scale, a Wightman theory, or Clay mass-gap promotion.

The carrier still does not have continuum beta running, continuum tightness,
continuum OS axioms, continuum reflection positivity, a BRST gauge-fixed
positive-Hilbert OS3 construction, a ghost time-reflection graded-sign theorem,
a continuum Gribov-copy resolution, an infinite-volume limit, Wightman
reconstruction, operator/Hamiltonian convergence, a weak-coupling/continuum
uniform correlator theorem, or a uniform continuum spectral gap.

The next admissible YM tranche should not aim vaguely at "Clay YM." It should
target the H1/L2-to-L3 interface: prove or refute a Balaban-style
volume-independent induction with constants independent of carrier depth and
volume, then isolate the BRST reflection-positivity and operator-valued
spectral-gap hypotheses required before any continuum limit can be consumed
as Clay evidence.

More concretely, the target is the KP/uniform-volume induction obligation:
prove the Kotecky-Preiss polymer bound with constants independent of the
spatial volume, prove the corrected single-prime overlap-set reduction and
its cross-term bound, prove `exactDecorrelation` if that route consumes it, prove an
ultrametric large/small field split with the large-field tail suppressed
uniformly enough for `H_k -> H_{k+1}`, and show that the resulting counterterm
and block-averaging errors remain controlled through cutoff/depth removal.
This would be a competitive Yang-Mills contribution if proved; it is currently
only an open obligation.

Phase 2 update: `StrongCouplingExpansionReceipt`,
`StringTensionCarrierReceipt`, `UniformBoundStrongCouplingReceipt`,
`BetaCriticalReceipt`, `CarrierRGTrajectoryYMReceipt`, and
`YML2StatusReceipt` record a partial L2 result only in the finite
strong-coupling regime `beta=alpha1`.  This gives a carrier-unit
string-tension/area-law diagnostic and exponential plaquette-correlator decay,
but it is not the Wilson continuum trajectory because fixed `alpha1` is not
`beta -> infinity`.  `Phase2ProgrammeReceipt` therefore treats the next YM
work as continuum beta-running, tightness, scale anchoring, and gap-survival
work, not as Clay closure.

Corrected coupling update: `CarrierScaleFromHeegnerReceipt`,
`QCDRunningFromCarrierScaleReceipt`,
`CarrierGaugeCouplingFromCSLevelReceipt`,
`WilsonBetaFromCSLevelReceipt`, `YML2CorrectedStatusReceipt`, and
`YML3TightnessFromKRunningReceipt` separate `alpha1` from the Wilson beta
and record a CS-level candidate: `alpha_s=1/3`, `beta_SU2=3/pi`, finite
string tension `2.125`, and a `2.33 GeV` mass-gap diagnostic.  The candidate
L3 family is `{mu_k}` as `k -> infinity`; tightness, continuum weak limit,
Wightman reconstruction, and Clay Yang-Mills remain open.

The same Phase 2 programme also records the CS-level gauge-coupling frontier:
`SMGaugeGroupFromCS3LanesReceipt`, `LevelRankDecouplingReceipt`, and
`WBosonMassFromCSReceipt` give candidate gauge-factor origins and expose the
SU(2)-SU(3) level-rank decoupling and W-mass RG/scale-matching blockers.  This
is Gate 6/Gate 7 gauge-coupling context for the YM programme, not a proof of
direct-product gauge independence, physical coupling normalisation, exact
Standard Model reconstruction, or a Yang-Mills mass gap.

## Promotion Boundary

The following must remain false until all nine lemmas and the required
authority boundaries are discharged:

- Clay Yang-Mills mass-gap promotion
- Wightman reconstruction promotion
- full gauge-sector OS positivity
- continuum reflection positivity and infinite-volume OS limit
- continuum Gribov-free/global gauge-fixing promotion from the carrier
  representative receipt
- consuming BT-tree/discrete carrier gauge fixing as a continuum Gribov or
  Singer theorem
- identifying the `p=7` amplitude `Z/7` gap with the phase-unit `Z/6` sector
- consuming carrier phase quotients, carrier representatives, or finite gaps
  before Gate 3 proves trivial-sector density and the continuum lift
- continuum interacting Yang-Mills construction
- operator/Hamiltonian convergence from finite carriers to the continuum
- Balaban volume-independent induction for the continuum constructive route
- KP/uniform-volume Balaban induction
- single-prime overlap-set reduction and its cross-term bound for any KP proof
  after the failed naive 15-prime series
- `exactDecorrelation` as a consumed KP/Balaban input
- ultrametric large/small field split with large-field tail suppression
- same-prime braid/Yang-Baxter theorem, or any nonabelian braid claim from one
  BT tree or from distinct commuting prime lanes
- BRST-compatible reflection positivity for the physical gauge sector
- an operator-valued physical spectral-gap theorem
- any inference of the form "`14 < 15`; therefore Yang-Mills mass gap"
- treating finite/strong-coupling carrier YM as continuum Clay YM
- terminal/unification promotion


### Max-cut 2026-11-01: native side-four rational-SU2 Wilson/C3 source carrier

Four new concrete source-aligned Agda owners are now linked from `BalabanRGTOERegression` (full audit in `Docs/physics/YMClayVoyagerCrossDomainSymmetryMaxCut20261101.md`): literal side-four C3 shifts/forward-bond path, group-valued loop naturality, `RationalUnitQuaternion` exact SU2 trace cyclicity/class-function invariance, and the `PeriodicBlock n=3` ↔ `Site4` bond graph pointwise codec. The positive-directed source signed-word holonomy and graph Wilson normalized real trace are same-object by finite induction, not merely two matching diagrams. Old `BalabanP33CMP109PeriodicPathHolonomyBridgeExact` independently verifies a signed-word/occurrence convention; it is imported as prior owner, not re-proved.

The exact remaining selected physical cuts are **inverse-edge extension**, **full closed plaquette action and C3 reindexing** on actual finite complete SU2/SU(N) group values, **product/constrained Haar change of variables**, actual **selected R443 finite action/Gibbs density**, **R445 preferred physical measure tail/convergence** and **R320/R333 same-H_OS spectral/UV–IR limit**. The existing R443→R431→normalized→continuum chain is already theorem-code; don't ask for another abstract facade. Rational unit quaternions need compact completion/Haar source and continuity, not categorical arithmetic promotion.

**Trust:** all new Agda is SOURCE-WRITTEN (not exact-head kernel-verified); no CI run.


### 2026-11-01 finite signed/native R443 symmetry closure

`YMClayNativeRationalSU2AllSignedC3WilsonExact.agda` closes the finite native
rational SU2 n=3 / side-four C3 graph-word transport for **both** positive
and inverse oriented links, using the actual existing path-holonomy/adjacency
operators. `YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact.agda`
then proves a four-axis-site and 4×4 **ordered** oriented Wilson plaquette
real-trace sum is C3 invariant, via rational exact finite reindexing.
This is genuine finite selected group-valued Wilson algebra, independent
of a jFine/Monster analogy.

Source-next exact leaves in ranked order:
1. **R443-six**: prove the 16 ordered plaquette sum reduces to exactly the
   source six `μ<ν` action with sign/inverse trace equality, diagonal
   constant and physical beta-normalisation; selected SU2 group values.
2. **R443-Haar**: literal 4D C3 configuration action preserves actual compact
   group product/constrained Haar integral (not merely rational point samples).
3. **R443-W/R445-T**: actual source physical Wilson/Gibbs action/density and
   preferred full measure/family attached to this same carrier with uniform
   bounded-observable tails; feed existing R443/R431/OS3 compiler.
4. **R320/R333**: real selected decay, OS Hilbert Hamiltonian and uniform
   positive gap after continuum/infinite-volume.
No Clay promotion. Exact-head Agda compilation remains outstanding.


The native six-positive-plane geometry and actual `Native.rationalSU2PlaquetteHolonomy`
are now directly reused by `YMClayNativeRationalSU2SixPlaneSameSourceExact`.
It proves source six-plane `Bond.plaquetteBoundaryDirections` equals our signed
ordered path, and source native group value/real trace equals the 16-term
subfamily on those exact 6 planes. The actual `sixPlanePhysicalTraceAction`
is thereby on the original named six-plane carrier. Independent exact Fraction
positive-six-plane sums remain -1108/25 before and after C3 on the tested
fixture, and its ordered action satisfies 2×six + 4×256 = 23384/25.

The *general Agda* six-vs-ordered identity (reverse orientation + diagonal +
2× multiplicity), full source action couplings, actual compact Haar, same
R443/R445 selected finite measure, and continuum R320/R333 remain genuine
open physical-source obligations. This six-plane file is source-written only.


The native norm-one rational SU2 four-factor reverse Wilson trace is now
source-written exactly in `YMClayNativeRationalSU2FourFactorReversalExact`,
reusing `Q.inverseProduct`, `Q.inverseInverse` on the original group
and `realPart(inv q)=realPart q`. The remaining six-plane cut narrows to
the **physical oriented contour evaluation/reindexing** and universal
16ordered↔6positive multiplicity and coupling norm; generic 4factor
group reversal itself no longer needs an arbitrary external assumption.

The literal native SU2 n=3 bond field <-> dependent positive-edge graph map now has **both** pointwise roundtrip theorems including arbitrary selected graph fields; no function extensionality nor off-carrier topology was used. Source-written, not kernel-verified.


### 2026-11-01 decisive max-cut recut — original six-plane C3 and native universe

**New actual-source lemmas on PR #1444 (source-written, Agda exact-head not run):**
1. Lower the *original* `RationalSU2BondData n` from an unnecessarily lifted `Set₁` to `Set`, consistent with its fields and with existing `RationalWilsonObservable n : Set` / physical finite `Configuration : Set`. This is a required typed bridge; check all importers on compilation.
2. `YMClayNativeSixPlaneC3SourceReductionExact.nativeSixC3Summed` reduces the **original six positive planes** to two concrete reversed orientations (21 and 31).
3. `YMClayNativeSixPlaneC3ActualPhysicalSourceExact.nativeSixPositiveWilsonActionSpatialC3` uses **existing** `pathHolonomyReverseOpposite` + `periodicPlaquetteClosure` and native trace inverse to pay both orientation cases and assert universally quantified native finite six-plane Wilson C3 invariance. No novel source axiom.
4. `YMClayR443NativeSixPlaneHaarNumeratorExact.nativeSixPlaneNumeratorC3Invariant` passes this same six-plane native finite action into the pre-existing R443 Gibbs/Haar and R431 numerator compilers, retaining only selected physical **Gibbs-density identification** and **compact product/constrained Haar C3 change-of-variables** as hypotheses.
5. `YMClayR443NativeSixPlaneC3SequenceLimitExact` compiles actual cutoff-indexed R431 numerator → normalized finite expectation → selected scalar-limit C3 invariance with **the same n=3 native configuration**; this does not manufacture a 4D continuum, which requires scale/refinement identification.
6. `YMClayR445NativeSU2R443SameObjectExact` proves definitional R443/R445 configuration identity, real native Wilson observable embedding and specializes the existing native P2 finite cylinder expectation convergence conditional on genuine preferred physical measure data.

**Re-ranked exact remaining mathematical max-cut, not to be conflated with the above:**
- **K0 compiler**: Agda exact-head kernel acceptance of native universe change and all 1 Nov modules/transitive safe imports; no claim until run.
- **R443-Haar**: an actual compact SU2/SUN product/constrained Haar C3 change-of-variables theorem, plus the **same finite Wilson/Gibbs physical measure/density**, coupling normalisation and full real-group identification. The rational quaternion finite source theorem is only a rational subcarrier; genuine compact SU2 Haar lives on its real completion.
- **R443-lattice**: selected UV-varying physical lattice, restriction/projection compatibility and actual original CMP119 nonlinear generated action: fixed n=3 finite side-four expectation sequences are not a continuum regularisation.
- **R445-T**: uniform-in-cutoff/volume physical bounded-observable tail and moment/coercivity-tightness estimates, selected limiting measure, plus continuum Wilson observable compatibility; R444 supplies moments only subject to its source hypotheses, not the tails.
- **R320-H1**: same original selected J-family marked second derivative exponential/rooted-shell estimate with volume/scale uniform constants, not the easy finite quaternion trace bound.
- **R333-H3/P3**: selected R281 physical decay spectrum equals the H2 OS reconstructed Hamiltonian, OS positivity/reflection, mass-gap lower bound independent of volume/lattice spacing, and infinite-volume/UV nontriviality. Claiming these from symmetry would be a Clay problem breakthrough not proved by the code.

**No Clay promotion.** Universal 16ordered↔6 constant relation still not kernel proved but **not needed for the now source-backed six-plane C3 route**.


### 2026-11-01 six-plane / 16-ordered physical Wilson normalization

`YMClayNativeSixPlaneOrderedIdentityExact` now source-writes a universal
same-original-n=3-carrier proof that `orderedTrace16 = 2*sixPositiveTrace+4`
at **every** side-four site: four diagonal `+a,+a,-a,-a` loops are
source-native prefix/reverse-opposite identities, six negative orientations
are the already-proved native inverse-path traces. Consequently the correct
physical Wilson action deficits satisfy
`orderedDeficit16 = 2*sixPositiveDeficit`. `Six.sixPlanePhysicalTraceAction`
is retained for the original six trace, while R443 source action is now
`SixOrdered.sixPhysicalDeficitAction = Σ_6(1−ReTr)`, with a direct finite C3
proof, leaving beta and original CMP119 effective Gibbs counterterms explicitly
unpaid. Independent exact arithmetic 4096 checks passes for the selected
fixture; kernel unverified.

Re-ranked residual: **Agda exact-head**, **actual physical R443 product/constrained
compact Haar and exact CMP119 finite Wilson Gibbs density with UV-varying source
family**, **R445 bounded tail/uniform volume tightness and physical continuum
expectations**, **R320 physical CMP116 marked-J source derivative decay**, and
**R333 same OS H2/H3 Hamiltonian, nontriviality and uniform physical gap**.
No other finite plane-counting or new C3/369 formalism is the mass-gap max-cut.


New exact native same-object owner `nativeR443SixDeficitR445Observable` proves the six-source Gibbs Wilson deficit is a R445 rational-observable *function* on the original `RationalSU2BondData 3`. It is not yet proved a physically bounded R445 input, and even such boundedness would not by itself imply convergent selected Gibbs expectations or a uniform physical continuum limit. **Next exact numerical lemma:** finite six-plane deficit majorant (at fixed side-four, ≤3072) from existing single plaquette trace bound and additive finite fold; then connect selected real/cutoff/volume weight and measure tail separately. Existing `NativeP2.nativeWilsonP2Limits` already handles products of individual loops under its actual measure hypotheses.


**Physical-carrier caution:** the exact native `RationalSU2BondData 3` record also stores an arbitrary `siteGauge` function. Its type equality across R443/R445 is genuine, but physical link-Haar requires an explicit pushforward/integration of this redundant gauge coordinate or direct link-only compact SU2/SUN configuration correspondence. The Wilson observable is gauge-field independent, the arbitrary physical integration field is not proven equivalent. Add **R443-linkHaar** to the source leaves along with actual compact completion/Haar and physical UV.


### 2026-11-02 source-first max-cut: selected CMP119 Gibbs numerator already owned

A new primary source readback audit `Docs/physics/YMClaySourceOwnerReuseAndProofGate20261102.md` establishes that `CMP119WilsonGibbsFiniteMeasureSameObjectExact` and `CMP119SelectedWilsonGibbsAnchorExact` **already construct** the source-selected CMP119 metric-insertion N/Z/DN/DZ Wilson–Gibbs finite numerator same-object theorem under their stated selected beta-driven density anchor and Wilson insertion. Do not duplicate these compilers. The next concrete leaf is the correct source proof that the chosen R443 actual compact SU2/SUN link-only Haar Gibbs configurations and varying cutoff family instantiate *those* original CMP119/R124 owners; the native side-four rational C3 module alone cannot pay that.

Likewise, pre-existing R445 selected marked moment and preferred diagonal producer structures do not imply the actual continuum tail, and R320 selected marked second source derivative and R333 same OS H3 Hamiltonian remain real theorem-bearing hypotheses, not syntactic construction tasks. All prior source-written new Agda remains exact-head kernel-unverified. Keep the max-cut list in the 2026-11-02 audit authoritative.


### Revived Yang–Mills audit / R443–R445–R320–R333 exact owner cut (2026-11-02)

The bounded source audit and exact remaining fields are recorded in [YMClaySUNMatrixR443R445R320R333MaxCut20261102](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-02-revived-thread-source-audit-executable-max-cut-and-non-promotion). The fixed rational SU(2) six-plane C3 deficit proof and conditional Haar numerator remain valid separately from the **selected** CMP119 N/Z/DN/DZ metric-insertion / R124 beta-flow family. Neither supplies the other's missing physical same-object witness. The concrete compact SU(N) trace/Haar + bond codec, selected Wilson-action and insertion equality, changing-lattice UV/IR estimates, literal selected CMP116 J-pair shell decay, and same-H OS uniform physical gap are **OPEN**. All new Agda source modules stay SOURCE-WRITTEN / NOT KERNEL-CHECKED. Golden source authority remains Agda; do not promote unverified Lean analogy or finite numerical tests. CI intentionally deferred.


### 2 November 2026 — full explicit source/PR search and finite R443 Haar-algebra payment

The prior broad 'Fubini, SU(N), CMP119, CMP116, mixed J, Hamiltonian, spectral gap, Haar, Wilson' search was repaired with indexed-file searches **and PR changed-file archaeology** (especially Agda #1444/#1440/#1049/#996/#967/#1231; Lean #7). See [the current max-cut source inventory](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#explicit-repo-and-pr-archaeology-and-new-finite-r443-implementation-2026-11-02).

**New source-written, not kernel checked:** `YMClayFiniteProductHaarOrderedAlgebraExact` derives N-link zero/add/scale/nonnegative integration by induction from the existing one-link algebra. `YMClaySUNMatrixProductHaarR443NumeratorExact` constructs the native finite Gibbs integration-law package and passes existing product-permutation C3 and action invariance through the original R443/R431 numerator theorem, without another global Haar or density-equality premise. Both are imported by `DASHI.Unified.BalabanRGTOERegression`.

**Unpaid physical max-cut:** (1) instantiate actual compact-real SU(N) normalized ReTr/N plus measurable selected one-link Haar/Fubini; note the existing `OneLinkProductHaar` type is total on all functions and must not be identified automatically with ordinary Haar; (2) construct the original side-four bond vector/C3 codec and source six-plane spatial action theorem; (3) identify the selected CMP119 R124 beta-flow and metric insertion, not just a fixed Wilson density; (4) provide actual all-n physical continuum measure/tails and cutoff compatibility; (5) selected CMP116 R320 mixed J rooted-shell inequality including physical source applicability; (6) H2/R281 same-H OS uniform spectral gap and nontriviality. Existing Lean PR #7 and Agda CMP116/CMP119 proof compilers must be reused without claiming their conditional hypotheses are paid. CI deferred; Agda kernel NOT RUN; Clay mass gap OPEN.


### 2 November 2026 — critical correction: Lean PR #15 already constructs compact finite Haar

[Exact Lean-PR-15 → golden Agda source map](../physics/YMClayLeanPR15FullPhysicalDonorCrosswalk20261102.md). Direct PR-head file reads recover real mathlib `literalSU2OneLinkHaar`, `literalSU2ProductLinkHaar`, `fourDimensionalNativeLinkHaar`, the exact product-identification theorem, and conditional selected CMP119 `ProbabilityMeasure`, Prokhorov, CMP116 mixed half-rate and OS spectral no-pollution machinery. Prior 'Haar entirely missing in repo' statements are inaccurate: **finite physical SU(2) Haar is source-written in Lean PR #15**. Golden Agda correspondence/selected measurable test class, original 1024-bond C3 codec and source R124 selection remain open. Do not call Lean PR-head theorem files Agda-kernel-accepted or pretend proof-bearing *transport* pays cutoff-uniform physical estimates.

The additional Agda strict-normalizer owners `productIntegralStrictlyPositive` and `nativePhysicalPartitionPositive` prove the finite Wilson–Gibbs partition is strictly positive conditional on the one-link strictly-positive integration law. The one-link source law remains explicit, not postulated in this module. R445 changing-lattice tightness, R320 selected actual CMP116 derivative, and R333 same-H physical continuum uniform gap are still unproved. No CI / kernel execution.

### 2026-11-02 — actual real SU(N) C3 site-Fubini theorem and finite Gibbs probability normalization

Added `YMClaySUNMatrixSpatialC3RealFubiniExact.agda`: instantiates the existing **polymorphic additive-monoid** `BalabanClayGate4FiniteWeightedAdjointFubiniExact.finiteFubini` at native real Wilson site sums. Two interchanges prove original side-four spatial C3 reindexing. This **derives global native real Wilson deficit/action C3 from a pointwise local six-plane C3 lemma**, rather than assuming global symmetry. In the R443/one-link Haar bridge, the former `sixPlaneActionC3` field is eliminated in favour of the strictly narrower `sixPlaneAtC3` original local physical trace equality.

Added exact native `normalizedExpectation` C3 symmetry, unit numerator = partition, and positive-partition + scalar self-division -> probability-normalized expectation of 1. Original R431 and `Finite.numeratorOneIsPartitionFunction` are reused, not replaced. All are source-written and re-exported through `DASHI.Unified.BalabanRGTOERegression`.

**Now highest-alpha finite R443 leaf:** instantiate local SU(N) inverse real-trace/oriented-plane identity (the rational quaternion source already supplies its geometric proof pattern), then construct exact original 1024-bond product-Haar codec and translate mathlib Lean PR #15's actual measurable compact Haar to golden Agda test algebra. This remains entirely separate from R445 continuum physical tightness, R320 selected differentiated CMP116 and R333 same-OS positive mass gap. See the updated physics ledger. No kernel execution/CI; no Clay promotion.

### 2026-11-02 — complete native SU(N) six-plane C3 proof reduction to matrix adjoint real trace

Source-wrote original SU(N) signed plaquette reversed-holonomy theorem with generic `pathHolonomyReverseOpposite`. Then established the full original six-positive-plane pointwise C3 permutation via real additive `sixRealC3Reindex` and exactly two reverse orientations; no new global C3 action assumption remains. `nativeC3BoundaryFromAdjointRealTrace` now constructs the actual R443 local boundary solely from the **matrix adjoint real trace law** and one-link ordered Haar laws. The new owners are `YMClaySUNMatrixNativeInversePlaquetteRealTraceExact` and `YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact`. Canonical Balaban TOE imports them.

**Unpaid R443 local scalar leaf:** instantiate concrete complex SU(N) matrices and the **ReTr_N(A†)=ReTr_N(A)** property of the selected normalized real matrix trace. Existing SUNMatrixRealTrace supplies cyclicity, not adjoint. Construct matching actual 1024-bond C3 codec and genuine measurable one-link SU(N) Haar/Fubini under the same source action. The earlier two-plane C3 source fields can be derived from this one matrix theorem; do not reintroduce them. R443 selected CMP119 metric source, R445 variable cutoff, R320 selected CMP116 mixed-J, R333 same-H mass gap/nontriviality remain open. No kernel or CI run.


### 2026-11-03 explicit all-gate archaeology and golden constructive complex trace / local-gauge Haar

The exact source list and new constructors are in [the canonical SU(N) physical cut](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-03-all-six-gate-source-search-constructive-trace--true-local-gauge-haar). Searches include every requested matrix/ReTr/dagger, Haar/Fubini, source E/R/B/V/CMP119, moment/tail/Prokhorov, mixed-J/R318/R320, and H2/OS/R333 spectral term; direct `dashi_lean4` PR #15 source verified genuine compact SU2 Haar translation and conditional moment Prokhorov.

**Paid source-written, not kernel checked**: `YMClayConstructedComplexFiniteAdjointTraceExact` derives `ReTr(A†) = ReTr(A)` for finite complex matrices *on the existing constructive-real carrier* by induction (with normalized trace and exact certified-SUN operator-correspondence adapter). `YMClaySUNProductHaarGaugeFromOneLinkExact` proves actual coordinatewise n-link gauge Haar from only one-link left/right Haar invariance. `YMClaySUNProductHaarNativeGaugeR443Exact` attaches this to the **original native SU(N) gauge action** and same literal finite Wilson/Gibbs R443 → R431 numerator/normalized expectation. Original global Wilson gauge theorem is reused. Physical integration laws were refactored to `nativePhysicalIntegrationLawsFromOneLink` and reused in both gauge and spatial C3 modules. All are imported by `DASHI.Unified.BalabanRGTOERegression`.

**Residual gates:** finite actual `CertifiedSUNMatrixTheory` over constructed complex matrices with ReTr/N and scalar alignment to legacy `ℝ`; selected measurable one-link compact Haar/Fubini and strict positivity; native original 1024-link C3/vector/gauge codec; CMP119 *source-selected* R124 E/R/B/V metric insertion/beta/counterterms (the `CanonicalWilsonGibbsMetricFamilyWeldCompilerExact` already compiles the family from the selected source equality); R445 selected marked moment realization, bounded-observable tail and source compact-containment, variable-cutoff cylinder maps; R320 exact selected J domain/source magnitude and CMP116 rooted-shell envelope; R333 real selected CMP119 H2 OS and spectral no-subgap positive uniform gap/H6. CI deferred. **No kernel acceptance or Clay proof claimed.**


### 2026-11-03 — repaired bond-field extensionality and native Bishop matrix-trace donor

`YMClaySUNNativeWilsonBondPointwiseExact` and `YMClaySUNVariablePeriodicBondPointwiseExact` prove original actual SU(N) signed paths, positive plaquettes, six-plane actions and Gibbs densities respect **pointwise** bond equality (the latter at every original periodic cutoff), without an unrestricted function-extensionality assumption. `YMClaySUNNativeSetoidBondProductHaarExact` supplies an alternate **setoid** original bond/Vec codec and proves selected-observable C3 product Haar, including the actual native Wilson and Gibbs observables, conditional only on constructing the native codec and one-link Haar law. It does **not** equate arbitrary functions or replace the stronger original two-sided codec. All are imported in the Balaban TOE spine.

Source searches also recovered the concrete vendored Bishop backend and `BishopSetoidComplexExact`. New `YMClayBishopSetoidFiniteAdjointTraceExact` proves finite complex-matrix `ReTr(A†) ≃ ReTr(A)` and normalized analogue by real-setoid congruence, directly on the ACTUAL Bishop source. This cannot be promoted to legacy `RealAnalysisAxioms.ℝ` / Agda propositional equality; `CanonicalDASHIRealBackendExact.LegacyFacadeMigration` explicitly records that pending equivalence/audit. Continue from same-carrier Bishop setoid SU2/complex matrix and selected test-Haar construction; do not reinvent abstract `SUNWilsonAction` or compact-Prokhorov/OS compilers.

See [full gate-ordered ledger](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-03-late-max-cut-original-bond-function-setoid-every-cutoff-vendored-bishop-real-trace). Concrete complex SU(N) unitary/determinant, normalized trace/cyclic laws, actually selected measurable one-link Haar and 1024-bond setoid codec remain physical source obligations. R124 CMP119, R445 estimates, R320 selected-J decay, R333 real same-H gap and nontriviality remain OPEN. Source-written Agda, NOT kernel accepted.


### 2026-11-04 source-selected R445 same-measure pushforward cylinder theorem

The current selected #1444 R445 bridge has two new OWNED source-written lemmas: `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact` constructs the actual original side-four SU(N) finite-Gibbs weighted blocked-cylinder functional and derives positivity, linearity, correct original partition-normalization and selected coarse Wilson/Gibbs gauge laws from existing `PhysicalFiniteMeasureIntegrationLaws`. `YMClayFiniteRGPushforwardNonBareWitnessSafeExact` proves an independent finite fibre-multiplicity no-go to automatic bare coarse uniform weight. Its 64-state Q8-subgroup comparison checked 4,096 gauge transformations and the exact density mismatch in a toy finite model, **not** the physical selected SU(N) Wilson Gibbs law. Full details: [source and exact gate ledger](../physics/YMClaySUNMatrixR443R445R320R333MaxCut20261102.md#2026-11-04--r445-original-physical-blocked-cylinder-pushforward-max-cut-source-written-not-kernel-checked).

**Remaining SOURCE→PHYSICAL gap:** show that this selected fine pushforward has a measurable coarse Haar Radon–Nikodym density/effective action, physical normalized disintegration and source-compatible RP cylinder transport, with actual beta(a), tightness/UV/IR uniform estimates and same physical source choice. Do not claim it is another bare Wilson weight; downstream R320 mixed-J, R333 same-H OS strictly positive gap/H6 and full Clay R⁴ remain open. Agda kernel/transitive postulate audit pending. Original 219 field inventory retained.


### 2026-11-17 YM.REAL rational S3 maximum cut: root/pi-free original source

SOURCE-FIRST: original rational SU2 carrier, finite positive-bond
enumerator, positive reciprocal, original finite RG pushforward/
disintegration and side-four blocked Gibbs pushforward are already
in repo. Do not duplicate these theorem owners.

The earlier concern about unavailable arbitrary Bishop square roots
or identifying Machin pi with the classical trigonometric period is
NOT a prerequisite for exact positive rational S3 cubature:
- YMClayRationalS3StereographicNodeExact constructs the Pythagorean
  identity for q(t)=((1-|t|²)/d,2t/d), d=1+|t|².
- YMClayRationalS3StereographicConcreteExact proves d>0, inverts
  it using the existing rational reciprocal and constructs the
  ORIGINAL RationalUnitQuaternion (no assumed norm witness).
- YMClayRationalS3PositiveWeightedNodesExact constructs strictly
  positive rational J(t)=(1+|t|²)^-3 weights, nonempty positive
  total, exact normalized mass one and original-to-Bishop SU2
  unitary source reuse (transitive kernel acceptance pending).

Four fully rational positive exact orbit cubatures are certified:
  d=7  : 120 original rational sphere nodes, 330/330 monomials;
  d=9  : 360 nodes, 715/715 monomials;
  d=11 : 696 nodes, 1365/1365 monomials;
  d=13 : 1000 nodes, 2380/2380 monomials.
Total 4840 exact rational assertions; no pi, roots, floating-point
or numerical optimizer in the committed certificate. The degree-7
rule uses positive orbit masses 167/960, 1/15, 243/320.
Its tensor product integrates the actual L=1 Wilson six-commutator
cubic 20,502-term polynomial and confirms H(D³)=6445/48
independently of the original Pochhammer-moment calculator.

All-degree MATHEMATICAL proof route: positive full-support
stereographic rational area J=8/(1+|t|²)^3; exact rational
divergence-free SO4 generator identities and integration by
parts derive all Pochhammer moments. Finite-dimensional rational
moment vector is interior to convex hull of rational sphere
evaluations; rational convex feasibility proves existence of
positive exact rational cubature at each degree. Effective
finite-dimensional Gram coercivity can certify a search margin:
lambda >= det(G_d)/tr(G_d)^(dimension-1). Rational LDL examples
through degree 3 are verified. This is NOT yet an inhabited Agda
termination/search proof for arbitrary d.

A second completely root-free Bishop route uses rational
stereographic MIDPOINT sums. For |f|<=B and L-Lipschitz on
the S3 chord, choose C=ceil(1+B+L), R_k=2^(k+16) C,
h_k=R_k^-5; exact rational midpoint and tail bounds give
normalized error <=2^(-k-3). This supplies an explicit
fast-Cauchy precision schedule, but native Bishop order,
multivariate midpoint integration and the vendor Sequence Cauchy
inhabitant are still unproved in Agda.

Existing original FiniteRG pushforward/disintegration is reused.
Naive same-beta L2-to-L1 link selection is false; the correct
RG blocking/induced effective action must be instantiated with the
original rational-design Wilson Gibbs source.

**Do not close YM.REAL:** exact mathematical all-degree rational
existence and finite certificates are much stronger, but the
all-degree constructive Agda producer, actual native Bishop
completion, original SUN matrix equivalence, and typed original
Wilson/RG cylinder weld still require kernel acceptance.
New source ledger: Docs/physics/YMClayRationalS3HaarNoRootsMaxCut20261117.md.


### 2026-11-17 continuation: compressed degree-13 source certificate and new degree-15 rational Wilson endpoint

**New exact mathematical/algorithmic result:** signed-coordinate and
permutation invariance reduces every polynomial of degree <=13 on S3
to nine elementary symmetric constraints in yi=qi²:
1, e2, e3, e4, e2², e2e3, e2³, e3², e2e4, using e1=1.
The independent exact SymPy checker
scripts/check_ym_s3_degree13_nine_invariants_20261117.py
checks all nine weighted rational moments of the nine existing
rational-orbit representatives and all symmetrized monomial orbits
through y-degree 6. The full 2380-monomial checker remains an
independent control. The new safe-source Agda
YMClayRationalS3DegreeThirteenInvariantCertificateExact
uses nine ACTUAL original RationalUnitQuaternion constructors and
rational masses, with nine closed invariant arithmetic equations.
This is NOT an Agda theorem formalizing the Reynolds
sign/permutation symmetrization and basis spanning step.
No pinned Agda kernel was available.

**New degree-15 positive rational cubature:** a rational linear LP
search over 20 low-denominator rational signed/permutation orbits
found eleven positive orbit masses. They were reconstructed with an
exact rational linear solve; the static certificate itself uses no
LP, floats, roots, angles, pi, or square roots.
scripts/check_ym_s3_exact_rational_orbit_degree15_20261117.py
independently verified **3876/3876** full monomials, strict positive
masses, exact unit norm and mass-one normalization.
The fully expanded signed/permutation cubature has **1464 nodes**.
The first 11 invariant constraints in yi of weighted degree <=7
are 1, e2, e3, e4, e2², e2e3, e3², e2e4, e2³,
e3e4, e2²e3. Numerical discovery is not proof;
the committed rational certificate is the exact proof witness.

**Concrete original Wilson finite-volume consequence.**
A positive exact degree-15 rule in EACH original link integrates
the actual polynomial Taylor series through degree 15 at all
original periodic sides L>=2, since each elementary plaquette
contains any one original positive bond at most once. The L=1
commutator reuses each of two bonds twice, so degree 15
integrates through Taylor order 7. In both cases the alternating
Taylor bounds are genuinely valid for ALL beta>=0.
At beta=1/(96 L⁴), the guaranteed interval width is
1/10569646080 at L=1 (T7/T6), and
1/46009701534740225458176000 at L>=2 (T15/T14).
scripts/check_ym_original_wilson_rational_degree15_taylor_budget_20261117.py
checks exact original edge incidence through L=4 and these
factorial interval bounds. **The high-order endpoint integrals
have not been expanded or evaluated**; the interval-width result
does not claim an actual numerical partition value.

**Trust:** these exact rational cubature witnesses substantially
advance the physical polynomial cylinder, but do not inhabit
the Bishop all-degree cubature/Cauchy/continuous-Haar source,
the original full SUN matrix equivalence, or the selected RG
disintegration bridge. No transitive Agda acceptance receipt,
no mass-gap/continuum claim. Maintain YM.REAL OPEN.


### 17 November 2026 — next implementation: degree-15 11-invariant source weld

New finite original-SU2 source proof candidates, committed to PR #1444:

- DASHI/Physics/YangMills/YMClayRationalS3DegreeFifteenInvariantCertificateExact.agda
  reuses the original rational quaternion constructor and the prior
  degree-13 invariant functions. Its 11 rational representatives
  have norm-one closed polynomial witnesses, and it writes the exact
  11 invariant moment equations as definitional rational arithmetic.
  Tagged --safe but no pinned Agda/CI kernel result exists.
- scripts/check_ym_s3_degree15_eleven_invariants_20261117.py
  checks each invariant by independent exact methods: evaluate positive
  rational orbit masses and expand into Pochhammer coordinate moments.
  It verifies all 38 distinct signed-permutation orbit-sum monomials of
  squared-coordinate degree <=7 reduce (using e1=1 on S3) into
  the explicitly listed 11-dimensional invariant span.
  Locally 11/11 moments and 38/38 orbit classes passed.
- The independent scripts/check_ym_s3_exact_rational_orbit_degree15_20261117.py
  passes 3876/3876 monomials on the 1464-node rational rule.
  The original Wilson T15/T7 degree budget remains a bound, not
  evaluated high-order Taylor partition coefficients.

Exact source moment targets:
1=1; e2=1/4; e3=1/48; e4=1/1920;
e2^2=11/160; e2*e3=1/160; e3^2=3/4480;
e2*e4=3/17920; e2^3=89/4480;
e3*e4=3/143360; e2^2*e3=69/35840.

NEXT KERNEL CUT: formalize in Agda the actual signed/permutation orbit
averaging and its action on every coordinate monomial through degree
15, then the invariant-basis reduction and the uniform positive
finite orbit weights. A sum over one representative per orbit is
NOT the actual full signed-permutation orbit measure.

ORIGINAL WILSON/RG: reuse existing
YMClayFiniteRGExistingPushPullReopeningWeldExact and
BalabanFiniteProbabilityPartitionDisintegrationExact, rather than
rebuilding finite disintegration. Instantiate them on the actual
rational-design original SU2 link product Gibbs measure and the
original selected block map, verify positive selected coarse fibres
or remove zero-mass fibres, then bridge to the actual Bishop limit
and original SUN matrix carrier. The RealAnalysisAxioms.ℝ legacy
carrier remains different from Bishop Real.ℝ.

Remaining YM.REAL formal obligations OPEN: universal constructive
positive rational design search termination, native Bishop
multivariate order/Cauchy proof, completed actual SU2 Haar
bilateral invariance, pinned original SU(N) carrier mapping,
original Wilson finite product and selected physical RG transfer.
No pinned Agda kernel acceptance is claimed.


### 2026-11-17 continuation: closed 24-cell original finite Wilson/RG

NEW SOURCE FINDING: The rational 24-cell one-link degree-five
cubature is closed under actual quaternion multiplication and
conjugation. It is the 24-element binary tetrahedral subgroup.
The constructed exact 24x24 multiplication table verifies
closure, identity, inverses, and all 24^3=13824 associativity
instances. Every left and right translation permutes the 24
nodes, giving exact uniform bi-invariance on this finite subgroup.

New Agda candidate:
DASHI/Physics/YangMills/YMClayOriginalRationalWilsonTaylor2PositiveExact.agda.
Uses prior original rational square positivity, rational ring
identities and strict rational products to derive, without a
positive-density assumption,

   T2(S) = 1-S+S²/2 = (1+(1-S)²)/2 > 0

for ANY rational action S. It deliberately makes no --safe
transitive claim, since the original positivity imports are non-safe.

New exact original Wilson finite RG checker:
scripts/check_ym_original_L1_24cell_group_rg_20261117.py.
It builds the true original L=1 4-link/6-positive-plane
quaternion commutator action on all 24^4=331776 fine states.
At beta=1/96 it assigns strictly positive rational quadratic
Taylor Gibbs weights and pushes them forward through the
ACTUAL noncommutative block B(U)=U0*U1. The coarse image is
exactly the same 24-element rational SU2 subgroup, with 24^3
fine configurations per coarse state. All coarse masses are
strictly positive and normalized; direct and blocked weighted
expectations are exactly equal. It recovers
  H(D)=9/2; H(D²)=187/8;
  Z_(L1,T2)=140731/147456;
  E_(T2)(Re(U0 U1))=0.
Exact quotient checks total 346302, including the complete
degree-five Pochhammer monomial basis and 24^3 associativity
tests. All arithmetic is rational; no Monte Carlo, pi or sqrt.

This is a real finite original-source noncommutative RG
PUSHFORWARD of a positive polynomial Gibbs measure. It is
NOT the full exponential Wilson measure, the continuous
SU2 Haar, the original Agda RG-record instantiation or a
continuum/Clay result. The finite 24-cell integrates linkwise
polynomial observables through degree five, but does not
provide exactness for all analytic observables.

Next kernel cut: construct the literal original RationalUnitQuaternion
24x24 Cayley table and full finite carrier, instantiate the
EXISTING BalabanFiniteProbabilityPartitionDisintegrationExact
and YMClayFiniteRGExistingPushPullReopeningWeldExact owners
with its positive T2 fine weights and block projection,
and prove consistency with the actual Bishop/continuous Haar
polynomial limit and original SUN matrix-carrier identity.
All-degree Bishop, full exponential and RG source welds OPEN.
Agda/Nix are unavailable here, so no kernel acceptance is claimed.


### 2026-11-17 finite original Wilson RG: explicit induced effective action

This continuation goes BEYOND a generic pushforward existence statement.
The original L=1 24cell rational subgroup has exact 24x24
noncommutative multiplication, uniform finite one-link Haar and
complete degree<=5 S3 monomial moments. Tensor its 24 nodes over
the original four positive links, enumerate ALL 24^4=331776 true
six-commutator fine configurations, and use the provably positive
rational Gibbs Taylor polynomial
  T2(beta D)=1-beta D+(beta D)^2/2 > 0, beta=1/96.
The actual selected noncommutative block is B=U0*U1 and lies
inside the SAME original rational 24cell subgroup.

NEW exact CONDITIONAL moment identities: with t=(Re B)^2,

  E[D | B]   = 19/4 - t
  E[D^2 | B] = 4t^2/3 - 169t/18 + 230/9.

The actual induced effective coarse density relative to the
uniform 24-cell law is therefore

  W_beta(t) = 1 - beta*(19/4-t)
             + beta^2/2*(4t^2/3-169t/18+230/9).

Three exact trace-square coarse classes exist:
  t=0   : 6 states, W=78955/82944;
  t=1/4 : 16 states, W=422191/442368;
  t=1   : 2 states, W=35459/36864.

Their positive mass average is exactly
  Z_(L1,T2)=(6 W0 +16 W1/4 +2 W1)/24=140731/147456.
The normalized pushforward law has coarse mass W_beta(t)/(24 Z),
and exact blocked real trace expectation zero. Conditional coarse
fibre counts are 24^3; finite positive disintegration is exact.
This is NOT a fake renormalized same-beta Wilson action; it is the
explicitly INDUCED coarse density.

Executable sources:
- scripts/check_ym_original_L1_24cell_group_rg_20261117.py
  (346302 exact group/Wilson/pushforward assertions);
- scripts/check_ym_original_L1_24cell_induced_rg_20261117.py
  (full 331776-state conditional moment enumeration and class checks).

Kernel-facing algebraic source:
DASHI/Physics/YangMills/YMClayOriginalL1Rational24CellEffectiveRGExact.agda,
a --safe CANDIDATE carrying the actual three-class rational weights,
closed exact rational positivity, and Z equality. This does NOT yet
prove the original group conditional moment formulas in Agda, nor
inhabit the previous finite partition/disintegration owner from the
24^4 literal group table. No pinned Agda/CI receipt is available.

This closes a concrete original finite-quadratic-Taylor RG
MATHEMATICAL subproblem. It DOES NOT prove the full exponential
Wilson coarse effective action, native Bishop all-degree/limit
functional, same-original SUN source equivalence, 4D continuum
Yang-Mills or Clay mass gap. Those remain OPEN.


### 2026-11-17 additional Agda B4 source: original rational SU2 orbit generators

New --safe SOURCE WRITTEN (not kernel-accepted):
DASHI/Physics/YangMills/YMClayOriginalRationalS3HyperoctahedralGeneratorsExact.agda.
It reuses the ORIGINAL rational SU2 quaternion record and previous
e2/e3/e4 source owners. Four coordinate sign flips and adjacent
swaps 01/12/23 are actual functions on the original unit quaternion,
with the unit norm proved from source polynomial norm equality.
The four invariants norm, e2, e3, e4 are proved invariant
for each generator using exact rational ring equations, not
just a numerical sample. It imports only the source-safe original
quaternion and invariant owners and is attached to the canonical
BalabanRGTOERegression safe-graph and local preflight.

Independent exact symbolic source check:
scripts/check_ym_original_rational_s3_b4_invariants_20261117.py
passed 32/32 polynomial identities.

NEXT exact Agda theorem for degree-15:
1. Define/reuse the complete orbit enumeration of the B4 generator
   action and prove signed-odd cancellation / uniform orbit
   reindexing on the 1464-node rational design, not just the
   representative-to-invariants map.
2. Formalize the fundamental theorem of symmetric polynomials
   specialized to four squared coordinates and e1=1 on the
   original rational S3; derive the 11-dimensional degree-15
   monomial normal form.
3. Compose these with the already source-written 11 exact rational
   moments of YMClayRationalS3DegreeFifteenInvariantCertificateExact.

This is one formal finite exact cubature target, not an assumed
Bishop continuous Haar or universal arbitrary-degree theorem.
The all-degree rational convex-interior producer and native
Bishop fast-Cauchy witness remain OPEN. Pinned Agda/Nix
kernel acceptance was not available.


### 2026-11-18 finite S3 Reynolds averaging: arbitrary-degree signed-orbit cancellation

New source owner:
DASHI/Physics/YangMills/YMClayRationalS3OddSignOrbitCancellationExact.agda
(a safe-source candidate). It proves by Nat induction that the
rational even-power operation is invariant under x to -x, the
odd-power operation changes sign, and every pair f(x)+f(-x)
vanishes for an odd function. It then enumerates the actual
sixteen sign choices as a MULTISET (important when a rational
coordinate is zero) and proves the sum vanishes whenever the
first coordinate exponent is odd.
There is NO degree cutoff, implicit Haar positivity input,
square root, pi or abstract cubature-exactness field.

Independent checker:
scripts/check_ym_s3_sign_orbit_universal_parity_20261118.py
passed 16384/16384 exact fraction checks for all exponent
vectors in {0,...,7}^4 at four rational coordinate vectors,
including zeros and non-unit inputs as a robustness control.
The source theorem is universal over rational inputs, not
derived from these finite examples.

The first-coordinate theorem can be extended to oddness at
any coordinate by the existing original B4 adjacent-swap
generators. The remaining Agda lemma must establish that
the full 16-signed multiset sum is invariant under swaps
(including stabilizers/duplicates), then combine that with
the existing degree-15 eleven-invariant source equations
and a constructive four-variable elementary symmetric
basis reduction.

Current five-gate status:
- All-degree rational cubature: universal odd-sign
  cancellation source added; all-degree positive rational
  design termination, complete permutation averaging
  and symmetric basis remain OPEN.
- Effective b_n and Bishop: native modulus/order and full
  _isCauchy witness remain OPEN; rational schedules alone
  are not native proof objects.
- Haar: full two-sided Bishop invariant limit and positivity
  completion remain OPEN.
- SU2 matrix: original rational-to-Bishop source written;
  kernel acceptance/full selected SUN identity OPEN.
- Wilson/RG: actual positive L1 quadratic-Taylor finite
  coarse law and 24^4 certificate stand; kernel
  instantiation and full exponential/physical cross-cutoff
  transfer OPEN.

No pinned Agda/Nix toolchain or CI acceptance was available.
Do not mark YM.REAL closed on SymPy or a source pragma alone.


## 20 November 2026 — current #1444 implementation and manuscript crosswalk

Source baseline: `33a87830df1dbc64fef7689d93150de54d602fcd`.
Rounds R are chronological iterations; reuse later concrete producers before
reopening an older obligation. The following are committed source changes,
not new kernel acceptance receipts.

| Work | Commit / source | Status |
| --- | --- | --- |
| Root-free SU2 dexp and exact rational reference | d182ad5, scripts/check_ym_path13_dexp_20261120.py | Prior reported SymPy execution; no Agda proof |
| Same two-carrier Eq119/Eq120 | 761cdba, 88daca8 | Source-written |
| Native Bishop Lie coordinates and signed path source | 9ee4f5a | Source-written |
| Reused Bishop reduced polynomial, physical factor two | 1785cf2 | Source-written |
| Direct variational selection, canonical geometry; no legacy chart input | 16924e8 | Source-written |
| Inhabited canonical radius-six walk certificate attached | 9af3446 | Source-written; no independent geometry input |
| Configured P33 bordered trace, moving normal constraint and measure distinction | bdbffd9, a3b5d9a; scripts/check_ym_p33_bordered_trace_20261120.py | Prior exact rational execution; not physical CMP109 beta |

| Root-free scaled inverse and positivity | cb0f8f9, 1252e6f, 3ce4195 | Source-written, kernel pending |
| Actual Bishop factorial/arcsinc series and bounds | 16ca148, de796db | Source-written, kernel pending |
| Constructed native LocalChart | 14fd22f, 7941c56, 33a8783 | Source-written and attached to focused regression; admission and semantic identity remain |
| Root-free chart exact executable checks | 854c1d3, scripts/check_ym_path13_rootfree_chart.py | Symbolic two-sided inverse and 16 rational contour certificates |
| Delta/pivot determinant and mixed jet | 576daf3, scripts/check_ym_cmp109_delta_pivot_measure.py | Exact rational checks; literal CMP109 normalization not yet identified |
| Full selected Path13 mixed jet | 4ea9811 | Exact local execution: 114244 contour projections |
| Full finite Q matrix and pivot/Gram jets | 6f69482 | Exact local execution: 12 x 342732, four jets, flat reference |
| Squared-chord path and direct contour admission | 10e2a4a, 066d5cf, 812e06a, f2bf18a, 4de7e33 | Source-written; consumes selected inverse-link radius, no independent norm representation |
| Bishop arcsinc positive upper bound | 80fb1ae, 915f147 | Source-written; kernel pending |
| Chart semantics and nontrivial commuting flat minimum | 38f9852 | Symbolic identities and exact rational fixture executed |
| Paper 3 source semantics and matrix receipts | 9612990 | Mathematical derivation in section 5.5; explicit claim boundaries |
| Full side-13 Wilson+covariant divergence Hessian and Green | 00e7d64 | Executed 84 stencil blocks, exact flat reduction and all 28561 Green equations; 326-bit denominator |
| Full finite exact bordered Gaussian | 277cf8d | Executed all 165 displacement pairs and two Q cross-contractions via signed CRT |
| Point/outer chart admission from chosen physical radius | fd89a34, 93919ea, b90e58d, 56519c7 | Source-written, pinned Bishop API checked statically; kernel pending |
| Actual multi-block flat pivot/Gram/propagator | 42a688f, caa29fc | Exact counts and finite cyclic tests; mathematical all-volume floor; source-written cyclic Gram proof |
| Rational near-identity root obstruction | 42b869e | Exact constant-sector counterexample, not general rational minimizer no-go |
| Paper 3 full finite trace and multiblock proof | d22154d | Section 5.6, all mathematical and executed claims scoped |

### Current execution cut (supersedes older packet lists; not new gate IDs)

The active local cut is the **four remaining Path13/CMP109 attachments**, not
a request to reconstruct the downstream RG, clustering and OS mathematics.
The distinction between an existing theorem/compiler and its application to
the selected original physical family is essential. R numbers are dates/order
of research iterations, not independent theorem authorities.

**Already constructed / reuse first:**
- Native Bishop real backend, rational coordinate embedding, signed bond
  projection, literal quaternion adjoint action, physical factor-two
  bracket, reduced polynomial operations, and Eq119/Eq120 on the same
  two-carrier source (`BalabanCMP98Path13BishopNativeSourceExact`).
- **Radius-six walk agreement is inhabited**:
  `BalabanPath13RadiusSixWalkAgreementExact.radiusSixWalkAgreement`.
  Commit 9af34466bb2689f4f6c05ca92563060bdc76e642 attaches it directly;
  no per-bond embedding or walk-certificate input is outstanding.
- Direct selection from the variational theorem and canonical geometry
  are implemented; no independent selected-background equality or legacy
  real principal-chart record is needed on the native route.
- Existing Bishop coefficient modulus and ad-polynomial telescope, finite
  Wilson 64-atom mixed jet, left/right trivialization, CMP99 pivot algebra,
  restricted trace cancellation, positive-patch arithmetic and finite
  remainder absorption are reusable. See `BalabanCMP109DirectBetaSourceRegression`.
- Existing downstream RG/moment/clustering/OS compilers are not fresh
  mathematical tasks merely because their inputs are conditional.

| Remaining local attachment | Exact acceptance test |
| --- | --- |
| A. Native chart | nativeInputsFromPhysicalRadius now constructs pointLogAdmissible, pointRelevant and outerRelevant on the same native series chart. Bishop square-reflection and normalized sum donors reused; API order transports corrected. Complete native exp/log/Fréchet identification and verify pinned Agda. No independent admission input. |
| B. Physical variational input | Nontrivial rational commuting flat fixture and exact near-identity rational 13th-root obstruction. General selected real-carrier variational theorem, actual action/constraint/gauge and physical radius remain. Reuse Bałaban; do not assert general rational minimizers, or promote the constant-sector obstruction to a general no-go. |
| C. Source-normalized restricted Gaussian | Full Q and chosen six-plane Wilson+covariant-divergence Hessian mixed jets, all finite delta trace terms computed exactly (CRT). Multiblock flat pivot and Green fiber inverse implemented. Attach actual selected minimizer derivatives, full printed A/H1/J and additional CMP109 measure density; a one-block trace is not the physical beta. |
| D. Uniform physical beta | All-volume flat Q0 Gram floor 57/13^6 (57/169 preconditioned), ker Q0 Hessian floor 1/57, with source-written cyclic Gram and exact stencil counts. Use existing patch/remainder and source-specific selected perturbation control, actual coarse momentum/normalization and uniform physical beta enclosure. No interacting beta claim. |

For A, the implemented root-free construction is A(w), B(w) factorial series, w=4||Y||²,
and positive-scalar quaternion log via the arcsin(r)/r series in r².
With h=1-wB, Delta=h²+wA² the inverse is
J=I-(A/Delta)ad+((A²-hB)/Delta)ad²; on 0≤w≤1/4 the mathematical lower
bound is Delta≥529/576. The coefficient convergence, interlacing and inverse cancellation are now
source-written using the existing Bishop limits; do not re-open them absent
a kernel failure. The executable rational certificates are not kernel receipts.
Do not impose global inverse-dexp or a decidable Bishop-real zero split.

For B, reuse the direct 74-link telescope (37/1024 threshold) wherever
its defect normalization matches the actual source. Squared chord and
operator norm are different quantities; do not equate them by notation.
For C, the new determinant reduction gives ordinary delta pivot density
1/|det P| and (-1)^m det bordered(A,Q)=(det P)^2 det(C*AC).
Induced volume differs by sqrt(det(QQ^T)); the exact mixed jets are tested.
Attach actual CMP109 normalization and any additional density before using
these results in the physical beta floor. For D, use finite active-scale history, not an all-Nat
positive-beta recurrence.


Current exact arithmetic executed receipt (one-block, chosen background paths, no physical beta):

```
Green denominator bits = 326; all 28561 equations PASS
exact finite 2 Gamma_st delta = 216322732729731037306399416467101947565702264504255432442831129938831157590086114944025745589515026330695342921918722859720533813302962357884707554671488525967748893665917497385415791464168273322246877/40831355640469077924296754159149697139903068972616389940473557569519290498175868526730955293070750301779577272128081390546952400138950539138107665343598731913478057839270326725044030505628195025
approx delta = 5297956.174527001
induced correction = -3328816224672/815730721
approx induced = 5293875.396227281
```

The exact trace scripts have byte-identical local and repository blobs
(bbef5abc0ee2b7c3504c444b6f5e191787729220;
f7fb2c9d8e9fe4a8b3028d442f94fd7f8329de0b). The finite multi-block flat
operator is the true two-box stencil, not merely the one-block constant
row. Agda and Nix were unavailable; no kernel or CI result is claimed.

### Downstream integration and endpoint acceptance (not additional local packets)

Use the current R578 source-native route:
R566/R568 selected projective Wilson projection and path factorization;
R545 finite OS source; R559/R560 CMP119 moments to OS05;
R576 original Wilson WEXT; R577 same reconstructed-H transfer;
R571 compact-simple source; R563 same-family Ward kernel.
The direct R333 route in `YMClayDirectSourceOSMassGapFrontierExact`
already composes H1/R295/R313/R296 with physical OS transfer.
The stronger historical F1/F3/F4/Mosco/trace-norm route is not mandatory.
Do not schedule it as another prerequisite.

After A–D, run the existing downstream consumers on the same original
family and inspect their actual remaining typed inputs; reuse any later
inhabitants before scheduling new proofs. This is an integration/acceptance
checkpoint, not evidence that A–D alone imply every downstream hypothesis,
nor a claim that all downstream physical inputs are absent. No exhaustive
cross-branch inhabitant audit has been completed.

Authoritative Clay endpoint IDs E1.01–07, D1.01–04, D2.01–05, N1.01–03,
G1.01–04 remain acceptance criteria, not a count of independent new tasks.
No new complete physical endpoint or exact-head Agda acceptance has been
observed. Keep mathematical status, source implementation, same-object
attachment and kernel certification separate. Local Agda is golden;
SymPy is supplemental executable verification where Agda is unavailable.

### Existing manuscript corpus (verified on this branch)

The original eight lanes and Paper 0 are retained. The publication router
is [PublicationRoadmap](../papers/PublicationRoadmap.md); the active
manuscripts are Paper 3 (first priority), Paper 1, and Paper 8. The remaining
old lanes are legacy/support, not deleted. Do not create replacement drafts.

- [Paper 0 — Shared Margin Grammar](../papers/legacy/Paper0SubmissionDraft.md)
- [Paper 1 — Navier–Stokes](../papers/live/Paper1NavierStokesClayDraft.md)
- [Paper 2 — GR geometry](../papers/legacy/Paper2GRGeometryDraft.md)
- [Paper 3 — literal Wilson mass-gap reduction](../papers/live/Paper3YangMillsClayDraft.md)
- [Paper 4 — Physical Hilbert space](../papers/legacy/Paper4PhysicalHilbertSkeleton.md)
- [Paper 5 — DHR](../papers/legacy/Paper5DHRSkeleton.md)
- [Paper 6 — Yukawa/CKM](../papers/legacy/Paper6MatterYukawaCKMSkeleton.md)
- [Paper 7 — Terminal composition](../papers/legacy/Paper7TerminalCompositionDraft.md)
- [Paper 8 — Unification](../papers/live/Paper8UnificationDraft.md)
- [Paper 3 finite geometry draft](../papers/drafts/Paper3YangMillsGeometryDraft.md)
- [Eriksson–Balaban source intake audit](../papers/drafts/YangMillsClayTrackAuditManuscript.md)
  ([TeX](../papers/drafts/YangMillsClayTrackAuditManuscript.tex))
- [YM / Unification theorem navigation](../support/reference/YMUnificationPaperToProofMap.md)

The active Paper 3 at d22154d supersedes its older local task list; Sections 5.5–5.6 record the full finite Q, exact bordered trace, source-semantic chart and physical multi-block flat base.
The older source intake manuscript's P33-closed label is scoped to its
historical reduction, not the current physical beta or Clay endpoint.


### 2026-11-20 — CMP102 constructor-first root-free boundary reconstruction

Mandatory attribution rule: on apparent errors, audit actual constructor, carrier,
coordinate normalization, multiplication order, path endpoints, scale and gauge
anchors before changing equations, shrinking radii or adding hypotheses.
Separate algebraic, analytic, geometric and physical acceptance.

At d88d709c the native CMP98 Path13 owner exposes outerY and nativeInputsFromPhysicalRadius,
with SmallLie giving 0 <= w = 4||Y||² <= 1/4 for the native series chart.
The quaternion exponential uses s = ||Y||², not the adjoint radius w.
BalabanCMP98Equation119GeometryRelativeContourExact.coarseBackgroundHolonomy
is the reference bond from the same nativeGeometryAt, and relativeContourElement
is Gamma times inverse(coarse), not the reverse order. Hence the candidate
boundary link is exp(Y) times coarse on the right. Mixed-scale endpoint and
multi-anchor compatibility still require actual source identification.

Reuse BalabanCMP109BishopRootFreeSeriesExact.aSeries and bSeries:
C(s)=1-s A(-s), S(s)=1-s B(-s), exp(Y)=(C(s), S(s)Y).
No zero/positive radius decision is needed; s <= 1/16 is already inside the
series domain. BalabanP33BishopLiteralQuaternionExponentialChordExact is an
existing conditional radius-case consumer, not a total real-radius compiler.
Reuse BalabanClayT2BishopQuaternionNormalizationExact.multiplyQuaternionB
and fourProductB. Do not assume the rational unit carrier is closed under exp.

For n>=1 the coefficient of s^n in C²+sS² is (-1)^n/(2n)! times
(sum of even binomial coefficients minus sum of odd coefficients at 2n);
both sums equal 2^(2n-1). Constant term is one. Absolute convergence gives
the classical identity. Local exact Python/SymPy execution checked coefficients
1..40, Hamilton norm multiplicativity and right-product displacement.
The reproducible script is scripts/check_ym_cmp102_root_free_exp.py.
This is not native Agda acceptance.

Next: formalize the same-series Cauchy product and parity-limit weld using
BishopExponentialCauchyProductExact and existing finite parity machinery.
JInvariantBishopTrigUnitPhaseExact consumes a Pythagorean certificate; it
does not prove one. Prove unit norm of actual root-free exp and identify
it with source exponential, then derive chord²=2s A(-s)<=s using alternating
bound. Compose with the same coarseBackgroundHolonomy and existing plaquette
consumer. Actual CMP102 mixed-scale incidence, Eq(7) strict witness, gauge
section, real minimizer and propagator remain OPEN. No radius shrink,
new kernel acceptance, CI or Clay endpoint promotion.


### 2026-11-20 — CMP102 Eq(7) and Bishop donor reconciliation

Exact donor heads inspected: #1478 fb374e50e59a98e2b8a1eee215c77428c5728b68,
#1529 0626c465c2721525f432bfef57d96f02d24fbe3d,
#1499 251b567d5242185b81dfdcd036889ca3b434f899,
#1503 b93909a044960a90690393fdadcb9f6692a139c0.
#1478 actual BishopComplexExpFactEqualsNativeExpExact proves source-written
coordinate convergence of factorial series to configured native expC.
BishopComplexCauchyTriangleLimitTransportExact transports Cartesian rectangle
limits with vanishing upper-wing residuals; specialized factorial donor is
for real and imaginary axis streams. BishopOriginalNativeComplexExpAdditionFromTrigExact
still takes OriginalCosineAddition and OriginalSineAddition; do not claim
unconditional addition from that owner. No donor kernel replay or transplant.
For root-free quaternion use weighted pair multiplication (ac-sbd,ad+bc);
at s=0 this formal algebra is dual numbers, not the complex field. Reuse
coordinate limit architecture or scalar coefficient cancellation; no division
by radius or unit imaginary direction.

Eq(7) audit: distinguish CMP102 pp255–275 DOI BF01229380 (local extract,
characteristic-function decomposition) from pp277–309 DOI BF01229381
(variational theorem). BalabanSelectedBackgroundVariationalChartBridgeExact
has incorrect page metadata 605–636 in header; DOI is correct.
FiveChannelSmallFieldRadius is conditional linear-budget compiler;
CommonSmallFieldRadius assembles input certificates; SmallFieldNonlinearConstants
assembles input coefficient bounds; PlaquetteBoundaryStateNormChargeExact
proves perturbation projector charge identity, not group plaquette smallness.
BalabanClayGate4BackgroundFieldVariationalTheoremExact consumes supplied
CoarseSmallField coarse before producing selected background and fine-bond
estimate. BalabanPath13VariationalSpecializationExact and
BalabanCMP98Path13VariationalRadiusSourceFamilyExact remove redundant
same-object/radius inputs conditional on this source. Do not use downstream
fineBondSmallness to prove its own coarse input: trace previous-scale
admissible domain and actual mixed-scale boundary incidence instead.
Eq(7) normalization established; producer prior-art search remains open,
not a claim of mathematical absence. Physical same-object attachment open.
Root-free analytic weld remains open; no new kernel acceptance, CI, radius
reduction or Clay promotion. Constructor/geometry audit before changing math.


### 2026-11-20 — reuse CMP99/CMP102/Cauchy and literal small-field complement

At e746c117 the actual BalabanClayGate4LiteralWilsonLargeFieldPredicateExact
defines LargePlaquette as threshold² <= literalChordalDistanceSq of the
supplied rational unit plaquette holonomy. For an owned plaquette, the
negative LargeFieldBlock witness excludes largeWitness; rational strict
order then gives chord² < threshold². This is a direct complement
specialization, not a new physical smallness estimate. Equality is large,
not small. Preserve ownedPlaquettes membership, exact selected configuration,
threshold vs scaleAdjustedThreshold, and rational vs Bishop-real carrier.
Do not infer a decidable strict dichotomy for arbitrary Bishop reals.
Actual mixed-scale shell membership and threshold/source identification
remain open. BalabanC2SmallLargeAllScaleExact packages supplied curvature
and one-step coercivity hypotheses; no unconditional Eq(7) producer there.

CMP99 already has BalabanClayGate4BackgroundPropagatorDecayTheoremsExact
(Theorems 3.1–3.4 source authority), BalabanCMP99CovarianceLocalityToRGStateExact
(cmp99CovarianceCapForNextState), and BalabanCMP99PathDerivativeSourceReplayRound413Exact
(asR408StageDifference, asR410CanonicalPathReplay,
cmp99PathDefectBelowResolventBudget). R413 fixes the changed pathDerivativeStage
definitionally and consumes the existing resolvent budget. Reuse R408/R409/R410
and R360; remaining inputs are same actual perturbed/reference inverse,
norm/order, unchanged outer dexp/log inverse/transport derivative, distance
and regular background. Do not reconstruct CMP99 decay or marked comparison.
BalabanPropagatorSourceLedger.md already identifies CMP99 regular configurations
DOI BF01466594 separately from propagators DOI BF01240355, and CMP102
variational Theorem 1 / Proposition 9 DOI BF01229381.
CMP102 R367 consumes source critical-map contraction and same argument
distances; source C-Lipschitz not a separate scalar primitive.
Cauchy already has BishopExponentialFiniteCauchyCoefficientExact,
BishopFiniteCauchyRowReindexExact, BishopFiniteCauchyTriangleInsideRectangleExact,
BishopFiniteRectangleInsideCauchyTriangleExact, BishopFiniteCauchyWingAbsoluteBoundExact,
BishopExponentialCauchyProductExact (bishopExpTimesNegativeIsOne).
Reuse these scalar finite and limit owners and #1478 complex donor; only
weighted pair same-series specialization remains, not general Cauchy theory.
Next implement explicit rational complement consumer on existing predicate,
then connect previous-scale mixed geometry and actual Bishop-real boundary
links. This audit does not assert new formal complement code, donor transplant,
kernel acceptance, radius reduction, CI or physical gate closure.


### 2026-11-20 — literal rational small-field complement implemented

In BalabanClayGate4LiteralWilsonLargeFieldPredicateExact, add SmallPlaquette,
notLargeImpliesSmall, smallImpliesNotLarge, goodBlockOwnedPlaquetteSmall,
allOwnedSmallImpliesGoodBlock, and gauge forward/backward transport.
The two directions consume the original LargePlaquette and largeWitness;
no new field, radius, or membership authority. The repository Empty is
explicitly eliminated into stdlib bottom when applying rational strict order.
At equality the large predicate holds. Scope is the exact rational
holonomy and unadjusted threshold; mixed-scale Bishop source attachment
and scaleAdjustedThreshold identification remain open. Source-written,
Agda kernel pending; no CI or physical gate promotion.


### 2026-11-20 — literal bad-component complement weld

Source commit 4303ce641148: BalabanClayGate4LiteralWilsonLargeFieldPredicateExact
now exposes OutsideWilsonComponents, outsideWilsonComponentsImpliesGood,
goodImpliesOutsideWilsonComponents, outsideWilsonComponentsOwnedSmall and
allOwnedSmallImpliesOutsideWilsonComponents. The forward direction constructs
the original Geometry.component and Geometry.root from any large witness;
the reverse consumes Geometry.pathEndBad. Thus absence from every original
bad component is equivalent to strict smallness of every owned plaquette,
on the SAME rational configuration, scale and unadjusted threshold.
No new component allocator, geometric predicate authority, radius or axiom.

Next gate: identify the actual preceding-scale good domain with this
component complement, including any additional collars/exclusions in that
domain (do not assume equality). Transport actual mixed-scale boundary
incidence to the owned plaquettes; separately identify the scale-adjusted
threshold and Bishop-real averaged holonomy. The rational result is not
a decidable strict dichotomy for Bishop reals. CMP102 physical minimizer,
weighted quaternion same-series specialization and CMP99 same corrected
propagator remain open. Source-written only; exact-head Agda pending,
no CI and no physical gate promotion.


### 2026-11-20 — enlarged-component complement and boundary support

BalabanClayGate4RBoundarySupportExtractionExact now defines
OutsideAllWilsonEnlargements on the original Wilson bad components and
Collar.Enlarged, with outsideAllEnlargementsImpliesOutsideComponents
using regionIncludedInEnlargement. outsideAllEnlargementsOwnedSmall
consumes the existing rational strict complement. boundarySupportOwnedPlaquettesSmall
and regularDomainSupportOwnedSmall reuse everyWeaken on the original
LocalizedSupport list. The latter consumes a forward inclusion of the
selected regular domain, not an assumed equality. A single component's
collar does not exclude other bad components.

Source-written finite consumer; actual preceding-scale regular membership
and global exclusion producer, selected mixed-scale plaquette incidence,
Bishop-real averaged holonomy and adjusted threshold remain OPEN.
No new analytic assumptions, reduced radii, or physical gate promotion.
Agda kernel and CI not run.


### 2026-11-20 — finite periodic regular-domain producer

The existing RBoundarySupportExtraction owner now contains PeriodicRegularProducer.
BadSeedWithin combines original Wilson badness and bounded reach on the original
periodic physical carrier. noBadSeedDecidable searches the complete finite block
list with decideAny; no component enumeration or path-length bound is required.
Both directions of the global enlargement exclusion use original pathEndBad
and component/root, respectively. periodicRegularBlocks filters the original
enumeration; soundness and completeness use existing filterDec theorems.
periodicRegularBlocksOwnedSmall and periodicRegularSupportOwnedSmall produce
strict rational plaquette smallness from actual filtered-list membership.
The component adjacency need not match the enlargement adjacency for this
union identity; the enlargement itself is fixed to physical periodic reach.

Next: identify the actual preceding-scale CMP102 regular domain (including
additional exclusions) with a subset of this list, and recover the literal
mixed-scale boundary incidence. Adjusted threshold and Bishop averaged
holonomy remain separate. Source-written, kernel pending; no CI, radius
reduction, or physical gate promotion.


### 2026-11-20 — native root-free quaternion specialization

BalabanCMP98Path13BishopNativeSourceExact now constructs quaternionW from
the unscaled native Lie vector, proves quaternionWQuarterAdjoint and
quaternionWBelowSixteenth from existing SmallLie admission, and derives
quaternionSignedWInside. The convergent existing aSeries/bSeries are evaluated
at the quaternion argument, not the fourfold adjoint argument.
rootFreeQuaternionCandidate uses the existing QuaternionB carrier and
nativeAveragedQuaternionCandidate consumes the actual outerY and outerRelevant
from nativeInputsFromPhysicalRadius, with the original selected radius witness.
This is a candidate coordinate constructor, not yet a certified unit
quaternion or a proved exponential identification. Same-series unit norm,
Cauchy product/exp-log identification, strict chord transport, actual CMP102
preceding-scale domain and mixed-scale incidence remain OPEN.
No radius reduction or new analytic authority. Source-written; kernel pending.


### 2026-11-20 — CMP102 complementary factorial coefficient reconciliation

Pinned donor: PR #1529 8fd6176551c643e72700a1410fb32d9b69e0480f, DASHI/Foundations/BishopFiniteEvenOddSeriesReindexExact.agda (originalBishopFiniteEvenOddSumReindex). Its only repository-module dependency, BalabanClayGate4BishopHalfRadiusRealEstimatesExact, has identical blob e5a4cf2f871fb4ce2892ed7a0183257b331b5848 on both branches. Transfer the donor unchanged. PR #1478 is merged; do not assume its complete dependency closure is present on this older YM branch. The local BishopExponentialBinomialCoefficientExact already supplies embeddedInverseFactorialProductBinomial and expConvolutionTermBinomial; prefer these real owners to importing the complex capstone.

Write z=-w_q, C=1+za, S=1+zb using the actual shifted aSeries/bSeries. For n>=1 the coefficient of C^2-zS^2 is the signed factorial convolution at degree 2n, hence zero by (1-1)^(2n). The finite parity split has 2n+1 terms: apply the donor at n and append the final even endpoint. Shift the zero positive-degree coefficients down BEFORE limit transport; never divide by z. This proves the intended scalar identity 1-2A+w_q(A^2-2B)+w_q^2 B^2=0 including w_q=0, once the original same-series Cauchy product and shifted limit are attached. Unit norm then yields chord squared = 2w_q A. Alternating bound 0<=A<=1/2 on the admitted w_q<=1/16 is a separate proof target.

Shared Paper 9 observation: multiplication by t in R[t]/(t^2-z) has matrix [[0,z],[1,0]], and conjugate norm a^2-zb^2. The exponential matrix has determinant C^2-zS^2=1. At z=0 the generator is nilpotent. Monster cyclotomic norm a^2-ab+b^2 is the analogous quadratic norm, not a representation-specific proof dependency. No new carrier required.

Acceptance: unchanged parity donor source transfer only; signed specialization, shifted Cauchy limit, native quaternion unit norm, chord, exponential identification and actual physical CMP102 domain attachment OPEN. No kernel/CI acceptance or Clay promotion; original physical radius retained.


### 2026-11-20 — CMP102 signed finite convolution specialization

New source-written owner: DASHI/Foundations/BishopSignedFactorialConvolutionExact.agda.
It reuses finiteExponentialCauchyCoefficient, expTermCongruent, expTermZeroAtPositive, finSumIsSeriesOf and originalBishopFiniteEvenOddSumReindex. signedPositiveDegreeZero specializes at (1,-1); inclusiveParity retains the final endpoint; signedInclusiveEvenDegreeZero joins these on the original Bishop sum. Existing vendor/Bishop and DASHI donor attribution retained. No new carrier, axiom, radius division or representation-specific Monster dependency.

Independent local Python Fraction regression: 128 inclusive parity checks, 128 omitted-endpoint negative controls and 128 shifted bracket coefficients passed (degrees 0..127). The corresponding reference is scripts/check_cmp102_signed_factorial_normalization.py. This is a finite reference, not a proof of the Agda source.

For the actual signed shifted aSeries/bSeries, the next Agda cut must identify every parity summand with the original shifted factorial coefficient, including degree zero and the two boundary terms, then transport through the same-series Cauchy limits. The bracket coefficient is (-1)^(n+1) times the inclusive signed convolution at degree 2n+2. Shifted Agda identity, analytic normalization, native unit norm/chord, alternating bound and physical CMP102 attachment remain OPEN. Agda executable unavailable locally; no kernel or CI acceptance. No Clay promotion.


### 2026-11-20 — CMP102 original positive-coefficient endpoint cut

Actual root-free series owner: BalabanCMP109BishopRootFreeSeriesExact, with positive aCoefficient(n)=1/(2n+2)! and bCoefficient(n)=1/(2n+3)!; term c X n carries X=-w_q. Added aBelowOneHalf by specializing the existing alternatingLimitBelowFirst on the same limit; aNonnegative already exists. No radius change.

New source-written BalabanCMP102BishopShiftedCoefficientExact defines the actual positive-coefficient evenPart and oddPart using original Row.cauchyCoefficient and original aCoefficient/bCoefficient, handles the singleton odd row at degree zero, and gives finiteTwoEndpointSplit, shiftedBracketBaseZero, signedRowsCancel, and shiftedBracketZeroFromOriginalRows. The last theorem is explicitly conditional on the two original signed-row boundary/interior identifications; these are NOT proved by the consumer. The desired polynomial is G(X)=1-2A-XA^2+2XB+X^2B^2. Its coefficient is oddPart-evenPart, i.e. minus the inclusive signed convolution of degree 2n+2. Existing Bishop/Murray/Csimma and DASHI factorial, parity, ring and Cauchy owners retained; no new carrier, new postulate or division by radius.

Local independent Python Fraction reference executed: 128 even boundary/interior, 128 odd boundary/interior (including singleton n=0), 128 shifted cancellation and 128 missing-final-endpoint negative controls, 512/512 total. Script: scripts/check_cmp102_native_shifted_coefficient.py. This is finite arithmetic, not an Agda receipt.

NEXT: prove the actual signedEvenRow ~= evenPart and signedOddRow ~= -oddPart, including natural complementary indices, and attach existing convergence to the original coefficient polynomials. Analytic G=0, unit quaternion, chord and physical CMP102 remain OPEN. Agda executable not found locally, so all new theorem bodies are source-written only; no CI or Clay promotion.
