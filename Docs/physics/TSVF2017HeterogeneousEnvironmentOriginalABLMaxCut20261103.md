# TSVF 2017 heterogeneous environment -> ORIGINAL ABL -> robust bound: max-cut (3 Nov 2026)

## Source-first result / attribution

This is a continuation of the 186-lemma P00--P11 `Emergent31QuantumYMKKExactLemmaRoadmap20261103.md`; it does **not** create a separate proof programme or renumber its obligations. Foundational authors: Aharonov--Bergmann--Lebowitz (1964), Aharonov/Vaidman, Aharonov--Cohen--Landsberger (2017, *Entropy* 19:111); original repository owners: `DASHI.Quantum.TSVF`, `BidirectionallyAdmissibleHistoryFibreExact`, `CayleyDicksonRationalComplexQuaternionExact`, and all #1460 predecessor modules. Osterwalder--Schrader/Stone and Bałaban remain the respective independent theorem owners.

**Novel SOURCE-WRITTEN files**, conditional on normal Agda stdlib imports, not verified by the Agda kernel in this session:

1. [TSVF2017HeterogeneousEnvironmentABLExact.agda](../../DASHI/Quantum/TSVF2017HeterogeneousEnvironmentABLExact.agda) constructs a finite list of distinct two-level rational-complex Hermitian environmental site pairs. For a site list `ss` it proves
   `|prod_s <r_s|w_s>|^2 = prod_s |<r_s|w_s>|^2`, and for arbitrary complex disturbance amplitudes `gammas`,
   `|prod_j gamma_j * prod_s <r_s|w_s>|^2 = prod_j |gamma_j|^2 * prod_s |<r_s|w_s>|^2`.
   It specializes back to the original homogeneous all-`k` environment theorem without restating the proof as a new axiom. It then *uses the existing* `TSVF2017OriginalComplexABLSelectedExact.finiteComplexQuantum`, its two genuine projectors, the original `DASHI.Quantum.TSVF.ablProbability`, and the earlier two-admitted/one-excluded boundary history source. The positive selected total `1 + W` is derived; original-ABL numerator normalization and the wrong-numerator gamma/environment factorization are proof terms.
2. [TSVF2017HeterogeneousRateExact.agda](../../DASHI/Quantum/TSVF2017HeterogeneousRateExact.agda) proves a heterogeneous rate law for *arbitrary* calibrated Nat Born count pairs `r_s,w_s` with `2 w_s <= r_s` per site:
   `2^k prod_s w_s <= prod_s r_s`, where `k` is precisely the list length. With disturbed counts `Gamma_W <= Gamma_R`, it proves the division-free `(2^k+1) Gamma_W prod_s w_s <= Gamma_R prod_s r_s + Gamma_W prod_s w_s`. For a positive selected total this is the probability-tail bound `P_wrong <= 1/(2^k+1)`. Its original 25/9 site inhabitant and repetition theorem recover the earlier uniform model.
3. [check_tsvf_2017_heterogeneous_abl_rate.py](../../scripts/check_tsvf_2017_heterogeneous_abl_rate.py) is the committed exact-rational independent arithmetic fixture. An equivalent local implementation **executed** 2,100 complex heterogeneous factorization/ABL cases, 4,500 heterogeneous rate cases and 45 homogeneous sizes, with two negative controls. The pushed script itself was not executed through a checkout and there is **no Agda binary in this environment**.

All three are imported/re-exported by `DASHI.Unified.BalabanRGTOERegression` except the script, which is an external checker.

## Important physical boundaries and falsification

- **Independence is a material premise:** the complex overlap factorizes only on a selected tensor-*product* environment. An entangled or correlated source cannot be replaced by a list of local marginal overlaps. Exact negative control: the two normalized coherent states `(3|00>+4|11>)/5` and `(3|00>-4|11>)/5` have the same one-site diagonal reduced densities, while global Born overlap is `49/625`, not `1`. The actual apparatus must establish the needed product, cluster, or quantitatively controlled approximation hypothesis.
- **The original finite ABL model has a deliberately nonzero right amplitude 1**. The physical source must independently construct its actual selected initial/final state and allow neither arbitrary postselection nor division by zero. The formal result is a finite complex inner-product/ABL theorem; it is not a many-body laboratory implementation or a thermodynamic claim.
- **Complex amplitude vs probability:** published 2017 Eq. (25) uses gamma overlap notation; arbitrary complex products require Born squares for a probability. The earlier `TSVFComplexGammaProductBornExact` and phase counterexample still apply.
- **Calibration firewall:** the new exact Nat rate does not by itself prove that arbitrary rational-complex site norms satisfy `2 w_s <= r_s`, nor that a real physical local disturbance obeys the global `Gamma_W <= Gamma_R`. This missing complex-to-ordered-certificate bridge must be proved on the **same selected site list** before promotion.
- **Clock firewall:** `TSVFOSSameSelectedClockIterateExact` owns finite-time commuting under a one-step physical intertwiner. This does not establish a strongly continuous unitary equivalence, its generator domains, spectral transport or `H_clock=H_OS` in the physical representation.
- **Clay independence:** R443 compact continuous SU(N) one-link Haar/native bond and CMP119, R445 physical continuum moments/limits, R320 CMP116 rooted-shell decay, R333 same-H spectral gap, H6 nontriviality all remain OPEN and can be proved independently of emergent (3,1)/KK.

## New immediate maximal frontier / minimal leaf cut

**P01.L13**: Construct actual controlled-unitary apparatus dynamics on the selected full complex Hilbert pointer + `N` environmental registers, and prove the *emitted* branch states equal the site records now consumed; characterize correlations rather than silently assuming independence.

**P01.L14--15**: Prove source-generated final postselection, original ABL normalization for the actual selected dynamics, exact physical complex `gamma_j` disturbance transfers and a calibrated sitewise overlap theorem; if the environment is correlated, replace equality by an explicitly proved global error/cluster bound. Derive ordered real/natural rate certificates from those actual Born masses and a real positivity theorem.

**P01.L16--18**: Prove the single-branch backward macro-record reconstruction/no-backwards-signalling comparison on the same physical selected observable net, with Everett/multiverse interpretations kept distinct.

**P07.L01--08,L15--16**: Supply the original observable clock as a strongly continuous physical unitary group on the same Hilbert space as the OS reconstruction; prove dense-domain generator and spectral projector intertwinement, selected OS reflection and physically preserved pointer/gauge observables. Matching finite steps or a 3+1 signature does not suffice.

**P05/P06 (independent)**: The physical Haar/measure/CMP119 -> changing-cutoff R445 -> CMP116 R320 -> nontrivial OS R333/Delta>0 route is still the largest mathematically independent Clay gate. No 5D KK claim is used to close pure 4D YM.

## Verification ledger

| Level | Current status |
|---|---|
| Github writes / file readback | New Agda source files, test script and root import pushed; SHA readback pending terminal audit |
| Source-written Agda | New exact finite proof terms; `{-# OPTIONS --safe #-}`; no local postulates, holes or termination bypasses intended |
| Independent exact model checks | PASS: 2,100 complex, 4,500 rates, 45 homogeneous and two negative controls (equivalent local Python) |
| Agda --safe kernel | **NOT RUN**; no transitive safe closure receipt |
| Physical P01/P07 | OPEN: dynamics, postselection, correlation and same-H OS source |
| Pure 4D Clay | OPEN: R443/R445/R320/R333/H6 |
| Emergent (3,1)/KK/gravity | OPEN; no unification or experimental claim |

**Proof-state rule:** source-written != kernel accepted != physically inhabited != experimental confirmation.
