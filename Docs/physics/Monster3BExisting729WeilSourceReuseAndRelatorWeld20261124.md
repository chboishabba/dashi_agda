# Monster 3B — original 729D Weil source already exists; compute original C/D cocycle and R⁷ phase instead of inventing k₀

**24 November 2026 | Canonical P5 audit and mathematical endpoint cut for [PR #1545](https://github.com/chboishabba/dashi_agda/pull/1545).** Source-first, geometry-forward, zero-mode/residual preserving. The decisive correction is that the repository **already has a constructive 729 Schrödinger representation and exact Weil kernel**. The missing variable was not the 729 carrier or its finite Fourier operator. It was the **choice of a source-aligned overall scalar gauge** and the operator identification on the **same literal Monster group word, E-basis, phase and 90D Hom carrier**.

## 1. Reuse ledger: previously owned theorems and executable producers

| Existing producer | What it already supplies | Exact boundary |
|---|---|---|
| [\`DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda\`](../../DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda), \`Monster3BFiniteSchrodingerFullActionLawExact.agda\`, \`Monster3BFiniteSchrodingerArbitraryWeylExact.agda\` | \(E=3^{1+12}\) original finite law, \(\mathrm{Schr}_s=\operatorname{Fun}(\mathbb F_3^6,\mathbb Q(\zeta_3))\), 729 dimension, \(T_aM_b\) Weyl action and centre \(\zeta_3^s\) | Literal MODEL action, not a supplied ordinary Monster W_s matrix |
| \`Monster3BFiniteSchrodingerPointProjectorExact.agda\` and \`Monster3BFiniteSchrodingerPointProjectorEvaluationExact.agda\` | Six commuting coordinate idempotents, point projector \(P_0\), pointwise extraction and normalization | The point projector and the 729 vacuum are *already* constructed |
| \`Monster3BAtlasSymplecticBasisIntertwinerCompilerExact.agda\`, \`Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact.agda\` | \(M\in\operatorname{GSp}_{12}(\mathbb F_3)\) with signed \(\lambda\), asymmetric cocycle \(c((a,b),(a',b'))=b\cdot a'\) and quadratic correction \(q(v)=2v^\top(M^\top C M-\lambda C)v\) | The actual Monster group word must have its affine section defect removed before using the canonical \(q\); the existing \`monster3b_mmgroup_canonical_cover_words.py\` now does this |
| [\`scripts/toe_cyclotomic_operator.py\`](../../scripts/toe_cyclotomic_operator.py), \`scripts/check_toe_atlas_weil.py\`, \`scripts/check_toe_atlas_rechart.py\`, \`scripts/check_toe_extended_batch.py\` | Exact 729 Weil support \(|\operatorname{supp} K_g e_x|=3^{\operatorname{rank} b}\), nonzero cyclotomic kernel phases and chart transport; signed \(\zeta\leftrightarrow\zeta^2\) action; examples with exact Fourier normalization and paired \(\mathbb Q(\zeta_3)[i]\) gauge | The TOE compiler explicitly says **“scalar gauge is an explicit input, not determined by quotient covariance”**; do not silently call its model normalization the original Monster W normalization |
| \`Monster3BNormalizerCocycleCancellationExact.agda\`, \`Monster3BCommonRepresentationTransportExact.agda\`, \`Monster3BHZetaCharacterTransportCompilerExact.agda\`, \`DASHI/Wikimedia/IbrahimMonster3BLinearMultiplicityHomSpaceExact.agda\` | Generic inverse projective cocycle, same-object evaluation/isotypic Hom compiler and actual-source preservation contracts | Generic cocycle cancellation **does not fill** a source \(729\otimes90\) action automatically; it is ready to consume the genuine source coefficients computed below |

**Attribution:** classical finite Heisenberg/Stone–von Neumann, Weil and Maslov theory retain historical credit; original ATLAS source 12D matrices retain ATLAS/AtlasRep credit; existing TOE/Agda finite operator owners are reused, not credited as novel in this consumer. Original Monster group words belong to Dietrich–Lee–Pisani–Popiel; original Monster class character/fusion to Barraclough–Wilson and their underlying sources; Ibrahim's actual 12/78 and Hom work remains distinct from this DASHI compiler consumer.

## 2. Full source kernel already determines the zero-vacuum coefficient

Fix the original six-position/six-modulation \(E\) chart, a signed centre phase \(s\in\{1,2\}\), a genuine quotient transformation \(M_g\), and its centre multiplier \(\lambda_g\). The existing TOE compiler expresses each *unnormalized* column \(K_{g,s}e_x\) as one cyclotomic phase on each of \(3^{r_g}\) support points, with \(r_g=\mathrm{rank}((M_g)_{a,b})\). The source-specific quadratic phase \(q\) is already computed by that compiler.

Choose an **explicit, not source-implied, unitary model gauge**
\[
\Delta=\zeta_3-\zeta_3^2=1+2\zeta_3,\quad \Delta^2=-3,\qquad
\widetilde K_{g,s}=\Delta^{-r_g}K_{g,s}.
\]
Then every nonzero matrix entry has absolute size \(3^{-r_g/2}\), as required by original Weil orthogonality. The **model** B-vacuum coefficient is exactly
\[
\boxed{\kappa_{g,s} =
  \langle e_0,\widetilde K_{g,s}e_0\rangle
=\begin{cases}\Delta^{-r_g}\zeta_3^{q_{g,s}(t_0)}&
   0\in\operatorname{supp}(K_{g,s}e_0),\\0&\text{otherwise}.\end{cases}}
\]
When it is nonzero, the affine support equation \(y_0+B t_0=0\) has a UNIQUE solution because the repo compiler's \(B\) columns are independent. This is a direct reuse of the original 729 **point-projector** kernel, not an invented unknown scalar. **Zero is retained**: a vanishing \(\kappa\) cannot be divided out and requires an alternative source point/projector.

The source [\`scripts/monster3b_original729_weil_source_cocycle_weld.py\`](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) reuses \`toe_cyclotomic_operator.compile_shape\` and the original MM full-word corrected \(12\times12\) \(\mathbb F_3\) matrices. It derives the exact \(\kappa_{D,s},\kappa_{CDC^{-1},s},\kappa_{C,s}\) and their products **without running the huge Monster-vector representation and without building a dense 729D operator**. An exact support-inversion fast path finds one kernel entry in \(O(r^2)\) and computes the two-operator cocycle by one 729-state column, not \(729^2\) dense entries.

## 3. Exact 729 Weil projective multiplier and genuine Monster 90D compensation

The existing kernel gives the exact source-model multiplier
\[
\widetilde K_{g,\lambda_h s}\widetilde K_{h,s}
=\alpha_s(g,h)\widetilde K_{gh,s},
\]
where \(\alpha_s(g,h)\in\mu_6\) in the selected unitary \(\Delta^{-r}\) gauge. The compiler computes this by evaluating ONE nonzero entry of both sides. Unlike a list of independent cubic roots for \(D\) and \(CDC^{-1}\), the composition law explicitly retains source word order and all three indices \((g,h,s)\).

In the actual original Monster action, if an original E-compatible Stone–von Neumann evaluation \(W_s\simeq H_s\otimes S_s\) is fixed using the same six E generators and phase, the complementary projective action must satisfy
\[
L_{g,\lambda_hs}L_{h,s}=
  \alpha_s(g,h)^{-1}L_{gh,s}.
\]
This *inverse* cocycle is exactly the already-existing \`Monster3BNormalizerCocycleCancellationExact\` theorem. No independent abstract cocycle theorem or free “Weil coefficient” search is needed after the model gauge is specified. **What remains source-specific is identifying the chosen model Heisenberg/Weil intertwiners with the actual Monster W_s in a compatible basis**, not rebuilding their formulas.

The existing \(\mathrm{MMV}(31)\) right-action vacuum sandwich \(M_g=P_B\rho(g)P_B\) is \(M_g=\kappa_{g,s}L_g\) in the corresponding transposed right Schrödinger convention. Thus its **source-observed** projective multiplier for the literal \(D,E=CDC^{-1}\) words must obey
\[
\boxed{\beta_s(D,E)=
\frac{\kappa_{D,s}\kappa_{E,s}}
     {\alpha_s(D,E)\,\kappa_{DE,s}}}
\]
when all three \(\kappa\) are nonzero. Note that the original \`MMV\` acts on the RIGHT, so the matrix product for actual word \(DE\) is \(M_E M_D\), not \(M_D M_E\). The [\`scripts/monster3b_original729_actual_vacuum_weld.py\`](../../scripts/monster3b_original729_actual_vacuum_weld.py) joins the new 729 source calculation with the *already implemented* actual Monster \(\mathrm{MMV}(31)\) 90D sandwich receipts. It records the predicted scalar in \(\mathbb F_{31}\), compares the actual source scalar and produces truly source-derived \(12D\)/\(78D\) modular operators divided by **the explicit model coefficient**. It refuses zero vacuum, unobserved source, nonscalar cocycle or a failing source orientation.

**Nuance:** this supplies a *convention-labelled projective multiplicity representation* when source compatibility is observed. Concluding it is an honest characteristic-zero \(6.\mathrm{Suz}\) action still requires globally trivializing the inverse cocycle and identifying the same original 6Suz standard words; do not label a modular projective trace as an ordinary character before that.

## 4. New exact ATLAS source computation — both phases, no Magma or mmgroup

Using the **actual SHA-pinned original ATLAS \(2.\mathrm{Suz}:2\) matrices** from \`scripts/check_toe_atlas_mirror.py\`, its existing standard symplectic basis \(P\) (NOT the MM-specific B-polarization), and the existing TOE 729 kernel, we independently calculated **exactly**:

| Original source group element | Off-diagonal rank \(r_g\) | \(\kappa_{g,1}=\kappa_{g,2}\) in the stated ATLAS chart |
|---|---:|---:|
| \(C\) | 2 | \(-1/3\) |
| \(D\) | 6 | \(-1/27\) |
| \(E=CDC^{-1}\) | 6 | \(-1/27\) |
| \(DE,ED\) | 6 | \(-1/27\) |
| \(R=cdcdcddcdd\) | 6 | \(-1/27\) |

Furthermore
\[
\boxed{\alpha_s(D,E)=\alpha_s(E,D)=\alpha_s(C,C)=1,\qquad
       (\widetilde K_{R,s})^7=I_{729}}
\]
for both marked phases \(s=1,2\). The exact R-power cocycle staircases are
\[
\alpha_s(R,R^j)=(1,-1,1,-1,1,1),\quad j=1,\ldots,6.
\]
The quotient \(R\) has order seven (we independently checked its \(12\times12\) \(\mathbb F_3\) source matrix); these are exact **ATLAS-source chart** statements. The new [original ATLAS 729 source replay](../../scripts/check_monster3b_atlas_source729_relator.py) uses the existing pinned \`C,D,J,P\` and the shared Weil kernel; it is a **reusable proof/data producer** for the selected 729 source, not a fictitious user-local MM result. For this turn, the same calculations were performed in local Python using the original source matrices and explicit repository formulas; the committed script itself has not been executed on a git checkout.

**Do not copy \(-1/27\) blindly onto the user-local MM B-fixed vacuum.** A nontrivial symplectic change of basis (the existing 12D original ATLAS-to-MM intertwiner) can change \(\operatorname{rank} b\), the zero support and the phase polynomial. The new source-specific compiler computes the correct coefficient **in the MM polarization**, without any new quotient search.

## 5. The relator \(R^7=z_{3B}\) now forces a specific multiplicity phase

The previously reported full **actual Monster** word satisfies
\[
C^4=D^3=(CD)^{56}=1,\quad C^2=(CD)^{28},\quad
R^7=z_{3B}\ne1.
\]
The 729 model quotient satisfies \(R^7=1\). Let its **chosen unitary model** \(\widetilde K_{R,s}\) have scalar seventh power \(\gamma_s I_{729}\). The exact kernel source computes \(\gamma_s\in\mu_6\). Since \(\gcd(7,6)=1\), there is a UNIQUE rephasing by a sixth root of unity that makes this cyclic operator **exact order seven**:
\[
\boxed{K_{R,s}^{\mathrm{ord7}}=\gamma_s^{-1}\widetilde K_{R,s},\qquad
       (K_{R,s}^{\mathrm{ord7}})^7=I_{729}.}
\]
For the original ATLAS chart above, \(\gamma_1=\gamma_2=1\), so no correction is needed. In the **actual Monster phase** \(s\), the original central element acts by \(\zeta_3^s\). Therefore the same-source complementary operator, *in that fixed cyclic order-seven Weil gauge*, is required to satisfy
\[
\boxed{\left(L_{R,s}^{\mathrm{ord7}}\right)^7=\zeta_3^s I_{90}}
\]
for the original relator generator whose literal Monster seventh power is **\(z_{3B}\)** (if \(\mathrm{MMV}\) right-action sign is opposite, retain and calibrate that orientation rather than silently inverting the phase). This pays the **relator-specific 729 scalar ambiguity mathematically**. It does not by itself split all of \(6.\mathrm{Suz}.2\), fix \(\rho_W(C),\rho_W(D)\) as ordinary complex matrices or identify the corrected C with source Monster class4D. All other 6Suz cover words and the outer phase remain subject to the exact sourced cocycle equations.

## 6. P0–P6 source/consumer and remaining exact lemmas

| Existing lemma | What this audit **pays** | What remains genuinely original-source specific |
|---|---|---|
| M3B-L10A | The 729 source scalar \(\kappa\) is **computable from the original kernel** before any ordinary character reconstruction; previous 517-value finite quadratic trace inversion remains correct *after honest source linearization* | Exact source word/character orientation and any literal complex Steel12 matrix basis |
| M3B-L10B | Full 729 source model action, compact vacuum coefficient, pair cocycle and inverse multiplicity cocycle now *compiled* from **actual corrected MM 12D quotient**; ATLAS R7 donor computed numerically exactly | Link existing actual 90D B-fixed \(\mathrm{MMV}(31)\) to the exact model in the SAME full Monster word/polarization, and promote source gauge from projective modular to honest char0 same-object Hom |
| M3B-L10C | No new 78 problem: the old faithful12→dual-Sym²78→90 operator functor is retained and now has a precise kernel-normalization upstream | Ordinary full 90D complex matrices require a genuinely selected source faithful12 basis |
| M3B-L12R | Exact original ATLAS quotient \(R^7=1\), model 729 \(K_R^7=1\); cyclic order7 \(\mu_6\) rephase uniqueness, ORIGINAL MM \(R^7=z\) **forces \(L_R^7=\zeta^s\)** in that gauge | Literal MM \(C\in4D\), global cover \(\mu_6\)/possible \(\mathbb Q(\zeta)[i]\) outer scalar and source identification of the true group representation |

**Machine producer chain** (one source, not duplicated): original AtlasRep/basis \`check_toe_atlas_mirror.py\` → finite \(729\) \`toe_cyclotomic_operator.py\` → [original 729 model cocycle / source MM C,D](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) → [actual Monster modular \(90\) vacuum and model gauge comparison](../../scripts/monster3b_original729_actual_vacuum_weld.py) → existing exact 12/78/90 and original Ibrahim Hom → Paper10. [The canonical checkpointed P5 runner](../../scripts/run_monster3b_p5_endpoint.py) now launches the independent original ATLAS 729 replay plus source MM 729 cocycle and both genuine modular phase comparisons when available, without Steel/Magma.

**Correct bounded scope:** 729 MODEL mathematical formulas and original ATLAS quotient numbers are established; the user-reported real MM E/Z(E), \(R^7=z\), and original mod31 rank90 are separate already sourced inputs. The newly committed scripts have source-readback rather than a fresh workstation execution receipt. The global same-object \(6.\mathrm{Suz}\) action and the original 4D literal class are still separate endpoints. Do not hide **zero vacuum**, **source class20 diagonal kernel**, **signed central residue**, **\(\zeta\) phase**, **primes31/127**, or **time/indexed original source provenance** under a dimension-only 729 label.
