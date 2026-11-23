# P0 original Wilson R445 × binary/base-2 369 × canonical BIPM SI: exact native physical-scale BIDI

Date: 2026-11-22. Owner: master-based #1536; cross-references original stacked #1444, indexed 369 cube #1291. Scope: **finite original Wilson source label geometry and an SI-typed conditional decay-rate identity**. It is NOT a newly established physical mass gap.

## Recall the ORIGINAL SI owners (do not reinvent)

1. \`DASHI/Physics/Units/SI.agda\`, sourced to BIPM *The International System of Units*, ninth edition, revision 4.01 (June 2026), DOI 10.59161/AUEZ1291. Seven **integer exponent** dimensions ordered (L,M,T,I,Theta,N,J), typed units/quantities and decimal scale, provenance/version/uncertainty.
2. \`DASHI/Physics/Units/SIMetrologyBridge.agda\`: separates dimensionally valid quantity, definition-exact constant, measured parameter and model-derived value. A model physical-spacing coordinate is not an empirically measured calibration.
3. \`DASHI/Physics/Units/MechanicalDimensionExact.agda\` and \`DASHI/Physics/YangMills/YangMillsSIScalingEndpointExact.agda\`: dimensionless lattice gap × inverse length (m^-1) first produces a **typed inverse correlation length** (m^-1). Optional explicit \`NaturalUnitConversion\` with hbar/c and hbar*c laws produces SI mass [kg] and energy [J]; no silent natural units.
4. \`BalabanPhysicalClusteringScaleAlgebraExact.agda\`: source-reused physical rational spacing \`a\`, inverse spacing \`aInv\`, dimensionless localization exponent \`lambda\`, and physical lower-rate floor \`mu <= lambda*aInv\`; it proves the exponent-distance inequality from reciprocity and ordered rational algebra. Does NOT instantiate the original Wilson D1 analytic source.
5. \`YangMillsClayPinnedPhysicalGapAttachmentExact.agda\`: conditional exact attachment of the *same* physical decay rate to the selected literal OS Hamiltonian and SI target. Requires actual physical clustering and same-H hypotheses. \`BalabanClayT5MassScaleDimensionExact.agda\` explicitly warns inverse length is not automatically mass.

The original SI system is about metrology/units, NOT the similarly named self-indexed hyperfabric. The *binary/base-2 369* address codec is instead the exact 1024 original positive bond ↔ 128 original native R445 fine-pair addresses × 8 transverse residual sheets, as proved at the finite source-index level in \`YMClayR445Base2ThreeAxis369FibreBIDIExact.agda\`. Their semantics intersect only through the actual native R445 2-link geometry and a supplied physical-spacing calibration.

## Exact two-step SI result: 2 physical links, not 8 address alternatives

At original side-four \`n=3\`, let the fine physical spacing be \`a [m]\`. One R445 native blocked positive link traverses **two consecutive axial positive fine links**, hence its geometric physical length is \`2a [m]\`. The three transverse residual bits yield 8 address sheets, but NONE represents an extra step along the Wilson path. Index multiplicity is distinct from physical distance.

Let \`lambda_f>=0\` be the original selected dimensionless fine lattice-decay exponent and \`i_f=1/a [m^-1]\`. For a physical coarse two-link distance calibrated to \`a_c=2a\`, inverse coarse spacing is \`i_c=i_f/2\`. If, AND ONLY IF, the actual rate transported through the ORIGINAL same Wilson marked source has coarse exponent \`lambda_c=2 lambda_f\`, then the physical decay rates match:

\`\`\`
lambda_c * i_c
 = (2 lambda_f)*(i_f/2)
 = lambda_f*i_f                    [m^-1].
\`\`\`

New #1536 owner \`DASHI/Physics/YangMills/YMClayR445Base2SIPhysicalRateBIDIExact.agda\` reuses the exact R445 128 native selected parity source, the original \`PhysicalScaleData\` and \`YangMillsSIScalingEndpointExact.SIIndexedQuantity\` to prove:

- native selected binary \`s=000\` bond is exactly \`originalR445SelectedFineBond\`;
- fine spacing carries SI.Length and original native pair length is two fine SI lengths;
- coarse dimensionless exponent is 2× fine exponent **by definition of the comparison target**, with \`OriginalR445TwoStepSICalibration.inverseCoarseSpacingIsHalfFine\` an **explicit field**;
- the resulting coarse and fine \`SIIndexedQuantity ℚ inverseLength\` are exactly equal, using the existing rational ring solver, not an ungrounded analytic equality;
- a separate \`OriginalR445SIInputMetrology\` witness reserves actual measured spacing, measurement authority/version/uncertainty and source-to-theory matching; no value is supplied or fabricated;
- mass and energy conversion are calls to the ORIGINAL \`NaturalUnitConversion\` owner, keeping hbar/c and hbar*c evidence mandatory.

**Crucial physical source gap:** The code does **not** assert or prove that the actual original Wilson effective coarse action has \`lambda_c=2lambda_f\`. The equation says what the rate must do **if** both descriptions represent a common physical inverse correlation length. The all-cutoff W1/W3 original Gibbs differentiation and small/large-field estimates must supply that physical agreement; \`n=3\` finite bond geometry cannot pay it. The full native 896 spectators remain in the original weighted F19 source.

## q versus SI rate and the continuum negative controls

For a source-derived original single-step decay factor \`0<q_n<1\`, let \`lambda_n=-log(q_n)\` (dimensionless). Then physical exponential decay rate is \`mu_n=lambda_n/a_n\` with dimension [m^-1]. If the SAME physical two-link rate is represented at coarse spacing \`2a_n\`, its factor must obey \`q_coarse=q_fine^2\`. **This is an analytic matching condition, not a combinatorial consequence of R445.**

- Counterexample: if someone sets \`q_coarse=q_fine\` while doubling physical step length, they obtain a physical rate only **half** as large. A valid finite R445 reindex does not prevent this error.
- Counterexample: a fixed \`q<1\` and \`a_n→0\` corresponds to formal \`lambda/a_n→∞\`, not a finite nonzero mass-scale identity; it is only an upper-decay bound and may be vacuous for nontrivial continuum fields. The physically calibrated family \`q_n=exp(-mu*a_n)\` would have finite constant inverse length [m^-1], but the original Wilson model has NOT been proved to obey that family.
- **SI dimensional firewall:** \`mu[m^-1]\` is not an SI kilogram. \`m_SI=(hbar/c)mu\` in kg, \`E_SI=hbar*c*mu\` in J, requiring physically justified constants/scheme and OS Hamiltonian identification. Numeric correlation length and a nontrivial physical mass are different proof obligations.

## Strict scalar and physical source identification still outstanding

The SI/rational `BalabanPhysicalClusteringScaleAlgebraExact.PhysicalScaleData` is an `ℚ` typed dimensional compiler, whereas the selected full interacting original `YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource` and E1/F19 Wilson probability use `RealAnalysisAxioms.ℝ` and source-selected compact Haar/exponential. They cannot be treated as definitionally the same scalar; a justified scalar transport with preserved inequalities, actual Wilson tests and common normalization is a separate bridge. A demonstration for native `n=3` does not automatically supply every cutoff and all physical volumes. In particular, the physical `cubeLength` of the D1 original full Wilson record is in the original `ℝ` context and must be fixed-calibrated across `n` before taking a continuum SI inverse-length interpretation. The SI metrology registry cannot be populated with a fabricated measurement as a replacement for that analytic proof.

## Local executable acceptance and remaining physical frontier

The local SymPy 1.14.0 reference \`scripts/check_ym_r445_binary369_si_scaling_20261122.py\` verified exactly: seven-exponent SI dimension arithmetic, \`hbar/c × m^-1 = kg\`, \`hbar*c × m^-1 = J\`; rational two-step equality \`(2lambda)*(i_f/2)=lambda*i_f\`; \`-log(q_fine^2)/(2a)=-log(q_fine)/a\`; countercheck coarse unchanged q halves the rate; constant q yields divergent formal inverse length as spacing decreases; and original 1024=128+896 labeling. It reuses the separate original source-index regression of 1024 bonds and 1536 plaquettes. **Neither executable is Agda kernel checking, empirical metrology, an original Wilson analytic estimate or a same-H OS spectral gap proof.**

For P0, reuse \`YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource\` and W1/W3 \`chargeSumBelowPhysicalRootedShell\`, plus preexisting #1444 original Wilson sparse bad-contour chessboard source and CMP119/122. The missing original estimate is across changing cutoffs, with fixed physical distance, actual original same-J marked Gibbs activities, genuine large-field error and nontrivial E1 interacting limit. Once a real inverse length and common same-H OS result are proved, attach the SI conversion via existing owners. SI correct code cannot promote the positivity, convergence, or spectroscopy leaves.

P0 Yang–Mills remains first; P1 antigravity follows.
