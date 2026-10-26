# 27 October 2026 — original 2024 Rodin Eq (7): field vs spatial field-gradient max-cut

## Specific original statement and author attribution

**A. D. Ramírez-Galindo; H. A. Pérez-Olivas; G. Basurto-Islas; A. Hernández-Rayas; F. González López; T. Cordova-Fraga**, *Vortex magnetic induction: Mathematical, geometric and experimental characterization*, **Revista Mexicana de Física** **70** (2024), e030901, DOI [10.31349/RevMexFis.70.030901](https://doi.org/10.31349/RevMexFis.70.030901), original journal text readable via [SciELO full article](https://www.scielo.org.mx/scielo.php?pid=S0035-001X2024000300006&script=sci_arttext). Paper issue May/June **2024**; SciELO electronic carrier displays **22 September 2025**—the latter is *not* a new original independent publication or a 2025 experiment.

In §2, after the Biot–Savart setup, original **Eq. (7)** is `B = nabla × A`. The next sentence describes this as a calculation of the **magnetic-field gradient**. That is the authors' exact *local equation/prose relationship*, not our own physics theory. The original article further contains finite-element magnetic-field modelling, an actual multi-axis Hall magnetometer, a 12-pole approximation of a larger proposed winding, mapped 3D fields and separately proposed biological motivation; those claims and data must be evaluated on their own merits and original authorial record. Original Eq. (7) itself is a valid conventional vector-potential relation.

## Operator/dimension audit: original line contains a local interpretive ambiguity

Under standard SI classical electromagnetism (not exotic scalar or quantum-vacuum physics):

[
mathbf B = 
abla	imesmathbf A,quad
G_{ij}=rac{partial B_i}{partial x_j},quad
mathbf g = 
abla|mathbf B|.
]

- `A`: vector potential, dimensional unit **tesla metre (T·m)**.
- `curl A = B`: vector magnetic flux density, **T**.
- `grad B`: rank-2 spatial Jacobian, **T/m**.
- `grad |B|`: spatial gradient *of magnitude*, a different vector, **T/m**. At magnetic nulls `|B|=0` care is required with differentiability of the magnitude.

Thus printing **B = curl A** does **not**, *by that expression alone*, calculate either magnetic-field gradient. Differentiating B, or obtaining spatial differences from mapped fields, is an additional operator/data step. Original undergraduate electromagnetic source owners: [Oregon State University vector potential textbook](https://books.physics.oregonstate.edu/GSF/mtriangle.html), [Cornell electromagnetism lecture](https://quantum.lassp.cornell.edu/lecture/electric_and_magnetic_fields) and [Markus Zahn, MIT/LibreTexts §5.3](https://eng.libretexts.org/Bookshelves/Electrical_Engineering/Electro-Optics/Electromagnetic_Field_Theory%3A_A_Problem_Solving_Approach_%28Zahn%29/05%3A_The_Magnetic_Field/5.03%3A_Divergence_and_Curl_of_the_Magnetic_Field). These originally authored standard definitions are independent of our audit, **not** independent repeat measurements of the 2024 coil.

### Exact finite counterexample: the implication is mathematically invalid

Choose the affine classical vector potential `A(x,y,z)=(0,x,0)` in consistent symbolic coordinates (a physically dimensioned version scales the coefficient appropriately). Then

[

abla	imesmathbf A = (0,0,1) = mathbf B,qquad

ablamathbf B=0_{3	imes3},qquad

abla|mathbf B|=(0,0,0).
]

This nonzero spatially **uniform** B is a counterexample to identifying `curl A` with either field gradient. Adding the gradient of any quadratic scalar gauge `χ` (a symmetric Hessian) leaves B unchanged; no choice of gauge can make `B` automatically into its spatial derivative.

The [in-place research checker](../../scripts/check_psychotronics_rodin_2024_vector_potential_gradient.py) uses `fractions.Fraction` and the exact affine 3×3 coefficient representation. For any affine A, curl A is spatially constant and `grad B` is zero. Its source-written self-test enumerates **729** coefficient cases with x/y-dependence and four malformed potential/gauge cases. The **exact committed Python file** was copied into the local execution container and its `git hash-object` checked **identical to GitHub blob `14062ab66872d3d032e6da4d5fc4638c6d6258af`**; Python 3.13.5 `py_compile` passed and `--self-test` actually passed **733/733** cases (729 affine candidates + four malformed/gauge rejection cases). See [exact-byte run receipt](../receipts/PsychotronicsRodin2024Eq7ExactPythonRun20261027.txt). This is an actual executed finite mathematics receipt but *not* a dataset or Agda kernel result. Source-specific attribution guard `ramirez2024Eq7SourceWording` is added to existing `PsychotronicsSuccorSourceAtlasExact.agda`, with a finite one-dimensional affine derivative/curl demonstration in existing `PsychotronicsSuccorAttributionRegression.agda`. This is *source-written, not Agda kernel verified*, and the finite Nat model is **not** a continuum 3D differentiation kernel theorem.

## Scope and scientific conclusion

This exact defect is **an explanatory operator/category distinction**: if the authors intended Eq. (7) to be the gradient of B, the equation as printed is insufficient; if they only meant Eq. (7) as an intermediate step toward a mapped gradient, the wording is imprecise but subsequent differentiation may be valid. We **do not** infer that their Hall probe, FEM fields, Biot–Savart geometry, 2013/2024 printed numerical agreement, or biological reports are invalid.

The later 2024 paper **discussion** cites Saikia et al. 2019 ACS as its numerical ref [24] in an **up-to-60-percent Rodin-versus-Helmholtz** statement. The accessible **2019 publisher abstract** reports **15–38% less cellular toxicity for electric-field-treated Aβ peptides versus its unexposed condition**, and the exact original associated [WIPO PCT/IN2018/050452](https://patents.google.com/patent/WO2019012556A1/en) proposes **parallel aluminium EF electrodes**, not that 2024 coil. [Maldonado-Moreles et al. original 2021](https://pubmed.ncbi.nlm.nih.gov/33043710/) separately report **~86% less Aβ fibril formation versus their own control after 24h**, a distinct publication and comparator. The newly demonstrated Eq. (7) operator distinction does not pay the **still unseen original Saikia ACS full article/SI**, and none of the three percentages is interchangeable: denominators, physics intervention types and cell/peptide endpoints differ.

## Acceptance, stage and stopping frontier

- **Paid:** source-native 2024 equation/prose exact locator; classical operator/dimension distinction; reproducible rational 729-case affine counterexample; source-relative original scholarly authorship and separate finite formalisation declarations.
- **Unpaid:** numerical 2024 original measured 3D field-map bytes/metadata, full original 2019 ACS experimental comparator and SI, instrument-specific quantified derivative `grad B` with calibrated spatial uncertainty, Agda kernel on the current repository exact head, Agda kernel-checking and running physical data analysis; the exact 733-case Python suite has now been executed and hash-matched.
- **P2 design consequence:** a credible empirical coil *gradient* claim must specify `G_ij` or `grad|B|`, same calibrated spatial sampling grid, probe orientation, sensor position bias, interpolation/difference stencil, calibration and uncertainty in **T/m**. A field amplitude table in **mT** cannot alone validate a gradient comparison.
- **P3 severe test:** match biological outcomes and exposure fields (field magnitude **and** gradient) against actual Helmholtz/Rodin pair, sham, temperature, RF/acoustic and blinded assays before assessing reported device-specific 60% effects. Ethical/clinical safety gates apply to human or high-voltage work.
- **Stop:** without raw calibrated field maps, do not reconstruct a 2024 gradient or claim a new failure in empirical data. Without 2019 original main text, do not allege deliberate mis-citation. Do not treat conventional B or its derivative as proof of magnetic vortices beyond Maxwell, zero-point energy, scalar force, distant psychokinesis or therapeutic efficacy.

**Attribution:** the original researchers retain the published equations, observations and scientific hypotheses. The mathematical counterexample and source-specific critical comparison are DASHI-authored under Johl Brown's investigation with OpenAI ChatGPT assistance. The original textbook source authors retain their independent prior mathematical explanations. This is neither an independent remeasurement nor a clinical trial.
