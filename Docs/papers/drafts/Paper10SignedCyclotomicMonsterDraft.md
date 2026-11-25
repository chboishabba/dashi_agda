# Exact cyclotomic intertwiners for finite Heisenberg representations: signed polarization transport and Monster normalizer recognition

Working Paper 10 candidate — 2026-11-20. TOE #1217 mathematical owner. Not a submission.

## Abstract
We investigate exact polarization transport for the two nontrivial central characters of the finite Heisenberg group over F3 with six position coordinates. Dependent binary support/sign fibres, native 729-state charts and cyclotomic kernels encode selected source-derived symplectic and anti-symplectic transformations. The selected ATLAS 2.Suz:2 matrix action gives a mirror-adapted Fourier rotation and a rank-five chart change with 243 nonzero coefficients per row and column in the reported model. Full Monster multiplicity recognition is a distinct source-dependent problem. We specify complete character-table and quotient-descent acceptance conditions for it.

## 1. Signed geometry
Binary support identifies opposite trits; the full sign fibre is lossless. The support fibre of weight k has size 2^k, yielding 3^n=sum binom(n,k)2^k. Reuse BalancedTritBitFibre, the dihedral codec and native zeta54/729 BIDI maps. Cardinality equivalence does not establish action equivalence. The 3C residual comparison is distinct from the 3B recognition problem.

## 2. Selected Heisenberg and Weil model
For c((a,b),(a',b'))=b.a', use W_s(a,b,z)e_x=zeta^(s(z+b.x))e_(x+a). A similitude A with multiplier lambda has quadratic correction q(x)=2x^T(A^T C A-lambda C)x over F3. The selected source mirror has adapted form diag(I,-I); the rotation has off-diagonal blocks U,V with UV=-I and symmetric U,V. F_s(y,x)=zeta^(s y^T V x)/27 intertwines the generators and squares to parity. Paired conjugate phases give a D4 model. These instantiate standard Weil theory, not a novelty claim for the general theory.

## 3. Coordinate change
A=Pa^-1 P has reported upper-right rank5. The modulation vacuum and its translated columns give a sparse cyclotomic matrix with 243 nonzeros per column. Encode zero coefficients separately from root exponents. The normalization 1/[9(1+2 zeta^s)] has squared magnitude 1/243. See the TOE ledger and check_toe_atlas_mirror.py, check_toe_atlas_weil.py, check_toe_atlas_rechart.py. Exact dependency replay and independent composed-matrix regression remain outstanding.

## 4. Suzuki multiplicity selection
Under actual sector premises the multiplicity Hom_E(H_s,W_s) has dimension90. The faithful 12 plus faithful78 candidate has central C2 trace -90; the faithful 12 plus Sym²12 candidate has trace +66. Neither dimension nor central phase identifies the original selected 78. Reuse #1250 full-character selection at c6a86e955baead05eef8dfe1a1c0f22d5b81de41: 6.Suz restriction from 6.Suz.2, main-group inflation, exact decomposition, quotient MN3B descent, Monster occurrence. The 210-class 6.Suz audit matches all class values, complete class signatures, power maps, runtime versions and literal Irr indices. The original class20 quotient kernel matters. No actual output receipt recovered in this round. Finite-field quotient matrices do not specify the complex multiplicity representation.

## 5. Acceptance and scope
Canonical execution ledger: docs/superpowers/plans/2026-10-16-dashi-toe-universal-realization-ledger.md. Paper 8 cites the finite package; Paper 9 remains independent. Complete source selection, both actual linear Hom maps, actual mirror compatibility, pinned Agda acceptance, and literature novelty audit remain open. No physical realization claimed.

## References and attribution
Barraclough and Wilson (2007), DOI 10.1112/S1461157000001352; Nebe (2025), DOI 10.1007/s10801-025-01399-2; ATLAS/AtlasRep original matrices; DASHI #1098/#1250 source producers. JMD centralizer/North Star diagrams and smoothness observations; DASHI signed geometry and source transport; joint model/character comparison. Preserve Ibrahim and JFine source-specific ownership. Full bibliography and novelty audit pending.

## 6. Direct original-coordinate regression (2026-11-20)
The selected finite model now has a direct composed-matrix test, not just a conjugation proof. In the cyclotomic coefficient-pair basis (a,b) representing a+b*zeta, multiplication is (ac-bd,ad+bc-bd). Write k and f for the unnormalized positive-phase rechart and Fourier kernels. The rotation numerator is k† f k with denominator 243*27=6561; the positive-to-negative mirror numerator is -k^T k with denominator243 (the conjugate normalization has opposite sign). Verify all original-chart Weyl generator covariance equations, with each source multiplier and quadratic central correction. Local execution of check_toe_atlas_composed.py passed 25,509,168 entry comparisons and exact rotation parity, unitarity, mirror involution and dihedral equations. Original rotation has 729 nonzeros per column; original mirror has 81 (rank-four mixing), rechart 243 (rank-five mixing), adapted mirror one. This is a source-selected finite computational certificate and a candidate sparse transport case study, not a new general Weil theorem. Actual 90-dimensional Suzuki multiplicity action and original Monster linear Hom evaluation are still unrecognized; GAP/Nix absent locally, no authentic 210-class receipt or kernel check. Existing source authors and donor owners unchanged.

## 7. Affine support and exact quadratic generative reconstruction (2026-11-20)

Proposition (standard finite Heisenberg argument, source conventions): Let A=[[a,b],[c,d]] be an invertible symplectic similitude with multiplier lambda in F3*, and K an invertible intertwiner between nontrivial central phases s and s/lambda, using the canonical quadratic central correction. Transport of modulation eigenvectors implies that each column support is invariant under translations im(b). For t in ker(b), the transported modulation eigenvalue conditions impose affine linear constraints with normals d(t). By similitude covariance b^T d=d^T b, hence d(ker b) lies in (im b)^perp; injectivity of A on (0,t) gives dimension n-rank(b), so equality holds. Nonzero support then forces one whole affine coset. Translated columns have support y0+a*x+im(b). For a unitary intertwiner the coefficient modulus is 3^(-rank(b)/2), by unit-modulus translation covariance and column norm. This is classical mathematics specialized to the chosen polarization, not a novelty claim.

For the selected source models, choose independent columns B of b, write y=y0+a*x+B*t, and store a scalar gamma in Q(zeta) and a quadratic exponent Q(x,t). The generator program is obtained from exact coefficient samples at 0, e_i, 2e_i and e_i+e_j, then verified against EVERY coefficient position, including zeros. For a function quadratic over F3 these samples determine its coefficients; the exhaustive check is required and does not assume arbitrary matrices have this form. The scalar is the literal source entry at the chosen vacuum seed, not an uncontrolled projective identification. The conjugate gauge is fitted and checked independently. New local verifier scripts/check_toe_atlas_generative.py passed 4,251,528 coefficient positions (four selected operators, two phase gauges, 729 squared); all mounted dependencies replayed. Exact modulus checked in integer arithmetic by (g0²-g0*g1+g1²)*3^r=den². The measured compact JSON record sizes in bytes (positive/conjugate) are adapted mirror 287/297, original mirror 410/420, rechart 437/445, rotation 478/488. Baseline 531441 bytes for a one-byte-per-position expanded exponent array, excluding scalar metadata; this is a serialization comparison, not a universal compression optimum or complete MDL proof. Decoder code and source operator-generation costs are not included. The test reconstructs into dense matrices and does not yet implement a standalone serialized decoder or efficient matrix-free application. Rank and support size are distinct from description length. Existing signed-fibre/FRACDASH architecture is a motivation, not a demonstrated integration with that production codec.

## 8. Direct source-to-quadratic compilation and matrix-free execution (2026-11-20)
Let E=A^T C A-lambda C, q(v)=2v^T E v, and let L select independent columns of b, so B=bL and D=dL. For input central phase s and output phase s'=lambda*s over F3, choose the lexicographically first y0 satisfying d(t).y0+q(0,t)=0 for all t in ker(b). In the chosen vacuum gauge the transported modulation vector at y0+B u has exponent s'[q(0,Lu)+(D u).y0]. Transport of the input translation x gives the supported column y=y0+a x+B u and phase
Q(x,u)=s'[q(x,0)+q(0,Lu)+(D u).y0+(c x).(y0+B u)].
This directly specifies a quadratic polynomial from finite source matrices, without sampling or constructing a dense kernel. Global scalar is additional gauge data. In the selected ATLAS model, recover composed mirror and rotation gauge by streaming the prior chart and adapted rotation on a single vacuum vector, followed by the chart adjoint; the full dense oracle is imported only after compilation.
New standalone scripts/toe_cyclotomic_operator.py accepts JSON, validates ternary field shapes, independent support columns and scalar norm, and streams columns and forward/adjoint products using arbitrary-precision integer cyclotomic coefficients with a common denominator. This validation is structural, not a general certificate of unitarity or source provenance for arbitrary JSON. The current implementation enumerates position labels and kernel constraints and visits N*3^r supported terms per application, not a factored FFT. No dense matrix storage on the execution path. Local check_toe_atlas_direct_codec.py passed 4,251,528 entry positions (four operators, two phases), 8 forward and 8 adjoint vector comparisons, and replayed the prior source/Weil/rechart/composition tests. Exact committed dependency replay remains separate. Fast rank-r Fourier factorization, full two-part MDL, production FRACDASH integration, actual Suzuki selection and actual linear Hom recognition remain open. No new general Weil-theory novelty claim.

## 9. Factored C3 execution and the existing Hom recognition route
The C3 Fourier rows are already owned by TriadicDepthOneCharacters and C3FourierConjugationExact; MLKEMButterflyStageLocalityInvariantExact supplies a scheduling analogue, not ternary arithmetic. On each affine support block parameterize x=x0+Hv and y=y0+a*x0+Bw with independent columns H,B. The substituted exponent q(v,w) is quadratic, so q(v,w)=q(v,0)+q(0,w)-q(0,0)+w^T J v, with J the mixed coefficient matrix. When J is nonsingular (checked per block), input/output chirps and the frequency permutation w->J^T w reduce execution to r stages of unnormalized C3 butterflies. There are r*3^(n-1) butterflies across all blocks. The selected ATLAS ranks 0,4,5,6 passed forward comparison against existing streaming application in both phases on seeded integer vectors, with explicit normalized fixture gauges. Rank-zero empty-array types were corrected. The current planner still enumerates support cosets and is called per apply; no end-to-end complexity or speedup claim, and fast adjoint remains open.
The existing Monster Hom owner IbrahimMonster3BLinearMultiplicityHomSpaceExact and Nov8 Y443 constructive recognition note give P_x=3^-n sum_b zeta^(-s*b.x) M_b, S=P0 W, Phi(e_x tensor s0)=T_x s0, Psi(w)=sum_x e_x tensor T_-x P_x w. SymPy 1.14 check_toe_butterfly_hom_sympy.py verifies the elementary C3 quadratic-field identities, both phase projectors and two-sided 9-dimensional linear model evaluation. By the existing projector theorem the actual Weyl inputs would construct the actual evaluation; no actual Monster action is manufactured by the model. The source-selected Suzuki multiplicity and actual linear Hom instantiation remain open. SymPy is the exact algebraic verification route for this round, not Agda kernel acceptance.

## 10. Shared butterfly action on the multiplicity model
Given a recognized evaluation Phi:H_s tensor S_s -> W_s, a normalizer intertwiner on H_s and complementary action L on S_s induce Phi' (K tensor L) Phi^-1; the prime indicates the target phase recognition when the centre is inverted. This conditional expression uses the existing Monster3BMultiplicityEvaluationExact and IbrahimMonster3BLinearMultiplicityHomSpaceExact owners and their cocycle cancellation contract. It is not supplied by the identity multiplicity model.
For the selected finite model set L=I90 only. A state stores two integer cyclotomic numerator arrays of shape 729x90 with a common denominator. The cached plan stores immutable input/output indices, chirps and frequency permutations once per serialized operator. Forward action batches all channels through the existing C3 butterfly. Adjoint reverses the permutation and chirps, uses conjugate-Fourier via coefficient conjugation before/after the existing butterfly, and conjugates the scalar. Local mounted regression check_toe_hom_batch.py passed eight full forward-adjoint round trips on seeded 65,610-dimensional vectors and sixteen independent streaming comparisons of channels0 and89. Both phases and ranks0,4,5,6 tested, normalized fixture gauges. Cache hits9/misses7. Source matrix hashes replayed; exact committed dependency replay not asserted. The plan's first-build coset enumeration remains; no performance timings or actual Suzuki multiplicity matrices provided. Actual Hom source recognition remains open.

## 11. Nontrivial paired multiplicity consumer and character mismatch
The signed block recipe of jfine_3b_linear_multiplicity_d4_repair.py (blob 3ee81609e48df0b2e6aa23488c555d2a796f7f5b) gives S90=23A1+5A2+13B1+13B2+18E with character (90,18,2,18,18) in class order 1,r²,r,s,rs. Its preceding H6 permutation factor has character (729,81,9,81,81). Our selected ATLAS-derived adapted Fourier factor is different: diagonal exponent counts (261,234,234) give tr K_r=1, and parity has trace1. Hence the paired-phase, phase-preserving C4 tensor character in order 1,r,r²,r³ is (65610,2,18,2), not the previous JFine (65610,18,1458,18). The equal dimensions and abstract D4 laws do not identify their actions. A trace1458 half-turn cannot be obtained from a 90-dimensional unitary multiplicity factor and a Heisenberg half-turn of trace magnitude1. This conditional bound does not identify the actual Monster class; preserve the source class-fusion branch and prior residual no-go quantifiers.
The new check_toe_d4_complement.py uses the same signed recipe and existing cached batched executor, tracks both phase sectors explicitly, and applies signed channel permutations without expanded tensor matrices. Local mounted execution passed both full seeded 65610-dimensional tests: r^4=s²=1, srs=r^-1, rotation adjoint round trip, and opposite scalar gauge cancellation. SymPy exact D4 matrix and character checks and elementary phase cancellation passed. The opposite scalar test is a fixture, not a source-derived projective cocycle certificate. No actual Monster action or selected Suzuki 78 inferred. No GAP/Agda/CI; exact committed dependency replay remains separate.

## 12. Constructor-first extension geometry
The Heisenberg quotient action does not fix the scalar lift. If F²=P and F⁴=1, the alternative iF has square -P and order four. Over Q(zeta12), i and zeta3 coexist. For a plain linear phase swap, choose R+=iF+ and R-=-iF- to preserve the paired inverse relation; identical i gauges instead give an unwanted minus sign. This scalar change can be compensated by an inverse multiplicity gauge without changing the tensor action. It is not evidence that the original source chooses that gauge. SymPy exact Phi12 reduction verified the elementary three-point unnormalized algebra (with factors of 3) and enumerated the ordinary C4 spectra on dimension90: half trace -90 forces all eigenvalues ±i (91 possibilities), half trace66 gives 78 eigenvalues ±1 and 12 eigenvalues ±i (1027 possibilities). The existing conditional source gate links 4A/4C via 6E to faithful78/negative parity and 4D via 6B to C2-plus78/positive parity. Actual class fusion, quarter-turn characters, compatible scalar extension and full linear multiplicity identification remain open. Constructor-first policy: distinguish errors from omitted source/quotient/polarization/phase geometry before promoting an obstruction. The previous trace bound 90 remains valid for either parity sign under its stated independent tensor hypotheses.

## 13. Extended scalar orientation without rebuilding the butterfly
The field Q(zeta12)=Q(zeta3)[i] admits unique coefficient planes a+i b. A cubic matrix acts independently on both planes and multiplication by i maps (a,b) to (-b,a). The cached 729x90 consumer can therefore reuse its cubic arithmetic with 180 channels, grouping them into two 90-channel planes. Paired rotation gauges iF+ and -iF- and a linear phase-swap mirror preserve D4, whereas assigning i to both fails. Local check_toe_extended_batch.py executed both complete seeded 65610-coordinate extended-field vectors with exact integer numerators and denominators; negative parity, order four, adjoint, mirror and dihedral relations passed, and the wrong-gauge negative control failed as intended. The original mounted ATLAS source hashes were replayed. This test uses identity multiplicity and selected normalized adapted Fourier gauges, not a full source-derived Suzuki lift. The general quarter-turn phase trace is obtained by the three-term central projector formula, with all three actual class values retained. Existing Suzuki 2B quotient centralizer witness in JFine3BInvolutionNoGoAndLinearRepair20261024.md narrows the source route but does not authenticate the Monster class. Exact source receipt, actual multiplicity and Hom, production integration and Agda acceptance remain open.

## 14. Conditional extended multiplicity branch execution
Reuse the 6E/6B conditional source parity gate, not a new character selection. In the 6E fixture the 12 and 78 blocks have balanced eigenvalues +/-i; the multiplicity quarter trace is zero and half trace -90. In the 6B fixture the 12 block has balanced +/-i, while the 78 block has 45 +1 and 33 -1; quarter trace12 and half trace66. These chosen fixture spectra are illustrative only, not derived from actual quarter-turn class values. Combined with the corresponding Heisenberg parity -1 or +1, the half traces are90 or66. Apply diagonal multiplicity i powers as signed plane rotations on the existing Q(zeta3)[i] batch; use inverse exponents in the conjugate sector with a linear swapping mirror. Local check_toe_extended_multiplicity.py passed four full seeded 65,610-coordinate phase-vector regressions, including the full half-turn action, rotation order four, mirror and dihedral laws, and rotation adjoint. SymPy 1.14 verified the diagonal C4 characters. The actual source quarter-turn character is still missing; no actual Suzuki selection, full arbitrary extended matrix consumer, actual cocycle or Hom recognition is inferred. Mounted dependency replay only, no GAP/Agda/CI.

## 15. Conditional constituent discriminator

## Conditional C4 constituent split — 2026-11-20
Given prior-session candidate phase trace -6 for 4D/12F/6B and chosen positive Heisenberg gauge, assume actual S=U12+Sym²U12 and U12(r²)=-I. Writing chi_U(r)=it, t even in [-12,12], chi_S=it-(t²+12)/2 forces t=0. Same on C4 for dual Sym². Thus U spectrum 6i+6(-i), Sym² spectrum 36(+1)+42(-1). Independent local SymPy 1.14 enumeration of thirteen trace expressions executed; committed script not separately replayed. For faithful78 branch, total imaginary eigenvalue counts (44,46) or (42,48) permit thirteen splits with degree12 i-count 0..12; scalar saturation (0,90) requires both scalar, incompatible with a faithful attachment of a noncentral element. All numerical class inputs remain conditional pending independently authenticated full original character row and same-word class fusion. No class selected; no actual Hom, GAP, Agda or CI acceptance. Reuse existing all-conductor source matcher.

## 16. Attribution and current source-recognition boundary

### Standing attribution and evidence rules
- Preserve original mathematical authors, original publication, precise theorem/section/class coordinates where inspected, and source data authors separately from archive/mirror custody. Cite original papers before derivative transcriptions. Do not imply independent source corroboration when two locations reproduce the same table.
- Classical Stone–von Neumann/Weil, finite Fourier and ordinary character theory are inherited mathematics, not DASHI discoveries. ATLAS matrices and characters retain their original authorship (Conway, Curtis, Norton, Parker and Wilson, *Atlas of Finite Groups*, 1985, and the relevant later source authors); CTblLib is the maintained computational table source, not new authorship of every stored row.
- Original Monster subgroup/character roots: Norton–Wilson, *Anatomy of the Monster II* (2002), DOI 10.1112/S0024611502013357; Barraclough–Wilson (2007), DOI 10.1112/S1461157000001352; Breuer–Magaard–Wilson, *Some steps in the verification of the ordinary character table of the Monster group*, arXiv:2412.12182, 2024, especially the distinct auxiliary and diagonal quotients in section 9. Moonshine coefficient attribution distinguishes Conway–Norton and Ford–McKay–Norton from OEIS transcription.
- Gabriele Nebe, *Symmetrizations of quadratic and Hermitian forms* (2025), DOI 10.1007/s10801-025-01399-2, section 6: published irreducible Sym² of degree 12 giving degree 78; retain Nebe's result and underlying character-table attribution. Do not claim DASHI discovered it. Table row labels from a paper must not be silently identified with GAP Irr indices.
- JMD owns the supplied 3C and North Star diagrams and prompts; DASHI owns the origami residual and signed/ternary constructions; shared orbit-to-character and source joins are joint synthesis only insofar as both contribute. Do not attribute new independent mathematics to JMD, DASHI or a literature author by proximity alone. The 3C diagram is not a proof of the distinct 3B recognition lane.
- Repository reuse: #1250 at c6a86e955baead05eef8dfe1a1c0f22d5b81de41 owns original Suzuki character selection and quotient matcher; #1098 owns ATLAS source-word and field-chart donors; earlier JFine and Hom/phase owners retain their mathematical/implementation provenance. TOE #1217 consumes them. Reused code is not a new independent implementation claim. Keep exact paths/commits and original source citations.
- DASHI's candidate contribution here is the source-specific signed support/phase/orientation codec, exact factored execution and conditional source-attachment discriminators. Novelty audit remains OPEN. Distinguish identities, seeded model regressions, committed-source replay, kernel acceptance and actual source recognition. Constructor-first diagnosis is retained; genuine obstructions keep their explicit hypotheses.

### Current source-recognition cut — 2026-11-20
The official character-table catalogue entry https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/6.Suz.html is the lookup target for 6.Suz (order 2690072985600; 210 classes); previous session recovered metadata, not complete original rows. Alternate mirror retrieval reported HTTP 403. No new source receipt, code execution, or kernel acceptance is claimed in this documentation update. The existing scripts/monster_3b_suzuki_selected_character_join.py consumes the all-conductor exporter/audit and main quotient matcher and checks full class signatures, original Irr row positions, all class values, central orientations and character orthogonality; do not duplicate it. Metadata alone does not authenticate the rows or selected source element. Original quarter-turn values in section 15 remain conditional input data, not an independently authenticated table receipt.
If U12(c)=zeta^s I for the central C3 of 6.Suz, Sym² U12(c)=zeta^(2s) I and its dual has zeta^s I. Thus the same-character candidate is U12 + (Sym² U12)*, conditional on the actual diagonal-quotient centre placement, not a proof that the actual 78 is selected. On the previously constrained C4 branch the degree-78 eigenvalues are real ±1, so direct and dual spectra agree there; full character rows and quotient descent are necessary to distinguish them. Elementary central phase arithmetic is standard, not a new theorem claim.
Next acceptance sequence: (1) obtain original 210-class all-conductor export and same-runtime main-quotient selection receipt, (2) run existing full-character join locally and bind class/power coordinates and literal source word, (3) select actual 12/78 and central orientation, then attach complementary linear action and inverse cocycle to the existing exact butterfly/Hom consumer, (4) actual source Hom and kernel acceptance remain separate. No new fixture needed. M08/M09/M10d and actual M10f.7 OPEN; M12 novelty audit OPEN. Prior model PASS statuses unchanged.

## 17. Original producer closure and execution handoff

## 2026-11-20 original producer closure
Inspected complete non-truncated #1250 tree c6a86e955baead05eef8dfe1a1c0f22d5b81de41: relevant producer paths found, no completed source receipt identified in the targeted listing. The all-conductor export, main quotient matcher, JSON helper, selected character join and renderer already have identical donor/TOE blob IDs. Import the previously absent original rotation-class producer scripts/monster3b_atlas_suz2b_monster_4class_source_fusion.g by exact donor blob aadfad33b6a811a7b3c4697e5c04461332175e27, preserving ATLAS/Barraclough–Wilson and repository provenance. The earlier portable exporter is intentionally restricted to Q(zeta3); do not use it as full-source acceptance. Constructor-first: source field restriction is not a representation obstruction.
Local environment probe: GAP executable absent, DNS resolution failed for github.com, www.math.rwth-aachen.de and deb.debian.org. No actual GAP/Agda/CI run, no newly authenticated character row. Source acquisition remains OPEN. On a local checkout with GAP and CTblLib, create build/ and execute the three committed producers (all-conductor export, main quotient match, rotation-class source fusion); then execute the existing selected-character join and rotation receipt validator. Paths and commands below. A structurally accepted receipt is not itself runtime provenance or actual linear Hom recognition. Check the literal matrix word and diagonal centre orientation independently.
```sh
mkdir -p build
gap -q scripts/monster_3b_suzuki_all_conductors_export.g
gap -q scripts/monster_3b_suzuki_main_quotient_match.g
gap -q scripts/monster3b_atlas_suz2b_monster_4class_source_fusion.g
python scripts/monster_3b_suzuki_selected_character_join.py build/monster_3b_suzuki_all_conductors_characters.json build/monster_3b_suzuki_main_quotient_match.json --out build/monster_3b_suzuki_selected_character_join.json
python scripts/monster3b_atlas_suz2b_monster_4class_receipt_validator.py build/monster3b_atlas_suz2b_monster_4class_source_fusion.json --out build/monster3b_atlas_suz2b_monster_4class_validated.json
```
Commands are a reproducible handoff, not executed acceptance. M08/M09/M10d remain OPEN; no further model fixture added. Original authorship and source custody rules in preceding section apply.

## 18. User-local source receipt report and quotient-first subgroup recognition

## 2026-11-20 user-local original-source execution and odd-kernel quotient route
Evidence status: the user supplied a local execution report (not the actual JSON, patched source diff, or generated Agda certificate bytes in this session). Reported: 57 Monster Python tests passed in 4.73s (68 warnings); five-orbit screen ~4s, main quotient checker ~3s; source pair families 12a/b -> chi146 and 78a/b -> chi109 each occur with multiplicity one in restricted degree196883. Record as USER-REPORTED LOCAL PASS for pair-family occurrence, pending receipt ingestion, exact source replay and full all-conductor join. Do not mark individual phase orientation, diagonal kernel orientation, matrix action, actual D8 or VOA/Hom recognition paid. Source table authors ATLAS/CTblLib, normalizer authors Barraclough–Wilson and subsequent original contributors; user owns reported local implementation/debugging and execution. Preserve Nebe's original Sym² theorem separately.
Reported OOM root: AtlasRep Mmax7G0-f3r78B0 matrix group was sent into unassisted Size/SylowSubgroup; user reports permutation-only guard and IsAbelian predicate correction, stopped runaway processes, fail-closed atlas-group-realization-residual. No zero-risk resource guarantee. Reported rotation-class screen has 17 candidate fusion rows, 9 central half-turn Monster2A, 8 Monster2B, theta=(5,5,1,3,3)=3A1+B1+B2; all 17 compatible, none establishes realized subgroup. Reported 42B power bridge retained separately. Existing IbrahimMonsterN3BAdmissibleOOMConsumerRouteExact.agda at TOE blob f553f5ecba78510ee51801ac36f2794407e70093 explicitly proves declared-model factorization and ordinal route costs, not actual subgroup injection or existence. Live GitHub TOE head before update c54d2914 and donor #1250 c6a86e95; user-local changes not independently inspected or pushed by this documentation commit.
Exact quotient-first mathematical refinement (standard Schur–Zassenhaus, not DASHI authorship): for E=3^(1+12) normal odd-order kernel and Q=N(3B)/E=2.Suz.2, any 2-subgroup embeds under projection. For an actual order-eight dihedral subgroup of Q, its preimage has a complement isomorphic to that subgroup, conjugate by E. For any cyclic 2-subgroup of Q the same complement existence/conjugacy implies unique lift of each 2-element up to E-conjugacy; conjugacy in Q then lifts to conjugacy in N, so projection is a bijection on conjugacy classes of 2-power-order elements. The stored N->Q quotient class map, with order preservation filter, is therefore the appropriate exact inverse-class consumer. This does not construct explicit group words in N or prove actual linear action. The degree1782 permutation representation of Suz.2 loses the central C2 of 2.Suz.2; cannot automatically lift a D8 found there as D8. Need actual double-cover subgroup relations/extension data (a reflection may lift to order four), then inverse odd-kernel class map and intersection with literal 17 rows. Do not equate generic candidate fusions with realized subgroup classes. Prefer existing quotient producer and stored exact fusions, bounded resources, no ambient matrix Size/Sylow.
Acceptance sequence: ingest user-local patched producer/renderer/checker revisions and both actual JSON receipts plus generated certificate; run all-conductor export and existing selected character join on matched runtime and class signatures; report exact selected 78 C2/C3 and full Sym²/dual results, not infer them from 78a/b label. For quotient route recover actual 2.Suz.2 extension and D8, verify unique order-preserving inverse class coordinates and intersect the 17 rows. M08 pair-family occurrence user-reported PASS; independent receipt replay and selected full character identity OPEN; M09/M10d and actual M10f.7 OPEN. No new GAP, Agda, CI, or code regression executed in this documentation turn. 


## 23 November 2026 — P0 actual-Monster source-word intertwiner weld (master-based)

Reconciled current default `master`: PR #1250 remains **open**, branch
`research/jfine-3b-character-steelman-20261024` has diverged
(263 commits ahead and 99,812 behind at inspection, not an instruction
to force-merge it). Source-word class 5 -> Monster 4D, class centralizer
322,560 and original ATLAS basis receipt remain on the old PR head
`ea91ece6`, not all present on master. This work is intentionally
on a clean master-based branch, NOT on a guessed `main` branch.

**Original producer reuse:** the existing master script
`scripts/monster_3b_mmgroup_source_symplectic_basis.py` imports the
published literal MonsterSubgroups MM words (Dietrich, Lee, Pisani,
Popiel, 2026; source SHA c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2),
reconstructs the actual extraspecial E/Z(E) basis by checked
commutators, exports 12-column g3b/h3b matrices in its
`normalizer_lifts` manifest, and tests MMV(7) sector transport.
Its actual execution requires the mmgroup Python module, missing
from this local environment. Do not substitute a synthetic matrix
or claim that a manifest JSON alone authenticates original MM words.

**New first-class admission consumer**:
`scripts/monster3b_atlas_mmgroup_cross_source_intertwiner_gate.py`.
It imports the manifest and an *explicit named generator-word map*
C_ATLAS,D_ATLAS -> words in the actual g3b,h3b generators. It
reconstructs the original pinned ATLAS GF3 12x12 matrices and
checks SHA-256 of both original MeatAxe files; regenerates target
matrices by multiplying the actual source-image matrices in the
**supplied order**. Requires source outer multiplier for C = -1
and source inner multiplier D = +1, and C²=-I, D³=I on both
representations. It solves all 288 GF3 linear equations
C_ATLAS T = T C_M and D_ATLAS T = T D_M for 144 entries of T,
not separately chosen conjugators. For a one-dimensional
nullspace with an invertible basis, verifies exact simultaneous
matrix equations and the transported original alternating form
`T^t J_ATLAS T = scalar J_MM` with nonzero scalar.
Correct source J_MM from the original mmgroup producer has
lower-left +I, upper-right -I. Additionally checks strict
similitude laws and symmetric Heisenberg cocycle defects
`g^t C_c g - lambda C_c`, and derives their characteristic-three
quadratic central corrections. Even when all equations PASS,
the output is explicitly **ALGEBRAIC_CANDIDATE_ONLY**; the
original quotient-word identification and actual Monster Hom/VOA
promotion remain unpaid until source group words and quotient
isomorphism are independently checked.

**Automatic bounded discovery**:
`scripts/monster3b_atlas_mmgroup_bounded_word_search.py` enumerates
bounded distinct GF3 normalizer quotient matrices from the original
g3b/h3b source, retaining exact generator words and signed centre
multiplier. Filters C²=-I, D³=I, and (CD)^28=-I before solving
the simultaneous 144-entry intertwiner. Explicit depth, state and
pair budgets cause a fail-closed error rather than a false
non-existence theorem. A hit is a plausible original word
correspondence candidate, NOT a proved isomorphism of the Monster
group or phase module.

Local exact GF3 independent replay on original ATLAS matrices:
`C²=-I`, `D³=I`, common self-pair intertwiner nullity **1**,
swapped C/D nullity **0**, identity/identity target nullity **0**.
Source alternating form verifies
`C^t J C=-J`, `D^t J D=J` exactly. The master Agda module
`DASHI/Moonshine/Monster3BAtlasSymplecticBasisIntertwinerCompilerExact.agda`
has a strict `preservesPairing` field for
`RepositorySymplecticAction`; it therefore cannot instantiate the
actual outer C generator with multiplier -1 without **extending to
a source-correct similitude action and centre scaling**.
This is an exact type-level obstruction, NOT a new analytic
or group-theoretic theorem.

Synthetic bounded search using C,D themselves as deliberately
non-Monster stand-ins recovers one-letter C and D candidates.
This tests search plumbing, NOT actual Monster-source fusion.
Committed source and regression test files have been read back
from GitHub; the complete committed tests, actual GAP producer,
mmgroup 3B group words, and Agda compiler have **not** been
executed from the exact new branch in this runtime.
Only independent local GF3 calculations above are execution-supported.
No existing master source overwritten. No Galois, group inner
automorphism or matched character inference is used as a
replacement for generator identification.

**Next P0:** obtain original mmgroup manifest using its existing
producer, run bounded matrix-word search, replay each candidate
word as literal MM group elements against the published quotient
semipresentation and original central word, establish the exact
source isomorphism (not merely same matrix class), then certify
simultaneous T, form multiplier, cocycle, centre action, and
selected `H_zeta`/`W_zeta` representation action. Retain
12+78 selected character, central phase zeta vs zeta^2 and
actual Monster Hom gates separately. Do not promote source-
relative 4D class recognition into a basis-level group action.


## 23 November 2026 — user-local source replay and tightened cross-source filter

Follow-up report from the user's own local `/home/c/Documents/code/dashi_agda`
working tree: fetched PR #1250 up through `ea91ece6`; executed original
`monster3b_atlas_original_symplectic_basis_weld.py` with rank(J)=12,
one-dimensional common same-source intertwiner, both ATLAS D4 words,
similitude and cocycle; reproduced its 12x12 matrix receipt; executed
all **15/15** source-fusion contract regression tests; then regenerated
original GAP CTblLib fusion JSON and executed the source-word to
2.Suz.2 class 5 to Monster 4D driver. Its local printed result was
`PASS: SOURCE-RELATIVE ATLAS D4 WORD -> 2.Suz.2 CLASS 5 -> MONSTER 4D`.
Five original Monster focus test suites together gave **39/39 PASS**
(1.34s). These are **USER-REPORTED LOCAL EXECUTION receipts**,
not GitHub CI or independent execution by the current agent. The user
also edited the GAP script locally before its successful replay;
the modified local GAP bytes and generated JSON are NOT thereby
assumed pushed or identical to the old PR #1250 Git blob.
Do not claim that the current GitHub head's GAP script independently
passed without ingesting its corrected bytes and source receipt.

New original-relator strengthening on PR #1545:
`scripts/monster3b_atlas_mmgroup_cross_source_intertwiner_gate.py`
now checks the literal ATLAS source C,D semipresentation:
C²=-I, D³=I and D nontrivial, (CD)^28=-I, (CD)^56=I,
and exact order 7 for the source word
`cdcdcddcdd` where lower-case c,d mean inverse matrices.
The same *ordered inverse-letter* constraints are imposed on
a proposed Monster quotient generator pair. The bounded
word search filters by this original word before expensive
linear nullspace calculations. Its regression suite now includes
positive and negative original-relator tests (12 source-written
unittest methods). Independently reimplemented local GF3
source-matrix replay of original ATLAS literal m1/m2 bytes
confirmed all four key relations, including relator^7=I
and relator != I. This local proof is a necessary source
semipresentation filter, NOT sufficient to certify the
MonsterSubgroups generator-word map, quotient faithfulness,
full group isomorphism or Monster H_zeta/W_zeta action.
The new head's full Python suite and actual mmgroup work
remain unexecuted from pushed exact bytes in this runtime.

The existing master Agda compiler still wrongly types both
generator actions as strict pairing-preserving; the
ATLAS source outer generator C has multiplier -1.
Correct next proof interface requires
`omega(gx,gy)=lambda_g omega(x,y)`,
`z -> lambda_g z` and the symmetric cocycle defect and
quadratic correction, including negative- vs positive-phase
transport. Preserve original generator labels, residuals,
sign and zero modes. Avoid merging all historical #1250
branch changes wholesale into master.

P0 exact Monster-source gate remains: execute the original
`monster_3b_mmgroup_source_symplectic_basis.py` producer on
an mmgroup-equipped runtime, extract actual g3b,h3b
12D E/Z(E) matrices and original centre, find source-identified
ATLAS C,D generator words (bounded search only offers candidates),
replay literal MM group identities and original normalizer
quotient relations, then solve the *same* invertible 12x12
T over F3, transport J and cocycle, and attach the selected
zeta/zeta² phases. Neither Out=1, Monster class 4D nor a
one-dimensional ATLAS self-intertwiner pays this gate.


## 24 November 2026 — canonical endpoint/phase/lemma ownership

The living [Monster 3B endpoint-first roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md) is the authoritative phase and dependency ledger for **PR #1545**, mathematical endpoints E0–E4, phases P0–P6, and exact remaining lemmas **M3B-L01 through M3B-L13**. Read its 24-Nov top section over the older historical open-state prose below. The existing Ibrahim `IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact` already pays the **character/Clifford** (8748=729\cdot12, 56862=729\cdot78) half-degree decomposition; the still-open problem is **same-object characteristic-zero matrices and full normalizer/phase action** on actual (S_s=Hom_E(H_s,W_s)), not rediscovery of the constituent integers. Other already-paid inputs: authentic `mmgroup` (E/Z(E)) extraction from user-reported local source, 28 powered finite-field quotient hits, (3B) phase-dimension formula (65610=729\cdot90), and explicit symmetric Heisenberg cocycle correction. The simultaneous *full-group* (C,D) lift still requires source residual/kernel membership and coupled affine/central equations; the (S_s) operator and actual source class-to-word weld require original complex action and selected full 210-class character rows. Certification is P6, **after** endpoint solving.

## 23 November 2026 — ENDPOINT-FIRST 3B completion: cocycle elimination and actual 90D operator extraction

This section consolidates the source-selected 28 candidate quotient intertwiners, genuine user-reported `mmgroup 1.0.8` E/Z(E) extraction and GAP/CTblLib fusion with the **actual endpoint**. The mathematical reductions are documented in [Monster3BEndpointFirstConstruction20261123](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). No separate small acceptance script is required to continue the derivation; later full-group kernel/identity checks belong after the endpoint construction.

**Original-source sector dimensions are exact.** The original 3B weight-two source has dimension 196884 with trace 54 on both z and z². The central idempotents give dimensions (65664,65610,65610), so for nontrivial phase and E=3^(1+12), the actual Stone–von Neumann 729-dimensional irreducible has multiplicity **90**. This is an actual character consequence, unlike simply choosing a finite `Fin 90` set.

**Actual Heisenberg action of normalizer words is algebraically recoverable from the existing manifest.** For the source E group `(v,t)(w,u)=(v+w,t+u+c(v,w))`, with c=b.a', and quotient similitude A and phase multiplier lambda, the symmetric defect `E_A=A^T C A-lambda C` admits `q_A(v)=2v^T E_A v`. Its polarization is precisely the cocycle defect, regardless of symmetric-defect rank. The original manifest's twelve selected `translation_images/modulation_images` include central exponents `t_i`; they supply the **unique residual linear functional** `ell(e_i)=t_i-q_A(e_i)`, thus the actual automorphism `(v,t)->(Av,lambda*t+q_A(v)+ell(v))`. Composition of these polynomial automorphisms transports every powered candidate's **entire conjugation action on E**, not just its GF3 quotient; it still does not identify candidate group elements which act the same on E.

**Full lift equations as one joint obstruction problem.** Multiplying proposed Monster C/D lifts by E corrections parameterized by two vectors u,v and two centre coordinates does not change their quotient pair. For each relator, its E/Z(E) residual is an affine function `r+L_Cu+L_Dv` (twisted relator/Fox linearization). If, and ONLY if, its original full-group residual belongs to E, solving these equations leaves centre-valued quadratic constraints from the known Heisenberg multiplication. The system is simultaneous across all target relators and representative candidate classes. Exact original relator residues and proof of kernel membership are not in the 28-hits summary; therefore no particular C/D group extension is falsely declared solved yet.

**Actual 90D multiplicity action via a single Weil-vacuum column.** In characteristic zero, take `S_s=P_(0,s)W_s`, where `P_(0,s)=(1/729) sum_(b in F3^6) rho(B_b)` is the common modulation-fixed projector inside the original nontrivial-centre sector W_s. Define `P_(x,s)=T_x P_(0,s)T_x^-1`. The genuine linear evaluation and inverse are
```
Phi_s(e_x tensor u)=T_x u,
Psi_s(w)=sum_x e_x tensor T_x^-1 P_(x,s)w .
```
Let g normalize E and map phase s to s'=lambda^-1 s. Choose the already constructed original-source Weil transport `K_g:H_s->H_s'` with `K_g e_0=sum_x k_x e_x`. By the E intertwiner/Schur argument, `Phi_s'^-1 rho(g)Phi_s=K_g tensor L_g`. For ANY x with `k_x != 0` and EVERY `u in S_s`,
```
       L_g u = k_x^-1 T_x^-1 P_(x,s') rho(g)u .
```
This extracts the actual multiplicity action from **one Weil vacuum column**, the original g action, and a modulation weight projector, without constructing a dense 65610-dimensional tensor matrix. The extraction acts between S_s and S_-s when lambda=-1; the source's outer anti-symplectic C must not be typed as an S_s endomorphism. The reciprocal gauge freedom `K_g -> alpha K_g`, `L_g -> alpha^-1 L_g` is retained and fixed jointly by original source relators. Finite-field GF3 matrix T and authentic MMV(7) phase samples alone do not supply the required complex rho(g) on W_s.

**Character/constituent selection is independent.** For any phase-preserving g, the actual `chi_(W_s)(g)=(1/3) sum_j zeta^(-s*j) chi_W(z^j*g)`; then `chi_(W_s)(g)=chi_H(K_g) chi_(S_s)(L_g)`. Character division requires chi_H(K_g) != 0; otherwise use the projector extraction. The original GAP 210-class rows and exact fusion are the correct source for distinguishing faithful 12+78 from 12+Sym²12. An outer phase swap has no separate ordinary trace on a single W_s. Neither the dimension 90 nor a quotient GL12 conjugacy determines this constituent.

**Endpoint scorecard, not a certification checklist:** the symmetric-cocycle correction and full actual E automorphism reconstruction formula are mathematically DONE from manifest coordinates; the characteristic-zero 90 sector DIMENSION and Hom evaluation/inverse are structurally DONE; simultaneous Monster group lift and original characteristic-zero g action remain the two specific SOURCE INPUTS preventing a fully numerical 90D operator and selected class/constituent. Finish those mathematically first; only then batch final verification. No invented full-group equality, class selection, original complex 90D matrix, or Monster VOA endpoint.


## 24 November 2026 — actual 90D multiplicity operators are Hom-functorial, with canonical 12+78 source projectors

The [complete same-object mathematical construction](../../physics/Monster3BActualHomMultiplicityCharacterProjectorEndpoint20261124.md) now supplies the canonical P3/P4 endpoint **formula**, with the [living L01–L13R roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md) remaining the owner of source attachments. It uses the existing Barraclough–Wilson extension of the \(729\)-dimensional extraspecial representation to the phase-preserving inertia, rather than manufacturing a synthetic 90D representation.

Let \(W_s=P_sW\) be the **actual original characteristic-zero Monster** central-phase eigensector; \(H_s\) is the genuine \(729\)-dimensional Stone–von Neumann irreducible of \(E=3^{1+12}\). Set \(S_s=\operatorname{Hom}_E(H_s,W_s)\), so \(\dim S_s=90\), with \(\Phi_s(h\otimes f)=f(h)\). For any original inertia element \(g\), and the **same-source** ordinary extension \(K_s(g)\) of the Heisenberg action, define
\[
(L_s(g)f)(h)=\rho_W(g)f(K_s(g)^{-1}h).
\]
This is an honest \(90\)-dimensional representation of the chosen phase-preserving inertia on the actual Hom carrier, with exact
\[
\rho_W(g)\Phi_s=\Phi_s(K_s(g)\otimes L_s(g)).
\]
The source-selected 729D phase-changing outer action instead maps \(S_s\to S_{-s}\); do not type it as an internal same-phase operator.

For an actual modulation subgroup \(B\), the canonical fixed-vacuum realization \(S_s\cong \Pi_{0,s}W_s\), with \(\Pi_{0,s}=729^{-1}\sum_{b\in B}\rho_W(b)\), gives an exact matrix-free recipe. If \(K_s(g)e_0=\sum_x k_xe_x\) and \(k_x\ne0\), then
\[
L_s(g)u=k_x^{-1}T_x^{-1}\Pi_{x,s}\rho_W(g)u
\quad (u\in \Pi_{0,s}W_s).
\]
One nonzero Weil-vacuum column suffices. Independence of \(x\) follows from the actual tensor intertwining property.

The existing Ibrahim phase-resolved character weld **already pays the original character-level 12+78 split**. After identifying the just-constructed \(S_s\) action's *same-object* 210-class character with the source \(\chi_{12}+\chi_{78}\), the two central idempotents
\[
e_a=\frac{\chi_a(1)}{|Q|}\sum_{q\in Q}\chi_a(q^{-1})L_s(q),\quad a\in\{12,78\},
\]
on the correct source phase-preserving quotient/extension \(Q\) give the **genuine** invariant direct sum \(S_s=\operatorname{im}e_{12}\oplus\operatorname{im}e_{78}\) and the constituent operators by restriction. Group/central extension is mandatory: a projective \(L_s\) needs its correct extension, not an idempotent in an incorrectly chosen quotient algebra.

**Endpoint solution vs missing source data:** the actual-Hom operator and constituent-projector construction are mathematically explicit, but the full original characteristic-zero \(\rho_W\) on the selected words, honest compatible \(K_s\) gauge, exact 210-class same-object equality, and the simultaneous full Monster C/D group-extension residuals remain necessary for numerical matrices and the final source-identical Paper 10 action. Reuse the existing 28 candidate quotient witnesses, authentic mmgroup manifest and GAP/CTblLib machinery; do not initiate another certification cycle.

## 24 November 2026 — direct original-normalizer idempotents solve the actual 12+78 Hom subdivision

[Full source-rooted mathematical theorem](../../physics/Monster3BActualNormalizerIdempotentSameObject1278Endpoint20261124.md) · [living phase/lemma and producer/consumer ledger](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). The existing original Monster normalizer restriction and Ibrahim phase/Clifford occurrence make the **same-object constituent subdivision mathematically constructive without first computing the unknown 90-dimensional class character**. Source assumptions remain explicit.

Let \(N\) be the original full \(3B\)-normalizer source group and \(W=\mathbf1\oplus V_{196883}\) the actual complex Monster weight-two representation restricted to \(N\). Breuer–Magaard–Wilson/An–Wilson/Ibrahim identify the multiplicity-one four-constituent degree multiset
\[
143+17496+65520+113724=196883,
\]
with the \(17496=2\cdot729\cdot12\) and \(113724=2\cdot729\cdot78\) summands the original *nontrivial-centre paired* character families. **Degree arithmetic alone does not fix characters or a chosen group embedding:** here \(\theta_{17496},\theta_{113724}\) are the actual source irreducible character rows on the same \(N\) as \(\rho_W\).

Define the *actual-normalizer* central idempotent operators
\[
E_d=\frac{d}{|N|}\sum_{g\in N}\theta_d(g^{-1})\rho_W(g)\qquad(d=17496,113724)
\]
and the phase idempotents \(P_s=3^{-1}\sum_{j=0}^{2}\zeta^{-sj}\rho_W(z)^j\). Since \(E_d\) is central in \(\mathbb C[N]\), \(E_dP_s=P_sE_d\), even when the outer normalizer inverts z. The genuine outer involution exchanges the \(\zeta\) and \(\zeta^2\) sectors within each of the source-paired \(\operatorname{im}E_d\) without producing a central-zero summand. Thus
\[
\operatorname{rank}P_sE_{17496}=8748,\quad
\operatorname{rank}P_sE_{113724}=56862,\qquad s=1,2,
\]
and the literal source subspaces \(W_{a,s}:=P_sE_{d_a}W\) sum to the entire actual \(W_s\).

Now apply the ORIGINAL Heisenberg \(H_s\) and the Hom functor:
\[
\boxed{
S_{12,s}=\operatorname{Hom}_E(H_s,W_{12,s}),\
S_{78,s}=\operatorname{Hom}_E(H_s,W_{78,s}),\
S_s=S_{12,s}\oplus S_{78,s}.
}
\]
Stone–von Neumann gives dimensions \(12,78,90\) without ever identifying an arbitrary \(Fin90\) basis with actual Monster states. Source inertia extends the \(729\)-module with the authentic \(K_s\); each original operator is already mathematically defined via
\[
(L_{a,s}(g)f)(h)=\rho_W(g)f(K_s(g)^{-1}h),
\]
and the outer generator takes \(S_{a,s}\to S_{a,-s}\). The earlier one-vacuum-column formula applies blockwise. **These are actual-module operator formulas** defined on the original \(W\), not numerical matrices computed in a specified basis.

This resolves the previous unnecessary order of obligations: the selected \(6.\mathrm{Suz}\) 210-class \(\chi_{S_s}\) comparison is no longer required *to locate the subspaces*, because the genuine \(N\)-projectors already find them. It remains required for exact original class labels, central signs, scalar gauge and matching ATLAS C/D candidate words to actual Monster classes. The full coherent Monster group extension relators and source-labelled complex normalizer matrices are still open mathematical endpoints, not mere certification. Generic characters and abstract finite-field matrices do not supply those selected same-object words.


## 24 November 2026 — source normalizer is a CENTRAL PRODUCT, not a split 2.Suz:2 lift

[Mathematical proof of full source group-cover and relative character reduction](../../physics/Monster3BNormalizerCentralProductRelatorDescent20261124.md) · [updated canonical P2/P4 roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). The original Barraclough–Wilson main group is the split \(E\rtimes6.\mathrm{Suz}.2\), whose published diagonal class-20 \(C_3\) quotient is the Monster \(3B\) normalizer \(N\). Its genuine injected \(6.\mathrm{Suz}.2\) complement-image \(H\) satisfies \(N=EH,\ E\cap H=Z(E)\), and \(N/E\cong2.\mathrm{Suz}:2\). **Thus all quotient-relator words of a jointly chosen source H pair lie in the original \(Z(E)\) automatically.** Requiring every full 2.Suz:2 relation to be identity in the source \(6.\mathrm{Suz}\) cover would be wrong (the central C3 cover is nonsplit). Only matching the actual MM Hit0 words to the source lifts and their prescribed central \(C_3\) scalars remains at P2, not a universal group-extension existence theorem.

For known quotient order-four C, \(C^9\) is an exact order-four lift because E has exponent three. The original D order-three ATLAS matrix instead has Jordan type \(3^2 2^2 1^2\), so an arbitrary candidate has a possible 4-dimensional vector obstruction \(\ker(D-I)/\mathrm{im}(D-I)^2\); this automatically vanishes **for genuine N word lifts** because the source H provides a lift with cube already in \(Z(E)\). The remaining central C3 cube is part of the cover and must not be discarded.

The source diagonal descent constraint is \(s+\epsilon(u_s+k_{12})=s+\epsilon(u_s+k_{78})=0\pmod3\), where \(u_s\) is the genuine central scalar of the source 729-extension; hence 12 and78 must share the same Suzuki central C3 phase. The one-class ratio of original source paired character values at the lifted order-two Suzuki central involution is \(+13/2\) for faithful78 and \(-13/2\) for symmetric-square78, independently of the 729-Weil trace/gauge. The original GAP source already owns this exact class/character family selection; no sign is invented without the genuine selected source result. This construction works **on the actual 12+78 Hom subspaces** already defined by prior N-idempotents; it does not assert an unproduced numerical complex Monster matrix.


## 24 November 2026 — GAP class-20 exact descent and signed original 3B Fourier phase

[Canonical derived theorem](../../physics/Monster3BGAPClass20DoubleC3FourierDescent20261124.md) and [updated seven-phase roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). The published main table has TWO distinct normal order-three objects: diagonal quotient K = original class20 \(C_3\) and extraspecial \(Z(E)\) = true 3B centre. The source main→MN3B kills the former and preserves the latter. For any irreducible main-table character \(\chi\), K-normality and conjugacy of its two nonidentity elements give \(\operatorname{rank}\Pi_K=(\chi(1)+2\chi(k))/3\in\{0,\chi(1)\}\). Thus original diagonal descent is **equivalent** to the ONE-CLASS condition \(\chi(k)=\chi(1)\), while K-nontrivial outer-paired components have \(\chi(k)=-\chi(1)/2\). Applying this *before* full character matching to the existing \(1458\times24\) and \(1458\times156\) products identifies one descended source component for each selected family: class20 traces (17496,-8748) and (113724,-56862) respectively. The full original MN3B→Monster character comparison remains the same-object group/representation selector.

For each *descended* character the distinct extraspecial 3B-centre trace is \(-d/2\), hence there is no z-trivial part and its \(\zeta\) and \(\zeta^2\) subspaces each have dimension \(d/2\). The original **signed phase operator** \(P_+-P_-=(\zeta^2-\zeta)(\rho(z)-\rho(z^2))/3\) is negated by the outer normalizer involution, while \(P_++P_-=(2-\rho(z)-\rho(z^2))/3\) is fixed. **The ordinary outer character by itself cannot canonically orient a/b and \(\zeta/\zeta^2\)**. Preserve the marked central element and original source class-word gauge. This is a mathematical analogy to the signed descent in the user's attached Langlands source, NOT an arithmetic Galois-to-Monster identification.

The correct diagonal scalar equation remains \(s+\epsilon(u_s+k_a)=0\bmod3\), retaining the central scalar \(u_s\) of the original 729 Weil extension; hence the selected 12 and 78 must use the same Suzuki central C3 phase. The original GAP producer now enforces two matched conjugate pairings and cross-checks exact class20 trace descent against **the pre-existing full 210-class character matcher**. No source CTblLib execution, numeric 78-selection, or original complex same-object operator has been asserted in this update. Original source attribution: Barraclough–Wilson, Bray–Wilson, BMW, CTblLib; user attached Langlands is mathematical analogy only.



## 24 November 2026 — authentic GAP selects nonfaithful Sym²78 and uniquely identifies source 4D

**This supersedes all earlier conjectures that the actual Monster chooses the faithful degree78.** The user-executed original GAP 4.16dev/CTblLib 1.3.11 main/Fusion sources both passed \`EXIT_0\`, reporting \`MAIN_AND_FUSION_SOURCE_MATCHED\`. The source-to-endpoint theorem and raw receipt checksums are recorded in [Monster3BGAPSelectedDualSymSquare12To90Endpoint20261124](../../physics/Monster3BGAPSelectedDualSymSquare12To90Endpoint20261124.md) and the [living P0–P6 roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). The raw original main JSON was not mounted here; the results below reproduce the user's supplied authentic run report rather than claiming independent source execution.

Original \`6.Suz\` faithful12 Irr153/154 (\`\\chi_{115}\` pair) and **selected 78 Irr79/80** (\`\\chi_{78}\` pair) are exactly **Nebe nonfaithful Sym²12/direct-dual family** by the original complete 210-class character comparison. Their selected degree90 central \(C_2\) trace is **+66**, not -90, and there are exactly two Suzuki central-C3-compatible 12/78 pairings. The 12 and 78 source products descend from original main Irr327/253 into MN3B Irr146/109 with Monster occurrence one apiece; the original diagonal K is main class20 (distinct from E-centre class2).

The important new *marked-phase* consequence is
\[
\boxed{S_s|_{6.\mathrm{Suz}}\cong V_{12,s}\oplus\mathrm{Sym}^2(V_{12,s}^{\vee}).}
\]
For a genuine complex faithful \(6.\mathrm{Suz}\) 12D generator matrix \(A_g\), the full source 90D inner operator is equivalent to
\[
\boxed{L_s(g)\sim A_g\oplus\mathrm{Sym}^2((A_g^{-1})^\top).}
\]
The **dual** is required: direct \(\mathrm{Sym}^2V_s\) reverses the nontrivial central C3 scalar, while dual Sym² retains the same one. The full-character source equality and two same-C3 pairings establish this within each unoriented conjugate sector; the absolute \(\zeta/\zeta^2\) orientation and original word-specific source matrix are not supplied by ordinary unmarked characters.

The central \(6.\mathrm{Suz}\) order-two source element acts on the actual multiplicity Hom space by \(J_s=L_s(t_2)\), spectrum \((-1)^{12},(+1)^{78}\), trace **66**. Thus **two operators suffice** to define the actual \(12/78\) Hom-block projectors:
\[
\Pi_{12,s}=\frac{I-J_s}{2},\qquad \Pi_{78,s}=\frac{I+J_s}{2}.
\]
Do **not** apply these to \(W_s\) before removing the original \(729\)-dimensional Heisenberg/Weil factor. The original N group-algebra idempotent construction remains valid, but the actual selected central involution now provides the smaller projection.

The **original source four-class ambiguity is paid**: stored \(2.\mathrm{Suz}.2\) class 5→\(6.\mathrm{Suz}.2\) class 9→main class54→MN3B class33→Monster class10 selects **4D**, uniquely for the original class with the specified square-to-2B criterion. This is not the same as identifying user-local \(C=(g_{3B}h_{3B}^{-1})^{15}\) or another of the 28 quotient candidates as that original Monster 4D group element.

**Paper 10 remaining actual operator endpoint:** obtain the complex faithful 6.Suz 12D standard-source matrices with correct \(6.\mathrm{Suz}.2\) cover scalar and actual Monster word/Hom realization; match the user-local MM words to those source elements and selected original 4D class. Then reconstruct the 78/90 action through the dual-Sym² construction and original intertwiner, preserving outer phase exchange and full central-cover relations. There is no remaining independent selected-78 family or source 4-class search. Formal certification deferred.


### P5 source found: original ordinary complex faithful 6.Suz 12D

Allan Steel's [Ordinary Representations Database](https://magma.maths.usyd.edu.au/~allan/reps/db/) lists an actual faithful degree-12 **characteristic-zero** \(6.\mathrm{Suz}\) representation over a character field of degree two, Schur index one, with linked original Magma file [\`d12.6Suz.nfdeg2.M\`](https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M). This is the correct original-source direction for the **matrix** \(A_g\) in \(V_{12}\oplus\operatorname{Sym}^2(V_{12}^\vee)\), distinct from finite ATLAS or characteristic-3 quotient representations. Because its faithful central \(C_3\) character contains \(\zeta_3\), the degree-two character field is exactly \(\mathbb Q(\zeta_3)\); Schur index one permits the genuine 12D model there, and the dual-symmetric-square 90D inner action remains over that same field.

Only the external listing and linked file have been verified; the \`.M\` matrix bytes and standard-generator words have **not** been retrieved in this session. The **remaining endpoint** is source generator/field alignment to the GAP-selected 12a/b full-class rows and the authentic \(6.\mathrm{Suz}.2\)/Monster-normalizer action, then original 12D Hom intertwiner and outer phase. No unobserved Magma/GAP execution or original complex matrix is claimed.


## 24 November 2026 — P5 exact ordinary-field one-source construction (Steel 12 → dual Sym²78 → 90)

The original GAP source result is now much stronger than merely an abstract \(90=12+78\) split. The Monster-selected \(6.\mathrm{Suz}\) family is faithful12 Irr153/154 and nonfaithful **Nebe dual-Sym²78** Irr79/80 (selected central C2 trace \(+66\), same central-C3 phase), and the published source order-four class fuses uniquely to **Monster 4D**, though no particular MM word has been identified as that source element. Using the original full character equality, the *marked phase* inner representation is of genuine \(6.\mathrm{Suz}\) type
\[
\boxed{S_s|_{6.\mathrm{Suz}}\cong V_s\oplus\mathrm{Sym}^2(V_s^\vee).}
\]

**All 210 class-character values from one original 12D row.** The faithful12 character \(\chi_s\) is valued in \(K=\mathbb Q(\zeta_3)\), with nontrivial field automorphism \(\sigma\). For each original \(6.\mathrm{Suz}\) source class \(g\), ordinary symmetric-square theory gives the exact source identity
\[
\boxed{\chi_{90,s}(g)=\chi_s(g)+\tfrac12\left(\sigma(\chi_s(g))^2+\sigma(\chi_s(g^2))\right).}
\]
The existing source \`PowerMap(six,2)\` and selected 12 full-class row determine this **without** any new 78D matrix, 90D character search or generic test loop. The absolute \(\zeta/\zeta^2\) label is still marked by an actual source central generator, not an unmarked outer table.

**Entire inner generator action over one explicit quadratic field.** Steel's ordinary [faithful \(6.\mathrm{Suz}\) degree12 source](https://magma.maths.usyd.edu.au/~allan/reps/db/) with [original Magma file](https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M) has character-field degree 2 and Schur index 1. Its faithful order-three centre provides \(12\zeta_3^{\pm1}\), identifying its minimal field as **\(K=\mathbb Q(\zeta_3)\)**. For any genuine source matrix \(A_g\in GL_{12}(K)\), the whole selected inner multiplicity operator is obtained **exactly and functorially** in a coherent source basis:
\[
L_s(g)\sim\mathrm{diag}\big(A_g,\mathrm{Sym}^2((A_g^{-1})^{\top})\big)\in GL_{90}(K).
\]
The explicit \(78\times78\) polynomial-basis entry formula is given in [the complete P5 mathematical max-cut](../../physics/Monster3BSteelOrdinary12Exact90SourceAlignmentMaxCut20261124.md) and is implemented in [\`scripts/monster3b_steel_ordinary12_to90.py\`](../../scripts/monster3b_steel_ordinary12_to90.py). The exact one-involution projections on the actual \(90\)-dimensional Hom carrier remain \(\Pi_{12,s}=(I-J_s)/2\), \(\Pi_{78,s}=(I+J_s)/2\), not operations on the full 65610D original phase sector without the 729 Weil factor.

**Boundary precisely retained:** our web/runtime cannot fetch the raw Steel \`.M\` contents (unsupported content type / DNS inaccessible). The original module variable, generator matrices, number-field embedding and corresponding standard group words are therefore **not claimed discovered**, and the source script's \`--acquire\` records the original attribution/SHA and a local inventory without executing Magma source as Python or claiming license to vendor it. The subsequent \`--matrix-json\` exact-field operator stage requires a genuine source-normalized 12D export and labels original GAP class, Monster MM word and actual Hom intertwiner as unverified until the corresponding original actions and 729 Weil gauge have been attached. **Mathematical construction is solved; same-object source-word realization remains open.** Remaining M3B-L10A original 12D module/generator/field alignment; M3B-L10B actual Monster Hom and source C/D group-word transport; M3B-L12R outer phase/gauge. No new proof/certification stage is added.


## 24 November 2026 — P5 unified source implementation for genuine C/D, Steel ordinary12 and actual MMV31 Hom

The original mathematical P5 construction \(V_s\oplus\operatorname{Sym}^2(V_s^\vee)\) is now accompanied by a [single source-first workstation handoff](../../physics/Monster3BP5WorkstationSourceIntegration20261124.md) and [checkpointed runner](../../scripts/run_monster3b_p5_endpoint.py), not another isolated certification loop. The already user-paid original GAP/CTblLib result selects faithful complex \(6.\mathrm{Suz}\) Irr153/154, **nonfaithful Nebe dual-Sym²78** Irr79/80, actual Suzuki \(C_2\) trace **+66**, 12/78 common \(C_3\) phase and **source Monster class4D** (the literal selected MM word still unproven).

**L10A source:** [Steel Magma GModule exporter](../../scripts/monster3b_steel_magma_export.py) reads Steel's real original \`d12.6Suz.nfdeg2.M\` with genuine Magma \`Representation(M)\`, gives exact \(\mathbb Q(\zeta_3)\) 12D generator matrices and group-word order/trace fingerprints; [GAP match](../../scripts/monster3b_gap_ordinary12_class_fingerprint.py) returns **all** original 210-class candidates for both faithful12 Galois orientations, without inventing a standard-generator or absolute-\(\zeta\) identification. Source \`.M\` bytes remain uninspected in the present assistant runtime and will be executed on the user's workstation.

**L10C code-complete mathematical output:** [exact Qζ source matrix functor](../../scripts/monster3b_steel_ordinary12_to90.py) constructs literal \(L_{78}=\operatorname{Sym}^2((A^{-1})^\top)\), \(L_{90}=A\oplus L_{78}\) and all source-character trace formulae from one actual Steel faithful12 generator matrix. Null 153/154 orientation is allowed until the source GAP word/class map is fixed.

**L10B original MM and true modular carrier:** [actual-mmgroup canonical lift](../../scripts/monster3b_mmgroup_canonical_cover_words.py) constructs corrected original full-Monster \(C,D\) words and **all** central-cover residues by solving the 12-coordinate extraspecial affine obstruction, rather than demanding false split \(2.\mathrm{Suz}:2\) literal identities. In addition [the genuine \`MMV(31)\` B-vacuum extractor](../../scripts/monster3b_actual_mmv31_hom_projector.py) can produce 90 independently checked **original 196884D Monster-mod31** projected vectors using \(P_{\zeta}P_B\). Its optional \(C^2\) source action can split the true mod31 90D into 12/78 C2 eigenspaces, and the phase-preserving \(D\) vacuum sandwich yields a projective 12D block if nonzero. This is **mathematically meaningful original-source modular evidence, NOT characteristic-zero Monster \(\operatorname{Hom}\)**. Only a real char0 \(W_s\) action or rigorous same-object lifting can pay the literal 12D source-to-Hom intertwiner.

**L12R outer/word-cover construction:** [the exact Qζ intertwiner solver](../../scripts/monster3b_ordinary12_hom_outer_weld.py) accepts an authentic original-source \(\alpha\) map on standard \(6.\mathrm{Suz}\) generator words and an original **characteristic-zero** Hom12 action, solves \(F A_g=B_gF\), \(U\sigma(A_g)=A_{\alpha(g)}U\), and derives paired outer \(U_{12}\oplus\operatorname{Sym}^2((U_{12}^{-1})^\top)\) and all outer-square central phases. Without those source inputs, it emits a **missing source/conditional** status. A quotient GF3 intertwiner or MMV31 modular B-vacuum does not establish a characteristic-zero \(W_s\) intertwiner, nor that a user-local corrected \(C\) is literally source class 4D.

**Priority after user's workstation run:** use the one run's authentic Magma/GAP original-generator and MM exact central-residual data to solve the final **same-element standard group-word/Hom/Weil scalar weld**. There is no remaining separate faithful-vs-Sym²78 search, 90D family mystery or abstract group-cover existence obligation. Formal kernel certification is after mathematics; original authors Steel, Barraclough–Wilson, Bray–Wilson, Nebe and Dietrich–Lee–Pisani–Popiel retain attribution.


## 24 November 2026 — reported authentic MMV31 12/78, exact R7=z cover and signed inner generator basis

The user executed the integrated P5 workstation source on the original \`mmgroup\` 1.0.8 Monster word/196884D vector module, obtaining \`EXIT_0\` from both the **full-group canonical cover** and **actual \`MMV(31)\` B-vacuum** stages. The source receipts are described with a strict user-reported versus independently accessed boundary in [Monster3BP5ActualSourceRunRelatorAndMMV31](../../physics/Monster3BP5ActualSourceRunRelatorAndMMV31_20261124.md); the original NPZ files and JSON remain on the workstation and were not inspected byte-for-byte in this session.

For actual corrected Monster \(C,D\), the report states
\[
\boxed{C^4=D^3=(CD)^{56}=1,\qquad C^2=(CD)^{28}.}
\]
For the original ten-letter quotient relator \(R=cdcdcddcdd\), with lowercase denoting inverses, the ACTUAL source has \(R^7=z_{3B}\ne1\). Since \(R\) has order seven modulo \(Z(E)\), its actual order is **21**, giving a concrete retained central-cover residual. This is NOT an obstruction to the published \(2.\mathrm{Suz}:2\) quotient, nor does it alone prove nonsplitting of the entire extension. **Do not assume \(z_{3B}\) commutes with \(C\)**: the source action inverts it. For all central rephasings \(C'=z^aC,D'=z^bD\), the **SIGNED** ten-letter expression satisfies \(R(C',D')=R(C,D)\); its phase is rigid, while \(C'^4=C^4\) and \(D'^3=D^3\). The repository's previous Hom-equation orientation and Python unary-minus-on-list bugs have been corrected; an independent nontrivial conjugacy regression and all nine signed rephasing cases are now in the local source-algorithm smoke suite.

The original \(196884D\) \(\mathbb F_{31}\) Monster vector module admits the six-B vacuum \(P_B P_{\zeta}W\) of **observed rank90** with central involution \(J=C^2\) on that vacuum, \(J^2=I\), eigenspace dimensions \(-1:12,\ +1:78\). Genuine original \(D\) vacuum sandwich blocks on these **same** modular eigenspaces were observed. Since \(31\nmid|6.\mathrm{Suz}|\), semisimplicity in this nondefining characteristic is available, but the unknown original Weil-vacuum scalar, standard-word identity and characteristic-zero basis must still be retained.

**Further algebraic source reduction implemented after this run (not yet re-executed):** for \(G=\langle C,D\rangle\) and \(\lambda(C)=-1,\lambda(D)=1\), Schreier's theorem gives
\[
\boxed{\ker\lambda=\langle D,\;CDC^{-1},\;C^2\rangle.}
\]
The genuine \(\mathrm{MMV}(31)\) projector script now derives the second actual source inner-word sandwich \(P_B\rho(CDC^{-1})P_B\) and its *conditional* \(12D\), \(78D\) mod31 blocks on the already original \(J\) eigenbasis, together with cubic-scalar checks. Both \(D\) and \(CDC^{-1}\) give a source-derived **inner generator pair** (up to still unknown Weil factors), advancing the selected \(12D\) representation endpoint without creating a synthetic \(90D\) model. The original quotient generation and the exact Monster word correspondences must still be attached to identify this kernel with the desired published \(6.\mathrm{Suz}\) source generators.

**P5 exact remaining:** Steel's original \`d12.6Suz.nfdeg2.M\` is cached on the user's workstation, but the \`magma\` executable is missing. Thus no original complex faithful12 generator matrices, selected absolute GAP 153/154 word orientation, source-\(\mathbb Q(\zeta_3)\) actual Hom12 intertwiner or complete outer 729 Weil gauge were produced by this execution. The existing original Nebe nonfaithful dual-Sym²78, 90D character type and source class4D fusion are PAID; **literal corrected MM Hit0 C→Monster4D** remains open. One original-source action plan is to inspect the already-downloaded Steel \`.M\` representation and obtain a faithful ordinary12 matrix realization without silently replacing it with a different quotient; then match its \(\zeta_3\mapsto5/25\) reductions against the newly actual original modular \(D,CDC^{-1}\) pair with compatible central residuals. Formal certification remains deferred.


## 24 November 2026 — Magma-free same-Monster signed phase: bounded faithful12 character and literal 4D criterion

**New original-source mathematical advance:** [full theorem and executable source map](../../physics/Monster3BMagmaFreeExactPhaseAndClassWeld20261124.md) and [canonical P0–P6 / L10A/B/C-L12R ledger](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md). The user-requested endpoint priority is to continue the original mathematical construction **without postponing everything until Magma is installed**. The previously user-paid source Monster \(C,D\) words satisfy \(C^4=D^3=(CD)^{56}=1,C^2=(CD)^{28}\) and \(R(C,D)^7=z_{3B}\neq1\), and the actual original 196884D \(\mathrm{MMV}(31)\) B-vacuum has rank90, \(C^2\) eigen dimensions \(12,78\); the GAP source selects Nebe dual-Sym²78 plus faithful12 and source 4D. The original source 4D class still is NOT a literal MM Hit0 word statement.

**First direct literal-class route:** \`mmgroup.MM.chi_powers()\` can compute the actual 196883-dimensional Monster character of the corrected order4 word and its square (especially for a 2B square), without computing a 196884D trace. [\`scripts/monster3b_literal_mm_4d_character_class.py\`](../../scripts/monster3b_literal_mm_4d_character_class.py) matches this literal original word's order and exact two character values against the full source GAP Monster table, accepting C as actual class4D only for a unique original class10 match. This is the missing *source-class vs same-word* discriminator. Its original MM character result is **not yet observed in the assistant runtime**; the method's probabilistic failure is not a proof against 4D.

**Stronger no-Magma ordinary12 theorem:** every ordinary faithful12 \(6.\mathrm{Suz}\) character \(\chi\) is an algebraic integer in \(\mathbb Z[\zeta_3]\), \(\chi=a+b\zeta_3\). The degree12 character bound gives
\[
N_{\mathbb Q(\zeta_3)/\mathbb Q}(\chi)=a^2-ab+b^2\le144,
\qquad\boxed{|a|,|b|\le13}.
\]
The two marked phase embeddings over the same split prime31 are \(\zeta_3\mapsto5,25\). For *coherently Weil-normalized* traces of the same actual \(6.\mathrm{Suz}\) group word, the exact integer pair is recovered **uniquely** by
\[
\boxed{b\equiv(t_5-t_{25})(5-25)^{-1}\pmod{31},\qquad
a\equiv t_5-5b\pmod{31},}
\]
with centered representatives. We checked all **517** integer pairs satisfying the norm bound: **no collisions**. This is an exact mathematical inverse, not a numerical approximation. It DOES NOT automatically turn the observed unnormalized \(P_B\rho(g)P_B=k_0(g)L_g\) into a faithful ordinary character: the source 729D Weil-vacuum scalars \(k_0(g)\) must be paid together with the marked z-orientation/actual standard group-word identity.

**Finite original-cover scalar search:** for source actual inner order3 words \(D,E=CDC^{-1}\), the \(12D\) vacuum sandwich cubes are scalars \(k_0(g)^3\). Each nonzero value permits at most 3 cubic roots over \(\mathbb F_{31}\), so both marked phases yield at most 9 possible Weil cochains per word. Preserve all survivors after the exact char conjugacy \(\chi(g^2)=\sigma\chi(g)\), norm≤144 and nonnegative integral order3 eigen multiplicities \(n_{\zeta^2}=(12-a-b)/3,n_1=n_{\zeta^2}+a,n_\zeta=n_{\zeta^2}+b\). [\`scripts/monster3b_quadratic12_character_lift.py\`](../../scripts/monster3b_quadratic12_character_lift.py) implements this source-bound candidate enumeration. A toy order3 action retains 3 genuine phase options; none is promoted without the original global relator/Weil phase constraint.

**Original source projective cocycle and outer map without Steel matrices:** [the existing MMV original projector](../../scripts/monster3b_actual_mmv31_hom_projector.py) now supports genuine \(MMV(31)\) *and* \(MMV(127)\), marked ζ/ζ⁻¹ independently (31:5/25, 127:19/107), retaining the original 90D source vacuum and 12/78 blocks. It computes exact original source group-word sandwich products for \(D,E\) and checks the correct RIGHT-action cocycle \(E_0D_0=\alpha(D,E)(DE)_0\), \(D_0E_0=\alpha(E,D)(ED)_0\). The new [paired-MM outer C source](../../scripts/monster3b_mm31_outer_phase_pair.py) reconstructs the actual Monster modular 90D ζ/ζ⁻¹ bases from original saved source probes and computes \(C\) between them and \(C^2\)-comparisons up to the observed Weil scalar; 12D/78D paired blocks are extracted only when their actual source action preserves the selected eigenspaces.

**Exact unresolved endpoint:** the same original \(6.\mathrm{Suz}\) source inner word/gauge and coherent 729D Weil scalar need to be solved to turn the modular bounded-character *candidates* into a literal ordinary faithful12 group representation and a full characteristic-zero \(\operatorname{Hom}_E(H_s,W_s)\) intertwiner. The \(\mathbb F_3\) quotient, \(\mathbb F_{31}\) and \(\mathbb F_{127}\) modular Monster actions, exact source 4D class and original complex Monster object remain separately typed; no stage has claimed to identify an original char0 matrix without an original field/basis lift. **The already existing Steel Magma source is useful numerical input, not a mathematical precondition for the new bounded-character theorem or literal class criterion.**


## 24 November 2026 — canonical P5 correction: the existing 729 Weil source already pays the kernel and relator-specific gauge

The primary 729-dimensional work was **already present** in the original Schrödinger/Heisenberg and TOE compiler owners, not a missing future producer. [The canonical original 729 source audit and exact relator work](../../physics/Monster3BExisting729WeilSourceReuseAndRelatorWeld20261124.md) now connects those existing contributions to the actual Monster normalizer P5 ledger. The existing \`Monster3BFiniteSchrodingerFullActionLawExact\`, \`FiniteSchrodingerPointProjectorExact\`, \`AtlasSymplecticSimilitudeHeisenbergLiftExact\`, \`Monster3BNormalizerCocycleCancellationExact\`, \`IbrahimMonster3BLinearMultiplicityHomSpaceExact\` and \`scripts/toe_cyclotomic_operator.py\` supply the literal finite-model 729, point projectors, q-corrected \(12D\) symplectic/anti-symplectic conjugation, exact support/cyclotomic Weil phases and inverse-cocycle theorem. No new 729 basis or generic projective representation is invented here.

For source \(M_g\) in the original six-position/six-modulation chart, set \(r_g=\mathrm{rank}(M_g)_{a,b}\), \(\Delta=\zeta_3-\zeta_3^2\), \(\Delta^2=-3\), and let \(K_{g,s}\) denote the previous \`toe_cyclotomic_operator.compile_shape\` **unnormalized** original kernel. Choosing the declared model gauge \(\widetilde K_{g,s}=\Delta^{-r_g}K_{g,s}\), its exact zero-vacuum coefficient is **already determined** by the existing Weil phase/support polynomial:
\[
\boxed{\kappa_{g,s}=\langle e_0,\widetilde K_{g,s}e_0\rangle
=\begin{cases}\Delta^{-r_g}\zeta_3^{q_{g,s}(t_0)}&y_0+B t_0=0,\\0&0\notin\mathrm{supp}(K_{g,s}e_0).\end{cases}}
\]
The unique \(t_0\) follows from the already established source rank-\(r_g\) support basis; \(\kappa=0\) is a legitimate geometric obstruction, not an invertible unknown scalar. The original compiler's overall scalar gauge must not be silently equated to the original Monster 729-factor gauge.

The new [source-compatible one-column Weil model compiler](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) imports the previous TOE kernel, consumes authentic corrected MM C/D quotient matrices, and derives \(\kappa_{D,s},\kappa_{CDC^{-1},s},\kappa_{C,s}\), the projective multiplier
\[
\widetilde K_{g,\lambda_hs}\widetilde K_{h,s}
=\alpha_s(g,h)\widetilde K_{gh,s},\qquad
\alpha_s(g,h)\in\mu_6,
\]
and the exact quotient relator seventh-power using only one kernel column and a fast \(\mathbb F_3\) support inverse. The [existing model versus actual source vacuum consumer](../../scripts/monster3b_original729_actual_vacuum_weld.py) additionally tests the genuine \(\mathrm{MMV}(31)\) projected 90D D/E product scalar
\[
\boxed{\beta_s(D,E)=
\frac{\kappa_{D,s}\kappa_{E,s}}
     {\alpha_s(D,E)\kappa_{DE,s}}}
\]
in the **right** MM action convention, preserving zero/nonscalar/orientation counterexamples rather than claiming a fictitious positive weld. If the same source identification holds, this yields genuine modular \(12D/78D\) matrices normalized in the **declared 729 projective gauge**, not automatically honest ordinary characteristic-zero 6Suz operators.

**Exact original ATLAS numerical donor, both marked \(\zeta,\zeta^2\) phases, no Magma:** from the authentic SHA-pinned \(2.\mathrm{Suz}:2\) \(C,D,J,P\) matrices (original \`check_toe_atlas_mirror.py\`), reuse of the earlier 729 kernel gives \(\kappa_C=-1/3\), \(\kappa_D=\kappa_{CDC^{-1}}=\kappa_{DE}=\kappa_{ED}=\kappa_R=-1/27\), \(\alpha(D,CDC^{-1})=\alpha(C,C)=1\), and
\[
\boxed{\widetilde K_{R,s}^{\,7}=I_{729},\qquad
        R=cdcdcddcdd,\quad s=1,2.}
\]
The original quotient order7 \(R\) and exact cocycle staircase \((1,-1,1,-1,1,1)\) were calculated locally from those source values. [Original ATLAS 729 replay](../../scripts/check_monster3b_atlas_source729_relator.py) is committed. These scalar values belong to the **ATLAS chosen polarization**; the actual user-local MM B-vacuum can have different coefficients, so the correct MM-chart compiler must be used before dividing its original modular operators.

**Exact full-Monster signed relator:** user-reported authentic corrected MM \(R^7=z_{3B}\neq1\) is *not* the quotient R⁷=1. For an arbitrary source-compatible 729 Weil model \(K_R^7=\gamma_s I\) with \(\gamma_s\in\mu_6\), the cyclic order-seven scalar is uniquely fixed (since \(\gcd(7,6)=1\)) by \(K_R^{\mathrm{ord7}}=\gamma_s^{-1}K_R\). It follows algebraically that any same-actual-\(W_s\simeq H_s\otimes S_s\) identification in this chosen order-seven Weil gauge must satisfy
\[
\boxed{(L_{R,s}^{\mathrm{ord7}})^7=\zeta_3^s I_{90}.}
\]
This pays the **relator-specific 729 scalar mathematical obstruction** without running Magma or independently constructing a 729 operator. The still-genuine terminal obligations are a globally coherent \(6.\mathrm{Suz}.2\) scalar/outer source-word selection, the original 729-to-actual Monster W_s basis/evaluation identification, the exact ordinary same-Hom 12/78 matrices, and literal corrected MM C→Monster 4D. None follows solely from matching dimension, quotient character class or these finite-model coefficients.

Attribution: original ATLAS/AtlasRep, Barraclough–Wilson, finite Weil theory, original TOE and finite-Heisenberg code, Dietrich–Lee–Pisani–Popiel Monster words and Ibrahim's original phase/multiplicity/Hom sources. Preserve the original signed central \(R^7=z\), diagonal class20 versus extraspecial centre, zero-vacuum, phase and model-chart distinctions; P6 certification remains after endpoint mathematics.


## 24 November 2026 — gauge-independent Monster 3B P5 **operator** weld, not merely a trace test

The original 729-dimensional Schrödinger/finite Weil model, Heisenberg cocycle correction, phase-changing similitudes and inverse normalizer cocycle are pre-existing source code (Agda and TOE/AtlasRep), not unresolved prerequisites. This continuation sharpens the genuine same-object problem: can the *actual* \(\mathrm{MMV}(31)\) 78-dimensional C²-eigenblock of the Monster be explicitly transported into the dual symmetric square of the *actual* 12-dimensional C²-eigenblock, simultaneously for the corrected Monster inner words \(D\) and \(E=CDC^{-1}\), without choosing the remaining scalar gauge? See the [complete original-source derivation and exact phase/lemma ledger](../../physics/Monster3BProjectiveDualSym2SameMonsterOperator20261124.md) and [living P0–P6 roadmap](../../roadmaps/Monster3BEndpointFirstConstruction20261123.md).

For a genuine inner order-three word \(g\in\{D,E\}\), the existing model Weil projective cocycle computes
\[
K_{g,s}^3=\gamma_{g,s} I_{729},\qquad
\gamma_{g,s}=\alpha_s(g,g)\alpha_s(g,g^2).
\]
The new source consumer [\`monster3b_original729_weil_source_cocycle_weld.py\`](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) explicitly records both original word cubic scalars in exact \(\mathbb Q(\zeta_3)\) for both signed phases. If the actual Monster \(W_s\simeq H_s\otimes S_s\) evaluation uses that *same original source Heisenberg gauge*, the genuine Monster relation \(\rho(g)^3=I\) requires
\[
B_{12,g}^3=B_{78,g}^3=\gamma_{g,s}^{-1}I
\]
for the **actual modular source** multiplicity blocks divided by the exactly compiled nonzero Weil B-vacuum coefficient. Their original 12 and 78 sizes are the already-paid actual C² eigenvalues, not independent invented carriers.

The source GAP selection gives the full ordinary character identity \(S_s\simeq V_{12,s}\oplus\operatorname{Sym}^2(V_{12,s}^\vee)\). There is an unknown cubic rephasing \(c_g\) with \(c_g^3=\gamma_{g,s}\), but **it cancels exactly from the 12/78 character and operator relations**. Explicitly, write \(A_{12,g}=c_g B_{12,g}\), \(A_{78,g}=c_g B_{78,g}\). Since \(A_{12,g}^3=I\), the symmetric-square character formula and \(B_{12,g}^{-1}=\gamma_g B_{12,g}^2\) give the phase-safe equation
\[
\boxed{2\operatorname{tr}(B_{78,g})=
       \operatorname{tr}(B_{12,g})+
       \gamma_g[\operatorname{tr}(B_{12,g}^2)]^2.}
\]
This is the original-source [\`monster3b_actual_order3_projective_sym2_weld.py\`](../../scripts/monster3b_actual_order3_projective_sym2_weld.py) test: its source inputs are the actual \(\mathrm{MMV}(31)\) \(D,E\) 12/78 matrices, the prior TOE-derived \(\kappa,\gamma\), and literal original C². It refuses zero-vacuum, mismatched source provenance, noncentral cubes and incorrect 78 characters. All six \(\mu_6\) model gauge options (including \(\gamma=-1\)) satisfy the formula in an independently locally executed synthetic 12/78 test; a deliberately changed 78 character fails. **These tests do not instantiate the actual Monster \(\mathrm{MMV}(31)\) receiver in this environment.**

Crucially, the operator relation is even stronger:
\[
\boxed{T_{78,g}
=\gamma_g^{-1}\operatorname{Sym}^2((B_{12,g}^{-1})^\top)
=\gamma_g\,\operatorname{Sym}^2((B_{12,g}^2)^\top).}
\]
The original 78-dimensional Monster block should be *simultaneously* conjugate to those two constructed operators by ONE \(78\times78\) invertible map \(F_s\),
\[
\boxed{F_s B_{78,D}=T_{78,D}F_s,\qquad
       F_s B_{78,E}=T_{78,E}F_s.}
\]
The [new constructive source operator program](../../scripts/monster3b_actual_projective_sym2_intertwiner.py) avoids a 6084-variable dense Kronecker solve: it finds a simple shared eigenvalue in \(h(D,E)=aD+bE+cDE\), propagates matching D/E words from a one-dimensional eigenspace to a full 78-dimensional cyclic basis, computes \(F\) as the target-to-source basis change and checks every entry of both generator equations and the inverse. A locally executed independent \(\mathbb F_{31}\) prototype with two noncommuting original-shaped order-three generators, a hidden random 78×78 conjugacy, model phase \(\gamma_D=-1\), and 78 generated vectors recovered the full \(F\); a wrong second source generator did not. The actual original Monster 12/78 inputs have not been run through the newly committed operator program in this assistant runtime, and no Magma or unrelated quotient search was necessary for the new mathematical construction.

This provides a clear **next promoted endpoint**: if original \(\mathrm{MMV}(31)\) source data produce an invertible \(F_s\) for the corrected \(D,E\), the **same actual modular Monster 78D action** is explicitly identified with \(\operatorname{Sym}^2(12^\vee)\) on these generators, stronger than coincident character values. It does not automatically identify all \(6.\mathrm{Suz}.2\) ordinary complex matrices or the literal corrected C with Monster class4D. Global standard-generator word alignment, phase-inverting outer \(C\), all normalizer relators and original characteristic-zero \(W_s\) remain the precise still-unpaid mathematical source welds; the prior \(R^7=z_{3B}\) signed central residual remains separate and preserved.

Original attribution retained: finite Schrödinger/Weil/Stone–von Neumann theory, source AtlasRep \(\mathrm{GF}(3)^{12}\), Barraclough–Wilson original Monster normalizer characters/fusion, Dietrich–Lee–Pisani–Popiel MonsterSubgroups words, and Ibrahim 12/78/90 character/isotypic/Hom source constructions. New code is a source-to-source consumer and representation-intertwiner algorithm, not a replacement original 729 model or a new ordinary 6Suz representation. The class20 diagonal-kernel C3 versus extraspecial Monster z, zero-vacuum, signed ζ/ζ² phase, p31/p127 indexed charts and source vs target field boundaries remain explicit.


### P5 signed outer projective packet join (2026-11-24)

Existing producer packets are joined by `scripts/monster3b_signed_outer_sym2_join.py`. For raw outer vacuum blocks A_s (12) and H_s (78), require A_-s A_s=-beta I and H_-s H_s=beta I, beta nonzero. With Q_s=Sym²(A_s^-T), test F_-s H_s F_s^-1=lambda_s Q_s; the signed loop requires lambda_+ lambda_-=beta³, not 1 unless normalized. Relative scaling G_+=F_+, G_-=F_-/lambda_+ fixes forward residual to 1 and reverse to beta³. Preserve both marked phases, zero/singular obstruction, packet hashes and inner D/E equations. This is a conditional modular packet join, not independently authenticated same-source provenance, ordinary Weil normalization or actual characteristic-zero Hom attachment. Original packet execution remains unpaid; L10B/C and L12R remain open. Prior ATLAS/mmgroup/Ibrahim/Nebe/TOE producers unchanged.


### P5 superseding endpoint cut — global parity cochain and central-involution complement (24 Nov 2026)

See [global signed Weil and complement theorem](../../physics/Monster3BGlobalParityCochainAndComplementConjugacy20261124.md) . The 729=365+364 parity determinant ratio gives a canonical ordinary signed quotient section on zero-affine Heisenberg automorphisms, with no local cubic-root selection. The central -I involution gives H^1(G,E/Z)=0 and the explicit reverse solve u=(I-j)^-1 f(j), structurally conjugating the actual corrected complement to the source complement under the existing source hypotheses. Pull back the canonical model to H and use the actual ordinary W in Hom_E; this is a genuine abstract signed multiplicity action, not an extracted numeric characteristic-zero matrix. Both projective and canonical signed joins are now integrated in P5, including literal provenance joins, fixed cyclotomic embedding, cyclic 78-unknown Hom fallback, known source relators and paired bounded characters. Independent original ATLAS model replay: 10/10 named relators, both E words, both C2 parity checks; 30/30 synthetic beta fixtures and full-rank cyclic fixture. Actual MMV/GAP/Steel source data were unavailable; actual numeric witness remains open. **Class correction:** existing 4D fusion selects inner r projecting to Suz 2B, NOT outer C projecting to Suz:2 2C; separate source scan and direct literal character test are needed. L10A literal ordinary source coordinates/word phases open; L10B global model normalization paid, actual numeric basis/vacuum attachment open; L10C source-bound modular witness open; L12R structural complement theorem conditional on reported authentic source data, literal C class/standard-word phases open. Do not promote conditional source data to executed receipts. P6 deferred.


### P5 superseding source-class and geometric reverse-lift cut — 24 November 2026

See [outer class and geometric ordinary lift](../../physics/Monster3BOuterClassAndGeometricOrdinaryLift20261124.md). The published CTblLib 1.3.11 fusion data give outer Suz:2 class 2C (38) -> 2.Suz.2 class 62, square class 2 -> 6.Suz.2 class 129 -> main 52 -> MN3B 31 -> M 10 (4D). Distinct from the inner 54 -> 33 -> 10 path. Schur–Zassenhaus proves the literal corrected MM C is 4D conditional on the prior authenticated order-four quotient attachment. No GAP or MM replay claimed. Universality/perfectness of the 6.Suz inner cover gives a unique inner lift of the fixed quotient chart; the outer lift is unique up to central conjugacy. Literal standard-word phases are still uncomputed. The complex Leech lattice modulo sqrt(-3) has exactly three minimal-vector representatives per occupied residue; the 196560 minima occupy 65520 nonzero residues. Relative Eisenstein phases on a 12-vector Hermitian Gram graph give a finite exact reverse-lift construction of ordinary generators from the original lattice chart, independently of Steel/Magma. Actual lattice/Steel coordinate data and numerical matrices remain open. A supported entry of the canonical Weil vacuum column replaces any zero vacuum sandwich, yielding the exact same-object Hom formula conditional on actual W and chart. One normalized inner intertwiner F_plus determines F_minus via Q_plus F_plus H_plus^(-1), so the second independent search is unnecessary; actual F_plus is not yet computed from genuine packets. These are mathematical endpoint reductions, not numerical characteristic-zero or P6 completion. Retain the zero mode, signed phases, indexed source charts, and original attributions.


### Ordinary source reconstruction (24 November 2026)

The [Lindsey ordinary signed source and join](../../physics/Monster3BLindseyOrdinarySignedSourceJoin20261124.md) replaces the missing ordinary matrix donor with a genuine characteristic-zero reconstruction of Lindsey's published six generators, using the existing ATLAS chart. Standard phase Q=CDCDD has Q^7=1 while R=cdcdcddcdd has R^7=z. The literal Monster Q^7=z^q fixes the remaining D phase; R^7 alone does not. The exact ordinary 12 induces the dual symmetric-square 78 and their signed two-phase sum. Good-prime source relations and source-derived hidden-basis tests passed; original Monster operator packet and actual characteristic-zero Hom transport remain distinct, unexecuted requirements. Credit Lindsey and ATLAS for their source constructions.


### 25 November — literal standard D and good-prime exact Conway Hom expression

[Source theorem, producer/consumer integration and execution boundary](../../physics/Monster3BExactConwayHomReynoldsLift20261125.md). Q=CDCDD, u=Q^7 in the actual E-centre; D_std=u^-1 D gives standard Q^7=1 and R^7=z, with reverse D=u D_std. Actual q is measured by the small original-word consumer, not guessed or inferred from R^7. Conway's rational 196884 module is defined over Z[1/2] and mmgroup's MMV(31) is its reduction. The original phase/vacuum and tensor evaluation and canonical Weil factors are integral at the marked prime (31,zeta-5). As 31 is prime to |H|, an actual signed modular intertwiner lifts to an exact characteristic-zero group-algebra expression via Reynolds averaging of an integer seed on the same original projected ambient coordinates. The existing P5 path now emits this expression after the genuine modular join, with original receipt hashes, no repeated E search and a fail-closed required-expression switch. Independent exact committed ordinary source checks 24/24 and local SymPy small-group Reynolds fixtures at 31/127 pass. Actual original MM packets and mmgroup unavailable; literal q and actual modular/instantiated char0 witness still unpaid, dense evaluation distinct. P6 remains deferred.


### 25 November — source C13 wheel and compact signed Hom lift

[Derivation, source provenance and acceptance boundary](../../physics/Monster3BSingerCyclicHomSeedProjector20261125.md). Literal ordinary source g=(DEdeDeDEDEdedEd)^3 has order 13, V12 restricts to augmentation, dual Sym² V78 to six regular modules. Preserve 0/6 fixed ranks and 12/72 relative ranks; Singer inverse B_g^vee/3-J_g/12, no identification with the donor Griess action. Direct source orbit bases solve positive 12 and 78 seed coordinates, derive opposite phase by actual outer C, recover relative Sym² map and recheck all signed generators. Source rank(S)=rank(S²)=n-1 mod31 for q=0,1,2; p(0)=17/4 mod31 for n=12/78. Exact compact characteristic-zero projector p(S_L)/p(0) uses degree 11/77 source determinant recipe and retains the genuine modular seed, under the prior authenticated Conway/Weil integral hypotheses; Reynolds retained as existence argument, no full group enumeration required. 18/18 local source-derived fixture generator equations, three wrong controls rejected, six seed projector cases; actual Monster packets and literal q not available; integrated runner and dense char0 evaluation unexecuted. Canonical roadmap/Paper10 now supersede old independent two-phase projective solve as required path; original source authentication and P6 remain independent.


### 25 November — exact zero-affine vacuum and one-sided original phase producer

[Source theorem, literal-word gate, tests and execution boundary](../../physics/Monster3BZeroAffineVacuumOnePhaseTransport20261125.md). For zero-affine linear M=[[a,b],[c,d]], E_bb=b^T d and t in ker b implies t^T E_bb t=0. The original compiler selects origin zero, raw K00=1, canonical K00=epsilon^-1 Delta^-rank with epsilon in mu6 and Delta^2=-3. Unit at both split good primes; no alternate vacuum search is needed in this chart, unlike arbitrary affine translations. Literal C vacuum map is invertible, so derive all 90 negative basis vectors by P_-(v_i C) from the original positive vacuum; retain full ambient row replay, original C/D and positive hashes. Independent negative search optional, negative D/E sandwiches still computed. Literal raw wheel g^13 residual measured and reversible correction g13=r^-1 g recorded; exact source Hom requires raw g^13=1, not silently corrected word. 864/864 marked compiler cases, 10368/10368 unit checks, 16/16 reduced signed tensor transport checks and two affine controls passed locally with matching checker blobs. Full actual MMV integration unexecuted, literal q/order13 and actual signed Hom/instantiated char0 witness remain unpaid. P6 and actual 4D gate remain separate.


### 25 November — intrinsic characteristic-zero closure and actual linear tensor boundary

[Complete theorem and exact constructor/weld audit](../../physics/Monster3BIntrinsicGeometricClosure20261125.md). Under authenticated original E/cover/ATLAS chart, original BW/CTblLib character restriction/descent and Lindsey ordinary source, the canonical Weil extension agrees with the original inner extension: Stone–von Neumann gives scalar character on the perfect 6.Suz inner cover, hence trivial. This comparison is on the original split extension before descent, not a fictitious separate 729-dimensional N representation. Original selected character restriction identifies the SAME actual Hom blocks; marked central phase fixes the conjugate member, C² signs split 12 and dual Sym²78. Actual isotypy over K follows from base change of linear intertwining equations, without requiring a target modular witness. On each block the cyclic residual sum-of-adjoint-squares has one-dimensional kernel by irreducibility/Schur, hence source polynomial p(S_L)/p(0) gives an intrinsic line. Normalize source orbit Gram G; U_i=P_L sum_j (G^-1)_ij L(w_j)^* and T_i=L(w_i) satisfy U_i T_j|_line=delta_ij, sum_i T_i U_i=I and exact matrix-unit composition. This yields forward/reverse on all orbit coordinates valued in the same line; an individual seed may be selected by the first nonzero projection of the original Conway basis. Opposite phase is transported by C and actual tensor inverse is the sum/weight-projector pair on all 729 copies; W0 retained. A pure Cartesian pair cannot represent all tensors; the existing Agda ActualLinearMultiplicityHomSpace interface needs repair and actual proof inhabitants; use the existing Lean #47 tensor finite-copy compiler. Exact rational controls 1299/1299 and 353/353, not actual Monster execution. Source premises and formal/numerical realization boundaries remain explicit. No claim of evaluated dense char0 coordinates, full source reauthentication or kernel acceptance.


### 25 November — full linear weight-frame weld (latest implementation ledger)

[Exact source formulas, owner links, executed controls and remaining gaps](../../physics/Monster3BActualLinearWeightFrameWeld20261125.md). Under previous A–C, R_x=P_B P_s rho(T_x^-1), I_x=rho(T_x)|S_s, orthogonality R_x I_y=delta_xy id and resolution sum I_x R_x=id yield full linear inverse Phi=sum I_x u_x and Psi_x=R_x w. Signed transport R_y^t rho(g) I_x^s follows by composition, not a pure-tensor-pair bijection. New Agda ActualLinearWeightFrame derives pointwise inverse, add/scale and signed roundtrip; Ibrahim Hom owner now exposes ActualLinearWeightHomSpace tied to the literal zeta carrier and same multiplicity carrier. Existing basis/vector correction and proof-relevant hardening retained; historical Cartesian contract not valid for full vectors. Lean #47 MonsterWeightFrame derives actual linear finite-copy equivalence and cross-sector transport (source-written, no kernels run). Python WeightFrame executes exact phase/weight inverse with zero sector retained; original MMV31 consumer streams two 729-weight charts with signed 12/78 projection and derives negative vacuum from original positive packet. Source-bound adapter unexecuted here. Local matching-blob Q(zeta3) reduced controls: 75 roundtrips, 1332 vacuum-range/same-weight inverse checks, 8 signed covariance equations, 18 coordinate-linearity checks and zero-coefficient rejection. No actual Monster execution. Remaining: authenticate original A/B source data; inhabit actual Conway K-linear action and weight-resolution laws, attach exact trace functional and existing character/cover weld, instantiate E4 seed-line operators on same actual vacuum, then P6. Numerical MMV31 roundtrip independent of characteristic-zero existence. Keep all source/fixture/formal/kernel boundaries explicit. No all-hit/character search or alternative canonical vacuum search.


### 25 November — single-residual dual orbit and original trace weld (latest implementation ledger)

[Full derivation, execution receipts and remaining source boundary](../../physics/Monster3BSingleResidualDualOrbitTraceWeld20261125.md). Replace the adjoint-square sum with the selected single R_D,i (zero-based i=0 for 12, i=26 for 78), rank R=rank R²=n-1 at prime31 for q=0,1,2. Source p(0) residues 17/22/23 and 15/15/15, degree 11/77; exact p=det(tI-R_A)/t, never lift modular coefficients. With Q_A=v lambda and H_ji=lambda A(w_j)^-1 A(w_i)v, H invertible at31 gives exact nonorthogonal dual U_i=Q_L sum_j (H^-1)_ij L(w_j)^-1 and both inverse laws. Under A–C actual char0 expression follows without target modular prerequisite. Local matching-blob source controls 6/6 cases, 18,684 dual equations, 18 signed generator equations, 3 corrupted controls. Actual ambient-character Fourier trace chi_Ls(g)=sum_(j,b) zeta^-sj chi_W(z^j b g)/(3^7 k_g) on phase-preserving words; C² sign projections give the two constituent traces without division by a possibly zero full Weil trace. 20 exact reduced cyclotomic controls passed; original literal word-class trace oracle/full original BW character receipt still unauthenticated. Canonical cyclic solver now consumes single residual; optional actual MMV31 frame --model composes true ordinary 729x12/729x78 coordinates with original W0 retained, checks same-action generator traces; exact witness writer emits source determinant and dual expression, both actual integrations unexecuted here. Remaining A/B/C source authentication, actual Conway K-linear action and trace/weight laws, actual application of exact source recipe and formal inhabitants/kernels P6. No genuine actual execution or dense characteristic-zero coefficients claimed. No new search prerequisites.


### 25 November — original Conway characteristic-zero backend and actual vacuum attachment (latest implementation ledger)

[Source-native exact rational action, actual probe/column producer and evidence boundary](../../physics/Monster3BActualConwayExactCRTAttachment20261125.md). Reuse Seysen's upstream mmgroup fixed-point CRT source, not a new group model. Under the original atom denominator-divides-8 and invariant weighted norm contract, signed radix128 limbs reconstructed from 7/31/127/255 give exact original rational atom action at arbitrary precision (limb bound 451132 < CRT half modulus 3513772). K-vector (a+zeta b)/d, exact sums/scalings, original native word action. Local matching-blob controls: 36 exact SymPy atom equations, 18 K-linearity, 36 good-prime reductions, 6 roundtrips, full 196884-coordinate limb test and corrupted residue rejection. Exact K-cyclic orbit solver source-written, 2D control 4 generator equations and 2 inverses; complete ordinary Lindsey JSON independently matched original Git blob b0f96b37494cfca56f116b991d350352d3a493f2; q=0 exact ordinary block checks printed true but command timed out, not complete acceptance. Actual char0 producer uses original direct positive MMV31 probe indices, EXACTLY reprojects the original Conway unit coordinates, verifies reduction against paid rows, derives opposite phase by literal C, checks marked pivots and full ambient reconstruction for each normalized C/D/E/C² column; exact sign split, single-residual nullspace and both signed source maps/inverses. This is not entrywise modular row lifting; no dense polynomial evaluation on ambient W needed. Per-vector/column checkpoints, --max-new bounds new units rather than walltime. Exact original runtime/packets unavailable, so actual native backend and integrated char0 output remain unexecuted. L08–L12 now have a concrete exact action producer; remaining actual runtime/source A–C and true full trace attachment, full-weight execution and formal P6. Successful actual generator weld under authenticated generation would imply all word-character equality, no need to enumerate traces separately. No new discovery programme or false flags.


### 25 November — native execution max-cut and exact ordinary source replay (latest implementation ledger)

[Bounded original word blocks, normalized outer basis, exact acceptance and native preflight](../../physics/Monster3BExactConwayBlockAndOuterGaugeMaxCut20261125.md). Original complete Lindsey blob b0f96b37494cfca56f116b991d350352d3a493f2 independently replayed: 48/48 exact Q(zeta3) 12D signed relators across all three D phases and both conjugate phases; dual Sym² carries the word identities to 78 (wheel nonidentity also previously checked mod31). This cleanly replaces the prior timeout for these source relations. Native CRT now groups integral atoms and up to two t/l atoms, denominator d=1/8/64 and full-dimension adaptive radix 4096/512/64 under 4d²(r-1)² sum weights < M²; full exact norm checks and streamed common-denominator ambient recomposition retained. Normalize negative basis as L(C)v_i, so C+=I, C-=J, D-=E+, E-=J D+ J. Extract only 270 positive D/E/J columns instead of 720 independent signed columns, derive negative under honest signed-action laws; --negative-audit 1 default replays 4 negative columns, 90 replays 360. Basis projections and full ambient residual checks remain. Code/source/runtime checkpoint identity strengthened. Local matching-blob controls: new 44 exact blocked/linearity/signed checks, prior CRT 36/18/36/6 plus full-size and negative control rerun, cyclic control rerun; original source 48/48. New native preflight compares to upstream expanded integer CRT buffer and standard MMV31/127 and inverse, not scaled float getter; unexecuted here (mmgroup 1.0.8 CP313 wheel download failed). Actual source-native backend, marked source packet and integrated actual char0 maps remain unpaid. Run native preflight then original char0 producer on existing workstation with genuine manifest/cover/model/positive packet, fresh checkpoint directory. No further abstract discovery campaign; actual A–C authentication, full-weight inverse and P6 formal/kernel remain distinct.


### 25 November — complete original-weight execution handoff (latest implementation ledger)

[Full native endpoint consumer, inverse, exact regression and resumable command](../../physics/Monster3BActualChar0FullWeightEndpointExecution20261125.md). Use the actual characteristic-zero vacuum basis V_s, marked pivot minor M_s and ordinary map A_s from prior exact receipt. Each c_(s,x)=A_s M_s^-1 pi_s P_B P_s rho(T_x^-1)v is checked by full ambient vacuum recomposition; inverse is P_0 v + sum rho(T_x) V_s A_s^-1 c_(s,x), with all 1458 marked weight rows including zeros retained and the original centre-trivial component stored. Source-written actual consumer checkpoints each weight and reconstruction chunk, verifies vacuum code/input lineage and both ordinary inverse maps. Shared exact codec and checker matching committed blobs executed 99/99 reduced checks (84 coordinate inverses, 14 full-vector inverses, one off-vacuum rejection, 13D signed fixture), prior blocked 44 and cyclic 4/2/1/1 controls reran clean. Strict original MMV31 receipt reader rejects incomplete/malformed echelon or noncanonical residue packets. New single-command runner reuses reported original P5 run, native preflight, canonical model if missing, exact vacuum, then exact full-weight roundtrip; separate output with log/summary, exit 0 only completed receipt, 3 checkpoint pause, 124 timeout, 2 blocked/error. Run `python3 scripts/run_monster3b_actual_char0_endpoint.py --source-run build/monster3b-p5-endpoint/run-20261124T071452Z-174442 --outdir build/monster3b-exact-char0-endpoint --timeout 900 --max-new 1` on existing mmgroup workstation. Native mmgroup absent here, pip acquisition retry failed; original paths from user-reported receipt not observed locally. Integrated CLI and actual original target remain unexecuted; no new native source or kernel acceptance. L08–L12 now have complete concrete execution consumers. Remaining genuine runtime, A–C source authentication, actual original generator/weight receipts and P6. No more abstract discovery required.


## 25 November — CONTROLLING post-native execution ledger

[Exact reverse-solved remaining source, Hom and good-prime welds](../../physics/Monster3BPostNativeExecutionReverseSolveWelds20261125.md). User-reported genuine mmgroup 1.0.8 preflight 224/224, canonical Weil 10/10 quotient relators, exact plus-00/minus-00 and rc3 checkpoint pause; raw files not independently accessed here. Original atom-tag and v1 receipt fixes not in remote head at start; preserve active local code/checkpoint identity and have workstation agent commit exact local patch, do not fabricate its bytes. No Python dependency in the active checkpoint identity changed by this cut. L08/L09 actual Hom = vacuum is now derived: separating modulations force support at origin, translation determines each basis image, linear extension gives f_u(h)=sum h_x I_x u, inverse R0 f(delta0). Lean #47 MonsterVacuumHomEquivalence actual equivariant linear submodule and inverse source-written, imported in post-recognition owner. Agda new literal linear normalizer/phase source removes impossible finite-basis recognition prerequisite; actual weight Hom consumes it with proof-bearing equivariant map and derived vacuum recovery; full weight-two acquisition now routes through the 196884D original action with explicit normalizer embedding and 196883D constituent inclusion/recovery, not a false carrier equality. Both nontrivial phase projectors kill original trivial line, W0 retained. Actual kernel inhabitants and genuine trace-of-action, not equality of arbitrary functions, remain.

Independent R3 shortcut: O=Z[zeta] localized at (31,zeta-5), original dyadic action, E-projectors and canonical vacuum units integral, actual rank90 local lattice by source trace54 and Weyl weights, existing direct probes mod31 basis. If actual signed modular generator intertwiner invertible, Reynolds F=(1/|H|)sum L(h)F0 A(h)^-1 is exact and reduces to Fbar, unit determinant since 31 does not divide |6.Suz:2|. No dense char0 numerical matrix prerequisite for mathematical equivalence, no group enumeration needed for proof, original BW row/fusion attribution still needs B. New positive-only actual mod31 replay script recomputes D/E/J on original probes, derives negative chart and checks signed maps both ways, source-written/unexecuted here; 46/46 exact reduced cyclotomic good-prime controls including bad-prime failure, matching committed blob. Continue existing genuine char0 campaign, optional independent modular existence route in separate output. Exact residual A1 original E/chart, A2 full generating quotient and perfect cover, A3 honest signed Weil action, A4 outer fusion, B original BW/CTblLib source authentication, C actual Lindsey standard word chart, L08–L12 actual rank90/270 positive columns and signed char0 or good-prime witness, full original weight probe, P6 actual source inhabitants and kernels. Detailed table in linked controlling audit. No completion flag promotion.


## 25 November — CONTROLLING quotient-generation and positive seed weld

[Exact source replay and remaining literal attachment](../../physics/Monster3BAtlasGenerationAndPositiveSeedWeld20261125.md). Original pinned ATLAS GF3 C/D bytes SHA256 matched; deterministic orbit-stabilizer certificate on e0,e1,e2 gives orbit sizes 465920,106920,36, product 1793381990400 = published |2.Suz:2|. First two stabilizer subgroups generated by 24 explicit Schreier witnesses total, constructed from prior generators, so lower bound divides group order and saturates published upper bound. Local matching-blob replay passed; three corrupted controls rejected. No semipresentation-only generation claim. Optional --manifest/--cover replays existing native canonical cover producer, matches literal words/matrices/relators, checks both ATLAS transports, zero affine and literal R^7=z, giving full H=6.Suz:2 under published original N/E/zero-affine kernel premises. Actual native attachment not executed here. Independent positive-only modular consumer now retains Q12/Q78 original 90D eigenspace embeddings, X=[Q12 F12+^-1,Q78 F78+^-1], both exact mod31 inverse laws and ambient D/E/J intertwining, positive seed columns, source hashes and optional generation receipt. Exact seed y=Q_L P_n P_B P_+ sum lift(x_i) lift(original row_i), where Q_L is the exact source polynomial projector, not lifted modular coefficients. Under honest integral source action and authenticated generation, good-prime Reynolds gives existence, then original single-residual cyclic forward/reverse coordinates retain seed gauge without huge sum. Native replay/actual exact seed evaluation unexecuted here. No active char0 checkpoint dependency modified; workstation local compatibility commits still need exact patch custody. Remaining actual source replay A1/A2, exact signed Weil covariance A3, BW source row/fusion authentication B/A4, same original standard cover C, native modular or char0 map and weight receipts, actual formal inhabitants/kernel P6. No new all-hit or representation search.


## 25 November — CONTROLLING exact Weil and original source authority

[Exact Weyl covariance, scalar uniqueness and original authority replay](../../physics/Monster3BExactWeilAndOriginalSourceAuthority20261125.md). Independently replayed pinned ATLAS quotient order certificate (465920×106920×36=1793381990400; 24 Schreier witnesses). Fetched original Dietrich–Lee–Pisani–Popiel subgroups.py blob c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2 and matched all 14 literal source group words to existing producer blob 290f6643f8bd1f842cf1c4591c0e68597d6d5b61. A3 exact original TOE 729 kernel verification: 72/72 Weyl axis equations on full zero/support and cyclotomic phase arrays, six parity checks, six corrupted kernels rejected, all zero-affine vacuum supports nonzero; executed matching Git blob e4965353654310044780dba99ef4cc33292e8fac, original compiler blob 85bff01e8f22211a0f688a94646ed12123dd0c74. Exact covariance plus Schur and column norm gives unitary Delta^-r normalization. Parity determinant ratio in mu6 (norm-one Eisenstein S-unit, only ramified prime3 inverted), uniquely determined mod31, dimensions 365-364=1 kill all scalar ambiguity. Normalized products implementing same signed automorphism agree by Schur and ratio1; honest action on generated quotient, all word relations, C²=J because parity ratio1. Literal actual cover/model comparison not executed here. New original_source_authority_replay command checks pinned producer, reruns native manifest from original words, actual 3B trace53+1 yields phase dimensions 65664/65610/65610 and vacuum90, replays literal generation and exact model covariance/scalar equality. Receipt can feed --generation into independent positive modular replay; see linked audit for command. Native source packets unavailable here, no new actual workstation acceptance, no active char0 dependency changes; commit exact workstation compatibility patch separately. A1–A3 mathematical constructor and source-only evidence now explicit; actual native attachment, B/A4 character/fusion authority, actual signed modular or char0 maps and full ambient roundtrip, P6 actual inhabitants/kernels remain. No CI, no endpoint promotion.


## 25 November — CONTROLLING sparse original character and central-signature weld

[Exact sparse parity, nonvanishing Weil trace and remaining source selection](../../physics/Monster3BSparseCharacterParityAndWeilTrace20261125.md). For literal j=C² inverting B, every b j conjugate to j by squaring automorphism and outer C conjugates z j to z² j. Thus tau=tr_Ss L_s(j)=(chi_W(j)-chi_W(zj))/3, full 196884 trace. Ranks (90±tau)/2. Zero-sector trace=(chi_W(j)+2chi_W(zj))/3 retained. Expected full traces 276,78 imply 12/78 and W0 trace144, not observed here. New sparse native consumer verifies literal Weyl chart and one actual 2B conjugator, reads j,zj,z²j,C via chi_G_x0. 508 exact reduced checks passed, matching committed blobs. General inner zero-affine Weil trace never vanishes: conjugation permutes symmetric Weyl basis of End(H_s), trace norm squared=3^dim ker(M-I). Thus full original central Fourier trace divided by tr K_s(h) gives actual multiplicity character using three original words, no 2187-word average; sign split from h,hj, zero sector preserved. Exact pinned ATLAS seven words/both phases 14/14 norm checks, identity729, J/DE/R/Q1, D/E27; exact Fourier inverse passed, matching committed blob. All inner words commute with j, so one verified 2B conjugator gives same original G_x0 oracle. Native actual trace and literal model inputs unavailable here. New GAP central-signature source gate asks if exactly one original degree<=12 negative-C2 and <=78 positive-C2 row with marked zeta phase fills each measured block; if unique, representation type follows from semisimplicity and full dual-Sym2 equality. Reports full original restriction and source C/j/zj/z fingerprints from stored fusions. Source-written, not executed; uniqueness not assumed. Independent original BMW published section6 confirms class20 quotient over class19, raw selected 12/78 source rows still need audit. If central-signature gate succeeds with authentic source action and ranks, no dense native 90D or full BW decomposition needed for existence/type; preserve BW row attribution separately and exact coordinate seed/inverse evaluation. A1–A3 literal replay, B/A4 source inventory and native trace, C ordinary source-cover attachment, L10C modular or char0 witness as alternative, L12 full ambient roundtrip, P6 actual proof inhabitants/kernels. No active checkpoint code change.


## 25 November — controlling stop rule: geometry before redundant execution

The intrinsic closure audit (E1–E4) is the mathematical dependency graph. Its A–C source premises imply the actual characteristic-zero representation type and the bidirectional finite-choice/group-algebra construction. The previously reported original GAP run already selects the faithful12 and same-phase dual Sym²78 family (source premise B; raw receipt custody remains outstanding). Do not make the new sparse parity trace or central-signature GAP gate mandatory: both independently audit or substitute for B, rather than supply a further mathematical lemma after B. Likewise the positive modular Reynolds lift and direct characteristic-zero coordinate extraction are alternative realization/verification routes, not successive mathematical prerequisites. If raw source custody is needed, first retrieve the existing original manifest/cover/model and original GAP receipts, not rerun the producers by default. Under A–C, rank12/78, standard phase transport, seed-line existence and both inverse laws follow; no new target-basis search, full character enumeration, or full-weight probe is a theorem prerequisite. A full-weight probe is an implementation receipt, not a proof for arbitrary vectors. Preserve original W0 and independent signed seed gauges. Remaining P0 mathematical/formal seam: prove and instantiate the literal K-linear group/action, actual phase projectors and Weyl laws, genuine trace/character identification under B, actual tensor/Hom and N-equivariant inverse with central descent; use the existing Agda/Lean constructors and distinguish source-written from kernel-accepted. Independently authenticate the original A–C source bytes and their common group/phase chart for an unconditional source-bound claim. Numerical coordinate output, native code acceptance and kernel certification remain distinct deliverables, only required for their respective claims. No new execution requested solely to confirm a derived consequence. Attribution remains original Conway/Seysen, Lindsey/Nebe, Barraclough–Wilson/CTblLib and Breuer–Magaard–Wilson, Dietrich–Lee–Pisani–Popiel, ATLAS, Ibrahim and actual JMD donor geometry; DASHI owns the new same-object signed/indexed transport, proof and integration extensions, not the original representations or classical theorems. No completion flags promoted.


## 25 November — CONTROLLING signed formal endpoint composition

[Exact composition and residual source ledger](../../physics/Monster3BSignedFormalEndpointComposition20261125.md). Recent donor sources #1552 ordered cube (a1cb9531) and #1551 punctured factor chart (d9e0782c): preserve indexed source/target arrow and distinguish equal-cardinality carriers; no transfer of unrelated metric or RH claim. Lean #47 now has signed cross-phase Hom action by conjugation, derived linear vacuum arrow, full-vector entry factorization, honest inner group action and actual LinearMap.trace character, signed negative gauge and reverse outer square from C², ordinary true tensor and weight coordinate BIDI, N=EH equivariance and central quotient descent, original three-projector range split retaining W0. Rollup head 75fb26a1. Agda signed ordinary composition (a69f4f7d) consumes literal phase restrictions and actual weight frame, pointwise inverse and source-derived inverter arrow. Universal central Fourier identities and diagonal kernel cancellation 36/36 exact SymPy, matching blob 1d7dd99d23a166ce7b9077396dabf925d8f6bd64. Existing character theorem IsAlgClosed cannot be used directly over Q(zeta); mathematical K-descent by unchanged rank of finite intertwining system under complex extension and Schur one-dimensional Hom, with determinant-grid generalization. This proof remains to be kernel formalized. Actual A–C attachment, literal Conway and Weil action/projector inhabitants, true B trace equality, source ordinary vacuum iso, actual signed N-equivariant tensor instance, scalar-field law and kernel acceptance remain explicit. No native or GAP rerun, no active char0 dependency changes, no proof flags promoted. Sparse character and modular/dense numerical routes stay optional. Attribution preserved per linked audit.


## 25 November — CONTROLLING direct cyclotomic character cut

[Direct original-field proof and custody audit](../../physics/Monster3BDirectCyclotomicCharacterMaxCut20261125.md). Existing Integration/FiniteCharacterDeterminesSimpleRep and pinned Mathlib character/Hom pairing remove separate base-change formalization. Corrected characteristic-zero cast hypothesis and pinned Fintype.card API. Sophie Morel's rank-one End implies simple proof direction reused with attribution; not the converse over arbitrary fields. New Lean literal central involution eigenspaces, half-projector inverse and actual restricted action; traceSum/traceTwist derive both parity block characters from the single same-object B identity and source central signs; source norm-one implies actual End and cross Hom rank one directly over Q(zeta), every nonzero cross Hom is iso. Integrated Lean head fea0e287. No additional numerical intertwiners, GAP, native or CI. Original raw receipt names searched but not found among accessible files. Exact remaining source A–C attachment, literal K-linear Conway/Weyl/normalizer inhabitants, original B equality and source norms/signs, ordinary block isos to existing tensor signed descent, and kernel acceptance. All new modules source-written only. No completion flags promoted.


## 25 November — CONTROLLING original projected character and ordinary gauge weld

[Exact source observer derivation and provenance](../../physics/Monster3BOriginalProjectedCharacterWeld20261125.md). Hopf #1554 P0H original spectral observer is methodological donor only. On actual W use Q=inc_s T0 U0 res_s; rectangular trace cyclicity and prior full Hom entry law give Tr(Q rho(g))=K00 chi_S(g). Q is original group-algebra central/weight projection sum over z^a b, with phase coefficient zeta^(-sa)/2187. On BW paired source model same observer kills W0 and opposite phase, compresses common Weil factor to rank one, and gives K00*(chi12+chi78). Original marked full word-character equality and common nonzero canonical K00 then imply actual Hom character identity; no independent 90D trace assumption after A-C, no word enumeration or native replay required for the mathematical identity. Lean new MonsterProjectedOriginalCharacter, MonsterSourceTensorObserver, MonsterOrdinaryGaugeFromSourceCharacter derive these trace transports and combine direct K block isos into an equivariant ordinary vacuum gauge; integrated head cc01a953. Original BW archive and BMW sections 6/7/9 reopened; printed filtered candidate row coordinates are distinct from CTblLib raw Irr coordinates. Actual marked original projector expansion, Conway/Weil actions, BW source tensor/word fusion and source selected norms/signs, ordinary original Lindsey cover attachment and kernel inhabitants still outstanding. Original raw workstation receipts not recovered. No new symbolic regression, native/GAP/CI run or active char0 dependency changes. All formal changes source-written; no completion promotion. Attribution per linked audit.


## 25 November — CONTROLLING literal six-axis source attachment

[Original Weyl frame and source custody cut](../../physics/Monster3BLiteralWeylSourceAttachment20261125.md). Reuse original E producer's marked z, A_i,B_i and exact B_i A_j=z^delta A_j B_i. In nontrivial phase t, original P_x=T_x P T_x^-1=729^-1 sum_b t^(-b.x) rho(B_b), with orthogonality/completeness derived by six one-axis Fourier sums; actual vacuum range and inclusion/recovery give the full frame and Weyl Hom laws, with zero sector kept separately. Q_s is the original joint projection sum, not a new observer input. Explicit left versus native right-action convention retained. Lean MonsterLiteralWeylFrame sourceActionEquiv/sourceVacuum/sourceFrame and originalObserver instantiate literal word formulas on supplied original action; source Fourier proof inputs, actual marked rho/words and kernel acceptance remain. Lean head 21791c73. Reopened committed Lindsey source packet b0f96b37 and Nebe 2025 section 6 original symmetric square (degree78 row80 for chosen 12), opposite direct versus same dual central phase; no unmarked row assignment. CTblLib 1.3.11 original data download blocked; raw workstation manifest/cover and GAP receipts remain unavailable; exact existing paths and reported hashes in audit, retrieve without rerun. No native/GAP/CI or new symbolic acceptance campaign; no checkpoint dependency changes or completion promotion. Attribution preserved.


## 26 November 2026 — binary Leech polarization and source-preserving gravity comparison

Cross-PR donor, not a new native certificate: [Hopf #1554 P0AN–AO](https://github.com/chboishabba/dashi_agda/blob/7914ec131be930eb8baa237f3489930ec91c2d24/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md), [literal Leech checker](https://github.com/chboishabba/dashi_agda/blob/7914ec131be930eb8baa237f3489930ec91c2d24/scripts/check_hopf369_p0ao.py), [revived Paper 2 gravity manuscript](https://github.com/chboishabba/dashi_agda/blob/db4e6fdad79e91043fb5449f77e326cdc6c16c1b/Docs/papers/drafts/Paper2SourcePreservingEinsteinIsraelGeometry.md). Existing ternary central-character, original ATLAS and Suzuki/multiplicity selection remain Paper 10's main theorem and acceptance path. This is a comparative section, not replacement or resolution of its current P0.

### Binary versus ternary polarization

The literal rank-24 Leech lattice was constructed from the extended binary Golay code and odd glue vector, with even unimodular rootless Gram G. Its 196560 minimal vectors give 98280 distinct nonzero singular mod-two classes with exactly two minimal representatives, antipodal. This is a selected subset of the singular locus, not the whole locus. On L/2L use q(x)=x^T G x/2 mod 2 and b(x,y)=x^T G y mod 2. In a lattice basis set U=triu(G,1)+diag(G_ii/2) mod 2; c(x,y)=x^T U y gives squares q and commutator b. Binary elimination yields twelve hyperbolic pairs and an invertible chart P, with P^T G P=J modulo 2. This is the plus-type extraspecial extension of order 2^25. The actual lattice coordinate chart, signs and cocycle are retained.

For Weyl coordinates x=(a,b), V=tril(J,-1). D=P^T U P+V is alternating symmetric over F2 and f(x)=x^T triu(D,1)x has polarization D. The exact extension BIDI is (x,s)->(P x,s(-1)^f(x)), with inverse using P^-1 and the same phase. In the standard carrier C[F2^12], T_a e_x=e_(x+a), M_b e_x=(-1)^(b.x)e_x, so M_b T_a=(-1)^(a.b)T_a M_b. Fourier diagonal projectors and translations generate End of the 4096-dimensional carrier. This is a concrete binary Weyl representation of the chosen Leech extension, not a generic claim of a new Stone–von Neumann theorem.

The ternary source uses six position coordinates, two nontrivial central characters and a 729-dimensional irreducible representation; the binary source uses twelve positions and one nontrivial central sign. In characteristic two the quadratic refinement and lift phases are indispensable. Do not transplant the odd-prime quadratic correction by dividing by two. For a selected lattice isometry A, D_A=A^T U A+U has zero diagonal; a phase with polarization D_A gives an extension lift. Lift discrepancies under composition are linear characters. The selected octad sign flip has a naive lift-square character, removed by a solved linear correction. This is an exact candidate input to the existing compensation and normalizer machinery, not a canonical FLM lift or actual Monster class assignment.

The previous local P0AN–AO receipts report 589824 binary generator-coordinate Weyl checks, complete minimal-vector enumeration and 4672 extension/basis/random controls plus all-index algebraic identities. They are source-linked prior runs, not newly reproduced for this manuscript. The 24 oscillator directions times 4096 twisted ground states produce 98304 coordinates. Actual canonical FLM theta-lift quotient, oscillator fields, mixed modes, selected Conway generators, projective gauge and relation checks remain distinct. Carnahan's integral Monster form and FLM's actual VOA exist mathematically; this does not identify the selected source representation with them. Consume the original Y443 all-mode and two-generator transport owners rather than new abstract record copies.

### Physical rank-24 comparison (Paper 2 consumer only)

The published M² spectrum splits the 27D graviton into STF24, scalar and vector (299+1+24), and p-form carriers into W⊕W with W=sum_{p=1}^5 Lambda^p R24 tensor R^{C(4,5-p)}. Each half has 98280 states. Natural inversion has 43608 even and 54672 odd per half; including graviton scalar/symmetric and vector gives full (87516,109368), distinct from lattice VOA (98580,98304). Parity times exchange of identical copies gives the latter dimensions without discarding signs; orthogonal BIDI w± -> (w±,±(-1)^p w±)/sqrt2. This is a selected C2 character repair, not literal natural rotation or actual full Monster action. For a three-cycle of three rank-eight blocks the exterior trace polynomial is (1+t³)^8; real order-three multiplicity mixing restricted to each degree gives trace 96-24m for integer 0<=m<=6, never actual V2 3B trace54. Under the separate assumption of an internal Monster action commuting with unbroken SO24 on these finite polarizations, all multiplicity spaces have dimension <=12, hence the action is trivial by the minimum nontrivial complex Monster degree. These are restricted non-descent certificates, not an exclusion of all nonlocal or boundary symmetries.

The original M² interaction tensors are unspecified by the published source. The prior AO algebraic Reynolds projection onto exchange-invariant coefficients is a candidate source constraint, not a gauge-complete interacting action; no new physical Monster realization. The gravitational paper independently retains a positive massive AdS3 tensor gap under its boundary conditions, and the Weyl curvature discriminator prevents identifying a different compact product by Ricci or central-charge agreement alone.

### Exact remaining work

Keep original Paper 10 P0 (actual marked E action, original selected Weyl frame/Hom, normalizer, Suzuki character and kernel) separate from binary extension P0 (canonical FLM quotient/phase section, actual source Conway action, projective lift composition, twisted oscillator and mixed-mode preservation). Reuse the existing ternary cocycle, signed support and sparse/factored operator compilers only after matching binary source conventions; a future matrix-free binary kernel and actual relation replay would be useful independent deliverables. Novelty review must distinguish classical Golay/Leech, FLM, Carnahan, finite Weyl/Clifford and Monster theory from DASHI's source-specific executable chart, sign and action comparisons. JMD and other donor attribution is unchanged and applies only to evidenced contributions. No new native kernel, CI, GAP, mmgroup, full dependency run or physical promotion here.
