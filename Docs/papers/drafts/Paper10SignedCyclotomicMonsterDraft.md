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
