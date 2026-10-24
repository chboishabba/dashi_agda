# Monster moonshine and AdS3 gravity: literature-grounded KK/braid max-cut

## Precisely what Wikipedia describes
Witten (2007), Three-Dimensional Gravity Revisited, arXiv:0706.3359, proposes an AdS3 pure/chiral gravity relation to the extremal holomorphic c=24 Monster CFT. Its character is J(tau)=j(tau)-744=q^-1+196884q+21493760q²+... . This is a research proposal, not a proved equivalence to full physical 3D quantum gravity.
BTZ entropy/microstate asymptotics, Rademacher-series candidate gravity partition functions, and JHEP 2017 Monstrous Entanglement computations are concrete research comparisons. Later gravity partition-function consistency caveats are essential.

## Exact concrete implementation
scripts/check_monster_ads3_extremal_partition.py independently computes E4, Delta=q product(1-q^n)^24 and J=E4^3/Delta-744 over integral truncated formal series. Checks J=q^-1+196884q+21493760q²+... and 196884=196883+1. This fixture was reproduced independently locally. It is not a VOA trace or gravitational partition-function proof.

## Reuse existing owners, avoid physics conflation
PR #1179: Jack Daniels/Ogg, Monster support, jCoarse/jFine, Fricke, Albert/F4 and physical-gravity boundaries.
PR #1162: Monster 3B and C3 entropy/gravity candidates, state-to-stress and observable promotions.
PR #1239: signed SSP FRACTRAN and C3 mirror, punctured balanced T9, continuous affine braid, Pin/O2 and actual Ricci-flat 5D KK pp-wave family.
The integer identity 47*59*71=196883, prime support, signed involution and braid symmetry do not substitute for an actual graded Monster VOA, AdS3 boundary dynamics, or physical stress tensor.

## Highest-leverage residuals
1. Connect existing Monster VOA graded traces to literal J coefficients; distinguish full level multiplicities from Virasoro primary degeneracies.
2. Connect actual SL2Z modular S,T transformation theorems and Rademacher sums to J and McKay–Thompson series; finite coefficient checks are insufficient.
3. Select explicit AdS3 gravity action/boundary conditions with Brown–Henneaux c=3ell/(2G3)=24, precise BTZ spectrum and partition function including saddle issues.
4. If a KK link is desired, build a *new justified* dimensional reduction of a higher-dimensional metric to AdS3 with internal factors, flux and matter fields. The current 5D null pp-wave has no established AdS3 boundary or Monster CFT dual.
5. Braid/SSP only join this physical picture through an actual grade-, symmetry-, stress- and observable-preserving map. Preserve C3 translation versus C2 conjugation no-go results.
6. dashiQ should distinguish code-level sign changes from measurable holonomy and modular spectra, with independent controls and locked parameters.

## Sources
https://en.wikipedia.org/wiki/Monstrous_moonshine
https://arxiv.org/abs/0706.3359
https://link.springer.com/article/10.1007/JHEP10%282017%29147

## Acceptance
python3 scripts/check_monster_ads3_extremal_partition.py
Exact q-series fixture locally independently checked. Exact-head Agda kernel, full AdS3 duality and physical KK/braid equivalence have NOT been established.
## 2026-10-24 source-backed physical observable update
Read `docs/monster369-physical-braid-defect-observable-maxcut-20261024.md` as the canonical physical visibility ledger. Carnahan's generalized moonshine (twisted trace/modularity) is proved; Witten's AdS3 Monster dual remains conjectural. Real Monster 2A and 2B defects have different CFT q-character coefficients and exact weight-two charge splits. The Monster has 27A and 27B elements whose ninth powers are in 3B; for g of order27, the recorded B3 modular matrix sends (g,1) to (g^13,g^19), but an actual certified g-twisted trace, multiplier and marked-torus comparison are still necessary. A chosen standard braided Ising anyon extension sends this braid to -I, which is invisible to isolated probabilities but potentially accessible through controlled relative interference. Distinguish the separate 3A three-state-Potts/noninvertible golden-ratio defect from the 27->3B lane. Real physical AdS3 visibility requires a bulk gauge/symmetry-defect/Wilson line matching the SAME boundary twisted observable, not the original KK null vacuum alone.


## 2026-10-24 operator max-cut: new terminal branch choices
See `docs/monster27-voa-cube-charged-links-braid-rank-gauge-maxcut-20261024.md`. Actual Monster Vnatural2 C27 source eigenspaces are rank-stratified [7298,7295,7296,7290], so a chosen spatial M (mod3 reduction of B3) sends three four-cycles through alternating ranks7290/7296 and cannot act as a full-fibre unitary without at least 36 spectator dimensions or a 36-dimensional truncation. It changes charge conductor 9→27, so it is not a C27 power automorphism. Strict native nearest-neighbour cube locality needs 36 added nonlocal bonds to have M symmetry. These two 36 values do NOT define the same physical cause. Actual local-Python link implementation now pays one of two different constructions: **weighted charge chart on original 54-edge cube** with 54 endpoint-charged bifundamental matter links, 36 gauge-invariant plaquettes and eight Bianchi identities, but no site M symmetry; OR **uniform onsite Monster representation on the minimally extended 90-edge graph**, where a standard Z27 edge connection is M-covariant, commutes with discrete coboundary/gauge shifts and preserves 36 transported native Wilson loops. This only realizes finite mod3 braid quotient M^4=1, not full hyperbolic B3/SL2Z or Monster projective anomaly. The existing `Monster27VOAVertexModeChargeSelectionExact.agda` now requires actually nonzero source-certified Vnatural modes and still lacks specific conformal-grade-two matrix elements/physical coupling. Rigorous bulk completion requires standard principal U1 KK connection, matter stress/Einstein dynamics or selected AdS3 twisted VOA multiplier/Wilson dictionary. 


## 2026-10-24 source-audited Pareto update (supersedes claims of all 54 literal VOA mode amplitudes)
See `docs/monster27-cube-voa-source-projectors-pareto-maxcut-20261024.md`. Actual McKay–Thompson series of 27A/B,9B,3B yield ordinary UNTWISTED twining traces `(3,0,54)` on Vnatural_2, not g-twisted trace values. ATLAS power maps and 2026 Breuer–Magaard–Wilson ordinary character-table verification cited. New exact-source polynomial projectors `Pi_k=(1/27)Σ ζ27^{-kj}ρ(g)^j` give 27 individual eigencharge sectors of ranks 7298/7295/7296/7290. More cheaply, four **rational conductor projectors** `Q_d=(1/27)Σ Ramanujan_d(j)ρ(g)^j` give ranks 7298/14590/43776/131220; exact orthogonality and completeness checked over Q[C27] and F127[C27]. mmgroup supports actual Monster rep mod127, so this is the P0 computational cut after a reproducible certified order27 Monster word, not a claim that mmgroup was run.
Existing `MoonshineGriessAutomorphismClassificationExact.agda` already owns actual Griess product `u_1v` and unit `e=omega/2`. Thus `u_k{}_1 e=u_k` is an established nonzero **fixed grade-two** mode for all charge eigenstates, and its CHOSEN spatial chart covers exactly SIX cube edges incident to origin. The other 48 adjacent charged pairs do not yet have specific nonzero weight-two Griess products/source amplitudes. Li's VOA nondegeneracy theorem does not pay those fixed-n matrix elements. New conditional source-specific weld `Monster27GriessNeutralSpokeActualVOAWeldExact.agda` is source-written, not kernel checked.
Exact cube graph automorphism ∩ charge power-map symmetry is only `{identity, full coordinate inversion}` (C2). The prior endpoint-weighted local gauge parameter map alpha->k alpha has a 3^13 kernel and is non-faithful; old gauge/Bianchi algebra remains valid, but should not be promoted to a faithful Z27 local gauge group or ordinary U1 KK connection. `mmgroup.axes.Griess` supports only limited 2A-axis/easy-factor multiplication according to its docs; full arbitrary 48-source-edge Monster products remain unsupplied. All details, acceptance and attribution in the new doc.
