# 26D K27 → 24 transverse → B2/C22 duality → M24 signed-duad max-cut
**Date**: 2026-10-24; **owners**: Agda hyperfabric PR #1249 and Lean4 TOE PR #84.
**Claim boundary**: rigorous source-labelled finite 24D representation diagnostics and a selected fixed-background 26D B-sector. No physical 27D uplift, Monster Tate identification, K27 non-linear algebra, worldsheet BRST, full Einstein solution, or Clay theorem.

## Primary literature and preexisting repo theorem owners

1. [Glennon & West, *K27 as a symmetry of closed bosonic strings and branes* (2024/25)](https://arxiv.org/abs/2409.08649): K27 low levels include 26D metric, dilaton, 2-form B2, dual 22-form C22, dual dilaton 24-form, dual graviton mixed 23,1. Original K27 non-linear realisation and duality are **published source mathematics**. No in-house reconstruction claimed.
2. [Glennon, *Bosonic M-Theory From a Kac-Moody Algebra Perspective* (2025)](https://arxiv.org/abs/2501.03000): 27D E27 lift dual-generator and proposed commutator obstruction; the high-level commutator was **not computed** in the source. Distinguish tensor rank from algebra generator / non-linear action.
3. [Bosonic string low-energy action derivation](https://math.berkeley.edu/~kwray/papers/string_theory.pdf), §13.26: `S26 ∝ ∫√(-g)e^-2Phi(R+4(dPhi)^2-H3²/12)`; bosonic physical SO(24) little group, 24×24 closed state tensor, 299 symmetric traceless graviton, 276 antisymmetric B2, 1 dilaton.
4. Original [ATLAS M24 on 24 points](https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M24G1-p24B0): involution 2A cycle shape `1^8 2^8` and 2B `2^12`; 3A `1^6 3^6`, 3B `3^8`.
5. Original [ATLAS M24 on 276 points](https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/M24G1-p276B0): action on *unoriented* two-subsets (“duads”) with class 2A fixed 36, 2B fixed12, 3A fixed15, 3B fixed0; character decomposition 1+23+252.
6. Agda **existing primary theorem owners**, already in master: `DASHI.Moonshine.LeechWeightTwo196608BridgeExact` records `Sym²_0(24)` coordinate count 299 with split `23+276`. `DASHI.Moonshine.OggSSP2BM24DuadPair24AuthorityExact` identifies ATLAS p276 carrier with duads (pair24), and explicitly withholds matching of Carnahan–Urano 2B Tate 276. Preserve the original sources and authorship.

## Positive: exact 26D target B2/C22 field sector

For `H3=dB2`, the actual B-field EOM at fixed string-frame metric is
`d(e^-2Phi *26 H3)=0`; locally define `G23=dC22=e^-2Phi *26 H3`.
The 22-form potential rank is `26-3-1=22` and its **transverse** physical polarizations are `C(24,22)=C(24,2)=276`. This is prior differential geometry and string field theory, not a new 26D physical prediction.

The new script `scripts/check_k27_26d_B2_dual22_dilaton.py` constructs a NONCONSTANT dilaton `Phi=s t`, a field `B12=q e^(2st)/(2s)`, hence `H012=q e^(2st)`, and the exact Lorentzian Hodge component `G3..25=q`, with the local dual potential `C4..25=q x3`. It verifies the nontrivial B EOM `∂0(e^-2Phi H^012)=0`, closure of H/G, dual EOM, epsilon sign and dilaton-weighted norm identity for 4 independent exact slopes/charges. The field is NOT a full Einstein+dilaton solution: on flat g, the `00` metric source equation has the explicit nonzero H contribution `-H012²/2`. No selected K27 generator action is constructed.

**27D form rank firewall**: for `G27=diag(g26,r²)` with the circle orientation chosen, `F4=H3∧dy` has `*27 F4=(1/r)*26 H3`, so a **23-form field strength with 22-form potential** has the correct tensor rank. That is a positive *rank* commutation, NOT an `E27→K27` same-generator representation embedding; Glennon's obstruction concerns the latter. The existing original Agda Hodge/gauge/GR source owners should consume the physical form identities only once source units and stress are matched.

## Positive: exactly 276 oriented duads are the 24D exterior-square B2 module

A string massless state has 24 transverse directions. Hence
```text
Sym²_0(R^24): 24*25/2 - 1 = 299 (graviton),
Lambda²(R^24): C(24,2) = 276 (B2),
R: 1 (dilaton).
Total = 299 + 276 + 1 = 576 = 24*24.
```
Under positive orientation, the transverse Hodge star gives the **SO(24)-equivariant orthogonal isomorphism** `Lambda²(R24) ≅ Lambda²²(R24)`: on basis `e_i∧e_j`, take complementary 22-subset and multiply by Levi-Civita sign. Our script verifies the map **on all 276 basis duads and all four ATLAS source-class permutation representatives**, preserving both the involutive Hodge relation and natural signed action. This is not a theorem that the 276-leveled Moonshine Tate module has this action.

**Constructive missing ingredient:** the ordinary M24 p276 carrier is *unoriented duads*, whereas the physical B2 basis is an oriented two-form: `[i,j]=-[j,i]`. The needed same-carrier **orientation line** (signed-duad local system) changes the action by the pair-order sign. This is the precise positive BIDI candidate for the user's orientation/signed-zero hyperfabric programme. The true trit signed-neutral states `minusZero/neutralZero/plusZero` are **not** this Z2 orientation line unless a typed translation is supplied. Adding sign data is mathematical source content, not an automatic Monster or physical identification.

## Concrete NO-GO: NATURAL M24 p276 DUADS cannot equal physical B2 (276)

The character of the **ordinary duad permutation module** at `g∈M24` counts unordered pairs fixed by g. The character of `Lambda²` of the natural 24-point permutation module is `(χ24(g)^2−χ24(g²))/2`, which uses a **minus sign for reversed pair orientation**.

| ATLAS class | fixed natural 24 | ordinary duad trace | oriented B2 wedge trace | graviton Sym²_0 trace | 299+276+1 character |
|---|---:|---:|---:|---:|---:|
| 2A (`1^8 2^8`) | 8 | **36** | **20** | 43 | 64 |
| 2B (`2^12`) | 0 | **12** | **−12** | 11 | 0 |
| 3A (`1^6 3^6`) | 6 | 15 | 15 | 20 | 36 |
| 3B (`3^8`) | 0 | 0 | 0 | −1 | 0 |

**No-go theorem at declared action:** two characteristic-zero representations with different characters cannot be linearly equivariantly isomorphic. Thus **ATLAS p276 ≠ Λ²(R24)** under the specified natural `M24 ⊂ SO(24)` action. The 2A and 2B are independent witnesses. The ATLAS source confirms both class cycle types and actual p276 trace; the executable independently calculates the signed wedge and graviton traces. This distinction is stronger than equal dimensions and is operationally falsifiable.

**Positive repair:** replace ordinary duad scalars by *oriented signed-duad fibres*, not the originally sourced p276 representation. This exactly creates the exterior-square action; it does not repair the original p276-to-Carnahan-Urano-Tate action, and does not make an actual physical string VOA field.

**No identification by count:** 299 in Leech chosen weight-two trace-free quadratic coordinates matches 26D graviton polarization dimension, and 276 in Leech offdiagonal coordinates matches B2 count, but the symmetric quadratic slot is not the antisymmetric B field; even when both have the same offdiagonal basis cardinality, the group representations differ.

## Executable/Agda evidence

- `scripts/check_k27_26d_24d_polarization_m24.py`: all 276 oriented B2↔22 dual-basis maps; ATLAS 2A/2B/3A/3B class-actions, source p276/wedge character mismatches; 299/276/1 decomposition. Executed equivalent exact source locally PASS.
- `scripts/check_k27_26d_B2_dual22_dilaton.py`: sympy exact nonconstant Φ local field-sector B EOM/dual EOM, Lorentzian epsilon/hodge norm, 27D circular rank and metric equation *failure*. Executed equivalent local source PASS.
- `DASHI/Unified/HyperfabricK27StringLittleGroupM24DuadDiscriminatorExact.agda`: consumes already existing original Leech299 and M24-duad276 theorem owners and records source-class 2A trace contradiction `36≠20` in Agda. Source-written **Agda kernel NOT checked**. External class existence/representation theorem sourced to ATLAS, not recreated by a new M24 generator group.

## Phase/gate decisions

- **C0 source owner audited**: actual 26D K27 2-form/22-form/dual scalar/graviton and original master Leech/M24 299/276.
- **C1 selected 26D field test PASS at stated fixed-metric sector**: varying dilaton + H field, local C22 dual, with explicit **Einstein metric residual FAIL**. Next only source-selected curved/source-matched full Einstein/dilaton solution.
- **C2 SO24 massless decomposition PASS**: signed Hodge map all 276; correct graviton/B/dilaton 24×24 representation.
- **C3 M24 wrong-representation identification REJECTED**: ATLAS p276 duads vs string B2 Λ² characters 2A 36/20, 2B 12/−12. A signed orientation-line lift **does** supply Λ² representation mathematically; do not call it p276 or Monster Tate.
- **C4 actual quantum K27/VOA/Monster bridge OPEN**: same selected 26D physical state/BRST and vertex operator modes + two-form/22-form local stress and K27 generators, Hodge/duality including source-metric backreaction. No full symmetry extension to E27.
- **C5 27D simple EH+3form still REJECTED** by 125/121 dilaton mismatch. Added scalar off-shell patch fails automatic 27D free-scalar EOM. No claim all alternative 27D theories fail.
- **C6 Clay independent**: chosen 26D form identity cannot discharge canonical YM/NS cutoff-uniform estimates, RH signed far-mu, BSD, Hodge or P≠NP.

### Pareto next

**Do not manufacture a new 27-dimensional ontology.** In 26D, certify one source-selected nonflat B/φ/g common-action solution (existing nonflat finite GR donor may help), then attach the exact same physical local duality operators and K27 level-one/dual-level generators. Separately test whether user-signed-zero fine fibres can model an **orientation local system** without conflating C3 with Z2 or nonoriented M24 p276 with antisymmetric B. Crosspolinate only if concrete fields/operators commute.


## Major stronger subsequent consumer: nonflat coupled EOM now available

A later same-PR reference model (source: standard SU2 WZW/linear dilaton) closes the *leading-order* NS-NS EOM that the earlier flat B-only example could not.
See `docs/hyperfabric-k27-26d-su2-nsflux-linear-dilaton-worldsheet-maxcut-20261024.md`.
`M26=R^(1,22)×S3_r`, `H=(2/r)vol_S3`,
`Phi=x_spacelike/r`, original 26D string-frame equations:
`E_g=0`, `E_B=0`, `E_phi=0`; sphere curvature and H-squared genuinely nonzero. SU2 orthonormal-frame curvature/parallel flux and 6 rational radii source-checked. Global B must be patchwise, with quantized H class.

This is an actual improvement in **selected leading 26D physical continuum source**, not a reason to lift ATLAS p276 unoriented duads to the physical B2 module. Existing 2A/2B no-go stands.
Worldsheet finite-level Sugawara `k+2` correction means the unshifted classical slope leaves `c−26=12/[k(k+2)]`; a genuine quantized CFT candidate must use the corrected charge and still pay state/BRST/global string conditions. The 27D E27/K27 missing-dual-generator issue remains independent.


## Final global-curved target correction / positive full-source dual (2026-10-24)

**Target SAME-BACKGROUND advance:** the subsequent selected
`R^(1,22)×S3_r`, `H=(2/r)volS3`,
`Phi=x¹/r` leading continuum solution now has **explicit
patch potentials B_N/B_S** with nontrivial gerbe flux
`∫S3 H=4pi²r²` and **explicit global noncompact C22**:

```text
vol26=vol_(R1,22) ^ volS3,
*26 H3=-(2/r)vol_(R1,22),
beta22=dt ^ dx² ^...^ dx²²,
C22=-exp(-2Phi) beta22,
dC22=exp(-2Phi) *26 H3.
```

The local duality comes from the **same** nonflat
g/H/Phi that solved the leading NSNS field equations.
Although the gerbe H is non-exact on S3 and no global
B2 exists, the dual 23-form on noncompact R1,22
is exact and admits the explicit C22. This
distinguishes differential-form source data from
the still-unbuilt `K27` 22-form **Lie generator**.

Existing SO24 transverse `299+276+1=576` is
the *flat-space massless little-group* decomposition.
The actual S3 flux / spacelike gradient background
breaks global SO24 symmetry; its 276 two-form
polarisations are NOT automatically one global
M24-equivariant field multiplet in this curved source.
The original Atlas M24 p276 versus oriented Λ²
2A/2B character mismatch remains a rigorous
comparison of the stated **abstract 24-point natural actions**.

**No Z2/C3/U1 identity:** oriented duad is a Z2
sign local system, user signed-neutral phases rotate by
C3, and the NS gerbe has U(1) 2-form cocycle.
A rotation C3 cannot supply a nontrivial
Z2 reversal via a group homomorphism
(coprime orders). Lean #84 writes the
`threeCycleCannotBeOrientationFlip` group proof,
source-written/kernel unverified. A more elaborate
semantic functor would need to explain its own
group-action changes and observed observables.

See the already-updated worldsheet dossier
`docs/hyperfabric-k27-26d-su2-nsflux-linear-dilaton-worldsheet-maxcut-20261024.md`
and new exact Python
`scripts/check_k27_26d_global_gerbe_dual_cft.py`.
No direct YM/NS/RH/Clay promotion.
