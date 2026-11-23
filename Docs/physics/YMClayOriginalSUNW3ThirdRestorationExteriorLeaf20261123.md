# YM P0 / W3 — third restoration exterior-leaf cut (23 November 2026)

Scope: **original periodic four-dimensional SU(N) Wilson source**, side four, two native time steps, eight tube walls, and the three transverse sections H0,H1,H2. This is a necessary Haar-leaf/finite-jet result only. It is **not** a physical weak-coupling, tau-interval, cutoff-uniform, CMP119/122, or mass-gap estimate.

## New geometric cut

Let B=T_2 union {H0,H1,H2}, and E be the 1,525 other restored original plaquettes. Count links of p outside the union of boundary links of B. Direct original L4 incidence enumeration finds **76 plaquettes with 3 exterior links and 1,449 with 4**. No exterior plaquette has fewer than 3. Two distinct native original plaquettes share at most one positive link.

For any multiset of at most three restored insertions containing an exterior plaquette, the corresponding joint cumulant with F and G vanishes under the wall-only reference measure:

* If 3 distinct exterior plaquettes occur, each exterior plaquette has at least 3 links outside B but can share at most 2 with the other two, leaving a private Haar-leaf link.
* If 2 distinct exterior plaquettes occur (with multiplicities), an exterior plaquette with multiplicity one has at least 2 private links; its insertion integrates to zero. With only one exterior plaquette repeated, that plaquette is independent of the entire B-observable sigma-algebra via a private link; connected cumulants involving F,G vanish.
* Any included section insertions use only B links and cannot remove the outside Haar leaf.

Therefore, in the **original** restoration Duhamel identity at tau=0, with common bare wall beta,

```
C'''(0) = beta^3 sum_{i,j,k=0}^2 kappa_{mu0}(F,G,H_i,H_j,H_k).
```

Exactly 27 ordered section triples survive as *candidates* from 1,528^3 ordered restored plaquette triples. Some of those 27 may vanish by group selection; **no value for the third derivative has been claimed**. This statement is for the original d=2,L=4 source, not arbitrary L,d.

## Periodic wrap negative control

A separate exact incidence sweep for all L=3..6, all 1<=d<L and all three spatial planes finds four off-section plaquettes with only **two links outside the expanded section-and-wall support** when d=L-1. Thus the stronger >=3-leaf premise is false near maximal periodic separation. Do not generalize the third-jet conclusion using this premise without additional geometry. The earlier >=2 exterior-link claim relative to the original wall+endcap support is a separate statement and is not contradicted.

## Acceptance / trust boundary

The third-order exterior reduction is a finite elementary Haar-invariance argument conditional on the original central tube transfer/source identification already documented in this PR. Local exhaustive Python original-incidence checks found L4,d2 count (76,1449), zero two-or-fewer, and wrap negative controls. This note does **not** claim Agda kernel execution, a new continuous group integral, full third-jet coefficient evaluation, first actual nonzero exterior polymer, or tau>0 absolute convergence.

Next physical gate: identify the actual first nonzero exterior **connected and source-normalized** activity, including repeated plaquette multiplicities and Haar center selection; then prove genuine source-to-CMP119/122 marked absolute cluster identity with small/large-field and cutoff-uniform shell controls. Prior Wilson/Haar/Balaban and existing F19/CMP116 owners retained.

## First exterior geometric activity candidate — five new plaquettes

Enumerating all original elementary three-dimensional cubes on L4/d2 yields **32 cube boundaries containing exactly one wall-or-section face and five exterior faces**, plus two tube interior cubes whose six faces are all in the wall+section support. An example is the (time,spatial-a,unused-spatial-c) cube based at the origin, meeting the tube on the wall face (origin;time,a); its other five boundary faces are native exterior plaquettes.

The cube is a closed six-face surface, and its five external plaquettes have no uncovered external boundary links once combined with the one pre-existing wall face. Hence order five provides an **explicit necessary-support candidate** for an exterior connected activity. This does **not** prove that the fifth-order connected cumulant is nonzero after SU(N) character integration, subtraction/normalization, or center selection; those are separate acceptance gates. This cube census also does not exclude other non-cubical lower-order mechanisms merely from counting elementary cubes.
