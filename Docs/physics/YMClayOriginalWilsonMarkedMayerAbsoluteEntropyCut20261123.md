# YM P0 / W3 — original SU(N) Wilson two-mark Mayer factor absolute entropy envelope

23 November 2026. **Original current-master source**: native four-dimensional side-four 256 sites, 1024 SU(N) positive link Haar variables, 1536 actual positive plaquettes, actual original closed Wilson normalized real trace two marks F/G on native time 0 and time 2; full original globally unique F19 1/F/G/FG source with 64 ordered R445 coarse link pairs and 896 remaining fine spectators. Existing **actual finite labelled Mayer partition identity** and explicit high-beta activity no-go: [YMClayOriginalWilsonFiniteHaarMarkedMayerPolymerW1W3NoGo20261122.md](YMClayOriginalWilsonFiniteHaarMarkedMayerPolymerW1W3NoGo20261122.md). Existing original P06/R429 animal owner: [YMClayOriginalPolymerAnimalReuseMaxCut20261109.md](YMClayOriginalPolymerAnimalReuseMaxCut20261109.md). This audit does NOT duplicate those producers, or assert a full CMP116 rooted shell.

## Source graph: what changed when keeping the two marks literal

For an original native plaquette p=(x,mu,nu), its four positive fine links are x_mu, x+e_mu at nu, x+e_nu at mu, and x_nu. On the actual L4 torus each fine positive link occurs in precisely SIX original plaquette supports; every original plaquette shares a fine link with exactly TWENTY distinct other plaquettes. The original 1536-vertex plaquette-support overlap graph is therefore degree-20 regular.

In the **true globally marked source**, the Wilson interaction factors at plaquettes F/G REMAIN present, and the two unique global source insertion factors (Lmark,Rmark) have their own literal labels with the exact same four fine-link supports as F/G. We MUST NOT replace the F/G action plaquettes by marks. The actual resulting 1538-label factor graph has 1494 vertices of degree 20 and 44 vertices of degree 21, maximum Delta=21. The two original marked labels are at overlap-graph distance d=3. Exact local native L4 reconstruction checks every vertex and edge.

## A genuinely absolute bound on ONE connected labelled factor

Use the original product-Haar finite source with ordinary microscopic plaquette factors `f_p(U)=exp(beta*t_p(U))-1`, beta>=0, original real trace t_p in [-1,1], and the two source insertions `s F` and `t G`, as in the preexisting 22-Nov source-exact factor-label decomposition. Let S be a labelled connected support set containing BOTH unique source mark labels and exactly n distinct original interaction plaquette-factor labels. Its original integrated activity is

```
z_S(s,t)=integral_original_SU(N)^1024
            (s F)(t G) product_(p in S ordinary labels) f_p(U) dH.
```

The original source gives, **with no independence assumption about Wilson holonomies**, and using pointwise compactness:

```
|z_S(s,t)| <= |s*t| lambda(beta)^n,
lambda(beta) = exp(beta)-1.
```

The integral of an absolute value may be larger than the absolute integrated activity, and this is an upper bound rather than a sign/representation assertion. It preserves the native source marks and original Haar; even though some such activities vanish by extra source Haar leaves, we do not use cancellation in an ABSOLUTE activity budget.

For a graph of max degree Delta, a canonical rooted ordered depth-first spanning tree gives at most `Catalan(k-1)*Delta^(k-1) <= (4Delta)^(k-1)` connected vertex sets of cardinality k containing one fixed root. Since both globally marked labels must occur, k=n+2 and n>=d-1=2. Hence the entire connected marked *single-factor* family has the rigorous absolute inequality, uniformly in original finite lattice size whenever the same Delta/d facts hold,

```
sum_{S connected, contains both marks} |[s*t]z_S(s,t)|
   <= sum_(n>=2) (4Delta)^(n+1) lambda(beta)^n
   = 4Delta * q(beta)^2/(1-q(beta)),
q(beta) = 4Delta*(exp(beta)-1)=84*(exp(beta)-1), if q<1.
```

The original L4 graph supplied Delta=21, d=3; this statement makes no claim that graph distance d=3 is a physical time distance d=2. The sum is over *one connected activity per labelled factor set* and is independent of volume because the root is fixed and the tree-count upper bound is uniform. For a general larger original periodic lattice, the same finite neighbour structure and fixed-size original Wilson plaquette marks give the analogous graph-degree bound; only the original mark-support graph distance must be recomputed.

**Exact high-temperature threshold:** beta < log(1+1/84). For beta<=1/m, m>85, the elementary rational inequality `exp(beta)-1 <= beta/(1-beta)` gives `q<=84/(m-1)` and the exact rational estimates:

| beta upper bound | q upper bound | connected marked factor sum |
| --- | --- | --- |
| 1/100 | 28/33 | 21952/55 (~399.13) |
| 1/200 | 84/199 | 592704/22885 (~25.90) |
| 1/2000 | 84/1999 | 592704/3828085 (~0.1548) |

The bound need not be <1 merely because it converges; the explicit n/d counting gives a decay *with increasing graph distance* in larger original physical source carriers, but no continuum fixed-physical-distance guarantee is asserted.

## Source-specific no-promotion: what this estimate does NOT prove

1. **NOT the W3 log/cumulant sum:** the original finite labelled Mayer partition is a compatible-polymer gas. Its log has Ursell connected collections of mutually incompatible polymers. A log-connected collection can join the two mark supports without containing BOTH original mark labels in ONE factor-connected S, so the sum bounded above is **not the full normalized mixed log derivative**, not the required literal CMP116 absolute mixed cluster charge and not the Agda `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell`. A separate physical KP/Ursell tree-graph bound, maintaining both unique source marks and original supports and activities, is required.
2. **NOT compatible with asymptotically free weak coupling by itself:** as beta(a)->infinity, lambda(beta)=exp(beta)-1 and q grow instead of contracting. The already-existing true continuous SU2 Haar singleton lower bound `z_p(beta)>=c exp(beta/2)-1`, `c>1/6`, independently proves that simply identifying this unrenormalized microscopic gas with FP.rhoBase=1/16 is invalid at large beta. There is no contradiction with a *different correctly renormalized* CMP119/122 small/large-field activity.
3. **No fictitious monomial surface shortcut:** the previous exact five-exterior square-free parity minimum and 24 positive 12-fold source coefficients remain actual source facts but do not make the high-temperature Mayer absolute factor sum equivalent to the all-channel homogeneous beta Taylor or physical RG shell.
4. **No spatial mass-gap result:** original running beta(a), actual CMP119 E/R/B/V and ghost/FP/Jacobian/T ordering, block-event/frustrated-tail domination, physical support injection into P06/R429, volume/cutoff-uniform physical prefactor and rate, interacting continuum E1/OS same-H D2/N1/G1 all remain OPEN.

## Local execution, reproducibility and attribution

The exact native graph/graph-degree/mark-distance/rational inequalities were run locally in Python/SymPy and passed, on the original full L4 support: 256 / 1024 / 1536, 6 plaquette incidences per link, degree-20 unmarked graph, **1494 degree-20 + 44 degree-21 augmented mark labels**, d(Fmark,Gmark)=3, integer rooted-tree envelope and rational q values. [Committed checker](../../scripts/check_ym_w3_original_mayer_entropy_20261123.py) contains a source-equivalent executable. GitHub readback confirms committed content; we do not claim byte-identical checkout replay, 1024-fold continuous Haar quadrature, Agda/Lean kernel or GitHub CI. The mathematical Haar integration inequality is exact directly from normalized positivity and |t|<=1; the combinatorial rooted spanning-tree bound is an imported standard classical enumeration.

**Physical next maximum cut:** source identify a genuinely renormalized CMP119/122 E/R/B/V marked cluster family and prove its absolute physical `shellCharge` including bad sparse clusters and source scores, with an entropy margin at the physical RG scale. Feed that actual per-cluster bound and original P06 traced support to the existing CMP116 charge sum. Do not duplicate an animal counter or replace global marks with per-polymer independent multipliers.

Attribution: original Wilson SU(N) product Haar, classical Mayer/KP/Fernandez–Procacci tree-graph/animal counting, published Bałaban CMP116/119/122, original DASHI finite labelled marked Mayer, original P06/R429, and source-first W3 compiler.
