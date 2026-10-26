# 27 October 2026 — exact MIXED8 linear-flag / pointed729 / Weyl max-cut

## Source provenance and ownership (do not erase)

* **Original finite mathematics:** Maschke's theorem (char 3 does not divide
  |D4|=8), Schur's lemma, finite D4 representations, orbit-stabilizer,
  quaternion commutators and finite Heisenberg/Weyl representation theory.
  These are classical theorems; their existence is not new DASHI authorship.
* **Original Monster scholarship:** Barraclough–Wilson (2007), *The Character
  Table of a Maximal Subgroup of the Monster*,
  DOI 10.1112/S1461157000001352, including 3^(1+12):6.Suz.2 main
  and 3^(1+12).2.Suz.2 diagonal-quotient tables; their
  [original supplementary author page](https://www.rwb.me.uk/table/index.html)
  explicitly distinguishes subgroup fusions from quotient maps.
  Breuer–Magaard–Wilson's [12 Dec 2024 reproducibility protocol](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm),
  subsequently published *Journal of Algebra* **703** (2026) 452–463,
  DOI 10.1016/j.jalgebra.2025.09.034, is related source lineage,
  not an independent original discovery.
* **Original repository owners:** #1098 the SHA-pinned original ATLAS
  2.Suz:2 D4 words, source invariant form, source 6D stable Lagrangian,
  stable rank2 plane, quotient E+E, centre-inverting normalizer/Hom
  proof interfaces; #1250 the original noncanonical MIXED8
  20,971,520 map count, full Suzuki 78 family/class-matched source join;
  #1148 original IIT/phi causal geometry and H4 phase bridges;
  preexisting Ibrahim diagonal class-20 and 729=720+9 carriers.
  The present new scripts are consumers of these original producers,
  not alternative owners of the Monster class or IIT interpretation.

**Observed execution:** independent local Python model check(s) executed
for the 48-by-4 Burnside census, source-linear commutator, 729
bidirectional codec, 16-map family and finite Weyl model. The new
GitHub commit objects exist, but the *exact committed script bytes*
and focused tests have **not** been locally byte-replayed. No genuine
GAP/CTblLib selected 6.Suz78, mmgroup Monster generator, Agda kernel or
full Monster Hom run is claimed.

## 1. New no-go: full linear-source naturality is impossible

Let E=F3^2 carry r(x,y)=(-y,x), m(x,y)=(x,-y).
Source V=E+E; target Y=E\{0}=A4 disjoint union D4', the
mixed-eight D4-set. The source-linear centralizer is GL2(F3)
on the multiplicity index; target Aut_D4(Y)=C2 x C2 (two independent
orbit antipodes), abelian.

Inside GL2(F3), the exact matrices

    A=((0,2),(1,0)),  B=((1,1),(1,2))

satisfy A²=B²=-I and [A,B]=-I. Every group homomorphism
rho:GL2(F3)->Aut_D4(Y) sends -I to identity. But
D4's half-turn r² acts as -I on both V and Y. Any D4-map f would
require f(-v)=-f(v), while simultaneous rho-equivariance requires
f(-v)=f(v). Y has no antipode-fixed point. CONTRADICTION.

**Scope:** no simultaneous *full* source-linear centralizer
equivariance through an abelian target D4-automorphism group.
It does not prohibit a quotient after an ordered splitting is selected,
nor rule out a smaller actual Monster-selected symmetry or a
different centre-inverting two-phase operator model.

## 2. Exact positive, choice-dependent bidirectional isomorphism

Let 0=(0,0) in E, E*=E\{0}, star a distinguished singleton
with trivial D4 action, S=E disjoint union {star} (|S|=10).
Choose an ORDERED D4-isotypic source splitting E+E.

    (a,b) with a!=0:  encode = (a,b)   in E* x S
    (0,b) with b!=0:  encode = (b,star)

    inverse(y,s in E) = (y,s)
    inverse(y,star)   = (0,y)

Thus (E+E)\{0} ≅ E* x S as **D4-SETS**, not just
cardinalities. With chosen inner 9-point E,

    E^3 ≅ E  disjoint union  (E* x S x E)
    729 =   9 + (8 x 10 x 9).

The total D4 action applies diagonally to all E coordinates,
and fixes star. This is a completely explicit invertible chart,
unlike selecting arbitrary orbit maps.

Exactly checked on equivalent local reference: 80 source pairs and 729
triples, all inverses and both D4-generator actions (1,618
incidences). Original #1250 source model orbit census reproduced:
80=8x4+6x8; outer720=24x4+78x8. Ten sheets are
**nine E points plus star**, with nontrivial sheet action:
this is a D4-set *product* Y x S, not a trivially acted Fin10
product (already refuted in #1250).

**Source bridge:** If the #1098 actual 6D D4-stable Lagrangian has
a 2D stable E submodule and 4D quotient E+E *as reported*, then
Maschke splitting over F3 gives a noncanonical D4-linear
identification with E^3. This is a classical conditional module
argument; it is not an executed original AtlasRep matrix
identification of particular coordinates.

## 3. Quantified constrained choices: precisely 16 linear-flag charts

There are 8 nonzero D4-linear surjections q:E+E->E, one per nonzero
row (a,b) in F3^2. Each ker(q) is another E, with two
D4-linear isomorphisms psi:ker(q)->E (scalar ±1).
Define f(v)=q(v) off ker(q); f(v)=psi(v) on ker(q)\{0}.
Every y in E* has 9 preimages off kernel plus 1 nonzero kernel
preimage: exactly ten. These **16 functions are distinct**.
They form **one GL2(F3) source-linear orbit**, with stabilizer
of order 48/16=3. Computed by exact enumeration and verified
D4 equivariance and uniform fibres. This is a selected
structured subfamily of #1250's 20,971,520 balanced maps;
selection of a particular q and psi still requires source structure.

Previous exact full Burnside result is preserved separately:
218,496 maps modulo GL2(source) times C2²(target), while
all 20,971,520 are equivalent under the much larger full
nonlinear D4-set source automorphism group. These three numbers
answer DIFFERENT equivalence questions.

## 4. Finite transported Weyl action — positive with crucial source caveat

Conjugate the finite Schr basis labels x in E^3 by the explicit
pointed729 codec. Let T_v|x>=|x+v>, M_w|x>=zeta^(w.x)|x>.
The exact Weyl relation is

    M_w T_v = zeta^(w.v) T_v M_w.

Exact equivalent local Python: 26,244 generator-pair checks and
8,748 D4 covariance checks, plus T_i^3=1. Translating the
chosen central projector (a,b)=0 leaves it invariant for
exactly 9 translation vectors v with v_a=v_b=0, and moves it
for the remaining 720. This reproduces #1250's original 9/720
Heisenberg **chosen-plane NONinvariance** and gives explicit
cross-block transitions. A transported *operator action* can exist
without preserving the outer/central *partition*.

**Critical negative control:** the simple model D4 permutation
lift is phase preserving (it induces a symplectic cotangent lift).
The actual #1098 ATLAS normalizer D4 mirror has symplectic
multiplier -1 and swaps zeta with zeta². Therefore the finite
chosen D4/Weyl operator representation is NOT the actual
Monster-normalizer mirror, and no scalar-centre selected
single-phase Monster Hom is claimed.

## 5. Pareto/snowball/Ibrahim handoff — original question retained

P0. **Authentic source class/character JOIN**: run ORIGINAL #1250
GAP/CTblLib all-conductor 6.Suz source export, exact source Irr
position/full class signature, main->MN3B class20 (not class19)
quotient and restricted Monster-196883 selector. Run original
Suz2B-to-Monster4 fusion script; fail closed on ambiguous r.
The published BMW24 class20 proof establishes external
source authority, NOT a runtime receipt. Do not recreate
existing table/character machinery or guess 4A/C/D vs 6B/E.

P1. **Actual equivariant source-word lift**: select original
12D AtlasRep source matrices and D4-Lagrangian basis; compile
the E^3 choice as an explicit source D4 basis/dual basis.
Require equality of source generators, correct central
multiplier and conductor phases on H_zeta and H_zeta².
Use #1098 for normalizer cocycle and source 729x90 Hom.
An abstract finite permutation Weyl consumer is insufficient.

P2. **Kernel acceptance**: typecheck the source-instance Agda/Lean
theorem package, not the abstract helper alone; retain typed
negative-control/provenance and original sources.

P3. **Original IIT/JFine inquiry**: only after P0–P2 can #1148
attempt explicit state/action/observable intertwiner and a
testable causal or phi consumer; shared 8/9/10/27/90/729/D4
indexing is no physical or neuroscientific identification.

**Deliverables of this cut:**
- scripts/monster3b_mixed8_full_linear_naturality_nogo.py (+ focused tests)
- scripts/monster3b_mixed8_ordered_E3_pointed729_bidi.py (+ focused tests)
- scripts/monster3b_mixed8_linear_flag_family.py (+ focused tests)
- scripts/monster3b_mixed8_pointed729_weyl_transport.py (+ focused tests)
- this dated original-source, proof-status and roadmap ledger.

Nothing here is a newly proved Monster group class-fusion theorem,
a completed genuine 6.Suz78 source run, Agda kernel-verified result,
or an IIT/physical identification.
