# 27 October 2026 — MIXED8 linear-equivalence max-cut, provenance and remaining original question

## Source owners and evidence boundary

**Original mathematical theory:** orbit–stabilizer, finite group actions,
representation centralizers and Burnside's lemma (classical).
**Published Monster sources:** R. W. Barraclough and R. A. Wilson (2007),
*The Character Table of a Maximal Subgroup of the Monster*,
DOI 10.1112/S1461157000001352; T. Breuer, K. Magaard and R. A. Wilson,
*Verification of the conjugacy classes and ordinary character table of the
Monster*, *Journal of Algebra* 703 (2026), 452–463,
DOI 10.1016/j.jalgebra.2025.09.034; and the same authors' source-reproducible
12 December 2024 [GAP protocol](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm).
These are related research lineage/protocol/publication, not three independent
discoveries. ATLAS and CTblLib own the original group, character and fusion
data. Do not attribute the finite chart construction or its 218496 count to
those authors.

**Repository source owners:** PR #1098 owns original SHA256-pinned AtlasRep
2.Suz:2 source-word D4, GF3 12-space, stable Lagrangian, E+E quotient80 and
original Heisenberg/normalizer bridge; PR #1250 owns the prior balanced
20,971,520 MIXED8 equivariant-map count and 6.Suz source selection. Original
Ibrahim formal modules on the diagonal kernel/class20 and the 729=720+9
carrier, together with #1148's separately typed JFine/IIT geometry, stay
original owners. The newly calculated quotient count below is a
DASHI-derived finite-model consumer, not a Monster group proof.

## New finite theorem

Let E be the standard absolutely irreducible 2-dimensional D4-module
over F3 with r(x,y)=(-y,x), m(x,y)=(x,-y). Work on X=(E+E) minus zero,
with orbit decomposition (8 four-orbits + 6 eight-orbits). Let
Y=A4 disjoint union D4' be the two distinct D4 four-orbits in
E minus zero (the axis and diagonal orbits), NOT natural cube corners.
Let B be all D4-equivariant X->Y maps with exactly ten source
preimages per target point, as constructed in PR #1250.

**Source-linear automorphisms:** the only 2x2 matrices commuting with both
r and m on E are F3 scalars (commuting with m kills off-diagonal entries;
commuting with r equates the two diagonal entries). Consequently
End_D4(E+E)=M2(F3), and Aut_D4(E+E)=GL2(F3) of order
(9-1)(9-3)=48. The full D4-set automorphism group of Y is C2 x C2
of order four: the two inequivalent reflection-stabilizer orbit types
cannot interchange, and each can be independently antipode-flipped.
The group G=GL2(F3) x (C2 x C2) acts on B by source precomposition and
target postcomposition.

**Burnside result:**
- Original finite count: |B|=binom(6,3) 2^8 4^6=20,971,520.
- Among 192 G elements, two fix every member of B. The second is the
  diagonal (-I_source,-I_target), corresponding to central r^2.
- Sixteen G elements fix exactly 512 balanced maps each.
- The remaining 174 elements fix zero balanced maps.
- Therefore
  |B/G|=(2*20,971,520+16*512)/192
        =41,951,232/192
        =**218,496**.

The source code uses **all 80 actual finite X-vectors** and target eight
vectors, enumerates the 48 source-linear and four target symmetries, forms
all D4 orbit-local equivariant maps, transports local map choices around
source-automorphism orbit cycles, and counts balanced fixed maps by an exact
integer generating-polynomial recurrence of degree three. It does not
enumerate all 20,971,520 global maps. The identity count is independently
predicted by PR #1250's closed product formula. The focused regression
checks D4 relations, orbit census, local map options, 48 automorphisms,
192-element fixed census and nonpromotion flags.

**Observed in this session:** an equivalent independently written
standard-library Python reference computed 218,496 with histogram
{0:174, 512:16, 20971520:2}, plus the original 20,971,520 count.
The repository source consumer and focused test are SOURCE-WRITTEN;
exact checked GitHub bytes, GAP/CTblLib, Agda and full Monster actions
were not executed in this session.

**Interpretation:** even granting every linear D4-automorphism of the
source 4D quotient, there remain 218,496 balanced map classes after
target-equivariant relabelling. This proves serious residual ambiguity
*under precisely that equivalence group*, NOT under all nonlinear
D4-set source automorphisms and NOT under a full Monster/Heisenberg action.
In particular it neither repairs the natural geometric cube-corner no-go
nor makes a ten-sheet quotient canonically Monster/IIT physical.

## Pareto / snowball / Ibrahim acceptance and handoff

P0. **Authentic 6.Suz 78 family / class fusion:** execute the *existing*
#1250 CTblLib all-conductor, source Irr-row matched and main->MN3B->Monster
degree196883 character matcher and #1250's source Suz2B->Monster4 class
fusion GAP script. Preserve original H/[1,20] BMW/BW quotient and original
source table numbering. Fail closed if source word r remains among multiple
2.Suz:2 classes or Monster 4A/4C/4D branches. This new finite count cannot
select the family.

P1. **Actual source words and phase:** select r's true Monster class,
6B/6E z*r^2 branch and its compatible 6.Suz faithful/nonfaithful degree78
pair on the same original class labels. Source catalogue existence does not
authenticate a run or weld to a particular AtlasRep generator word.

P2. **Full Heisenberg action:** instantiate the existing #1098 normalizer
cocycle, the 729-dimensional Schr phase, and the selected actual
Hom_E(H_zeta,W_zeta) intertwiner; test generators, central phases,
class fusion and quotient diagonal identities on the same carrier.
The chosen rank-nine plane is NOT invariant under 720 of the 729
translations; this new GL2 symmetry calculation does not change that.

P3. **Kernel proof:** typecheck actual source-instantiated Agda/Lean
theorem assembly with bound receipts, no unsupported postulate promotion,
and preserve original proof/source owners, attribution, negative controls
and date-stamped provenance. Avoid spending Pareto effort on CI until
mathematical acceptance is met.

P4. **Original IIT/JFine inquiry:** only after P0–P3, supply an explicit
operator/observable intertwiner from the source-carried Monster action
to the specific geometric or causal IIT/JFine consumer, with selected
invariant, normalization, state/action transport, and tested countermodel.
Sharing 8,9,27,78,90,720,729, D4 or ternary indices is insufficient.
#1148 retains ownership of the original IIT/phi interpretation. Nothing
here establishes a physical, neuroscientific or consciousness claim.

**Practical deliverables from this cut:** one exact finite-model source
checker; one focused regression; this provenance/acceptance ledger.
Do not duplicate the original Monster class matcher or start a new group
formalisation. Source-written versus externally proven versus
computationally observed versus kernel-checked statuses stay distinct.

## Follow-on naturalness discriminator: full D4-set relabelling

The number 218,496 is **specific to linear source automorphisms**. A
different, larger equivalence relation has a sharply different answer.
The full D4-set automorphism group of X, ignoring the F3-linear
structure, is

    Aut_D4(X) = (C2 wr S4) x (C2 wr S4) x (D4 wr S6)

because X contains four copies each of the inequivalent axis-
and diagonal-reflection four-orbits, plus six copies of the free
eight-orbit. Each 4-orbit has internal equivariant automorphism
group N_D4(C2)/C2 = C2, and a free orbit has internal group D4.
Its order is (2^4*4!)^2*(8^6*6!) = 27,831,388,078,080.

**Exact theorem:** this full *nonlinear set* automorphism group acts
transitively on the 20,971,520 balanced equivariant maps. Proof:
permuting six free orbits moves any choice of three axis-assigned
free orbits to any other such choice; independent internal D4
automorphisms move each of their eight allowed orbit-map choices
transitively. The independent internal C2 automorphisms move the two
allowed choices of each of the eight reflection-stabilizer
four-orbits transitively. Thus any balanced map can be carried to any
other one by a source D4-set automorphism. There is **one**
equivalence class under full source-set reindexing and its stabilizer
has order 27,831,388,078,080 / 20,971,520 = 1,327,104.

This result does **not** supply a canonical map: transitive action on
choices means *every* possible choice can be renamed into every
other, not that one is distinguished. In fact no equivariant map
X->Y is fixed under every source automorphism while the target labels
are held fixed: the source-linear central map -I = r^2 acts as
x->-x; equivariance forces f(-x)=-f(x), and every y in Y is nonzero
so -f(x) != f(x). A *paired* source/target antipode instead fixes
every equivariant map. The correct distinction is **uniqueness
up to an allowed equivalence** versus **canonical natural
selection**; neither implies the Monster/IIT same-object join.

This is an exact group-set argument using classical wreath-product
automorphism theory and the original source-chart orbit census.
It is not a novel Monster conjugacy-class computation and does not
identify the correct Heisenberg/Monster-equivariant coordinate map.
