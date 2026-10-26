# Horn Hatcher meridian: coherent basing, inverse orientation and Wilson fringe discriminator
Date: 2026-10-26 (Australia/Brisbane)
Owners: Agda hyperfabric #1249, Lean conditional mirror #84; DO NOT mutate
the original horned geometry owner #1244 or neutrino selected-W owner #1247.

## Precisely attributed original and repo roots

* **Allen Hatcher**, Algebraic Topology, Example 2B.2, printed
  pp171–172 (original PDF https://pi.math.cornell.edu/~hatcher/AT/AT.pdf,
  visually checked in this cut): in a REAL linked punctured-torus
  complement, the annulus generator maps to the commutator of the TWO
  newly linked meridian/longitude child generators; finite stages
  inject. No Euclidean length or named actual source C3 satellite
  homotopy equivalence follows from that group proof alone.
* **J. W. Alexander (1924)** owns original wild sphere,
  DOI 10.1073/pnas.10.1.8. **Morikuni Gotô (1949)** owns compact
  semisimple commutator surjectivity, DOI
  10.2969/jmsj/00130270. Neither authored the following
  finite combinatorial/glue adaptation.
* Original **Agda horn PR #1244** owns the 3-satellite C3 geometry,
  finite punctured-shell collar and recent exact global-to-shell
  C3-equivariant basing paths gamma_i from (20,20,20) to 13e_i.
  These are valid within the central region, but DO NOT supply a
  relative satellite-side pi1 equivalence or chosen Hatcher generator.
* **Agda neutrino PR #1247** owns the SAME chosen W, original exact
  cyclotomic trace, its selected unpolarized synthetic two-arm
  Wilson interferometer P(phi), and the independent C3-conjugation
  trace no-go. We do NOT relabel its chosen PMNS/CP entries as predictions.
* **Agda #1249 / Lean #84** own the earlier spectral cubic
  ||W-I||op²>517/250 and flat marked-child gap >781/1000, plus
  the conditional curved eta<=23/500 rejection. The new bridge
  changes only the allowed coherent orientation/basing convention.
* **Exotic topology Agda #1254 / Lean #86** found the
  append-chronological versus prepend-newest-first hazard.
  The original source already contains
  AlexanderHornedBinaryPadicCylinderExact.chronological and the
  leftChildAddsHighOrderDigit/rightChildAddsHighOrderDigit lemmas.
  REUSE those rather than inventing a fresh binary codec.
* **Classical differential geometry:** flat holonomy is a
  representation of based pi1, and changing the basepoint path
  conjugates; reversing a loop inverts. General nonflat Wilson
  transport does not respect homotopy equality without a BASED
  curvature-area defect. This distinction remains a hard gate.

## Exact source-group basing and orientation normalisation

For [a,b]=aba^-1 b^-1, the free-group identities are

    [b,a]=[a,b]^-1
    [gag^-1, gbg^-1]=g[a,b]g^-1
    [a^-1,b^-1]=(ab)^-1[a,b](ab).

The second identity requires ONE coherent group element g
conjugating BOTH child words. If only one child acquires an
independent whisker h, there is NO generic identity
[ha h^-1,b]=h[a,b]h^-1. Source group marking must not be
silently transported with mismatched basepoint-path conventions.

For a unitary representation rho (flat source), define
d(U)=||U-I||op. The exact classical invariances are

    d(gUg^-1)=d(U),      d(U^-1)=d(U).

Thus for any SOURCE-PROVED parent root relation

    rho(m_root)
      = rho(g) (rho([m_L,m_R]))^epsilon rho(g)^-1,
      epsilon in {+1,-1},

the operator-norm *scalar obstruction* and previous
selected-W flat child bound >781/1000 are invariant
under these coherent choices. Hatcher's source **pi1**
marking still has to be supplied for the actual satellite:
neither word algebra nor a source annotation constructs it.

This is a practical relaxation of the acceptance INTERFACE:
for the flat bound, it is enough to provide the correctly
free-homotopic/unbased commutator class (whole-loop conjugacy)
up to inversion, not an exact common global word spelling.
For the CURVED bound the actual eta for the chosen based
loops and homotopy is still required.

## Exact original W trace: norm-even but calibrated fringe-odd

Original neutrino #1247 fixed

    T=tr(W)=(176093404722400-19836986431118*zeta3)
              /181846007130841,
    zeta3=-1/2+i sqrt(3)/2.

Write A=176093404722400/D, B=19836986431118/D>0.
Then Re(T)=A+B/2 and Im(T)=-B sqrt(3)/2.

Original SOURCE-CHOSEN unpolarized two-arm port formula:

    P_W(phi)=1/2+Re(e^(i phi)T)/6.

Loop inversion gives tr(W^-1)=conj(T) and

    P_{W^-1}(phi)=P_W(-phi).

Conjugation by a basing transporter or C3 actor DOES NOT
change the trace and leaves the ENTIRE P(phi) fixed.
The orientation-zero phase signal likewise does not change:

    P_W(0)=P_{W^-1}(0)
           =434928608401/648677790003.

But the ODD-IN-PHASE component changes sign. With a fixed
externally calibrated orientation/phase convention:

    D_W = P_W(pi/2)-P_W(-pi/2)
        = -Im(T)/3 = B sqrt(3)/6 >0,
    D_(W^-1) = -D_W,
    D_W² = B²/12
          = 98376507667089911639682481
            /99203910928289627462680101843.

This is an EXACT algebraic model contrast (~0.03149063),
NOT a measured optical/interferometer signal. A simultaneous
swap of interferometer arms or reversal of control-phase
conventions can reverse the measured sign, so independent
calibration is mandatory before source-orientation inference.

Moreover for unitary W,

    (W^-1-I)^*(W^-1-I)
      = 2I-W^-1-W
      = (W-I)^*(W-I),

literally the SAME Hermitian X operator, so even the FULL
previous selected-W exact spectral cubic and child gap
bounds are orientation invariant; only the imaginary
TRACE/fringe component is orientation odd.

## Executable receipts and negative controls

New Agda #1249 scripts:
1. scripts/check_horn_marked_orientation_whisker_cut.py
   checks 27 reduced free-word triples x4 identities, all
   254 chronological binary histories of lengths 1..7,
   and an independently-whiskered child counterexample.
   Independent equivalent local source execution PASS.
2. scripts/check_horn_selected_w_fringe_orientation_cut.py
   computes original exact source probability and odd
   contrast squared in Fraction, reconstructs SAME selected
   W (original neutrino source), and checks matrix/trace
   conjugation and inversion at four phases. Independent
   equivalent local source execution PASS.
No physical detector, empirical evidence or original-source
field is asserted by these passing controls.

New Lean #84 source-written consumer:
Integration/DASHITOE/HornMarkedMeridianOrientationCut.lean:
abstract group commutator convention, conjugation/inversion
identities, source-marked COMMON whisker/orientation interface,
conditional transport of selected-W scalar child floor.
Integration/DASHITOE/HornWilsonFringeOrientationCut.lean:
exact original trace zero-phase port and orientation-odd
fringe-square rational checks. Underlying SU3 matrix/actual
source geometry are EXTERNAL and Lean/Lake kernel NOT RUN.

## Pareto/Ibrahim revised frontier: one source join

P0 source-specific SATELLITE-side group equivalence
pi1(S_i,p_i) =~ Hatcher G_A and associated meridian class.
Reuse #1244's central C3 basing paths exactly and the existing
Hatcher-at van Kampen conditional Lean carrier. Pay the
***same-object induced generator map***, allowing common
conjugation and coherent orientation inversion.

P1 actual compact local loop representative for that class,
avoiding the ENTIRE source finite stage X_n with source
Euclidean arclength. The existing nested-stage/rigid-C3
interfaces handle later-stage and sector transport. The
exact flat selected W obstruction is M L<=781/1000,
now invariant under the allowed complete marking choices.

P2 a real BASED curved parent/commutator surface and
transported curvature integral eta<=23/500 with
one source child ML<=3/4; abstract free homotopy is NOT
enough when the connection has curvature.

P3 a calibrated two-phase interferometer with actual
selected physical gauge/bundle, measured W and W^-1
paired traversals and conjugated/C3 controls; this would
separate fringe orientation from norm obstruction.
No hardware/theory of lepton masses claimed.

P4 exact-head native Lean/Agda compilation and matrix-to-Lean
analytic theorem welds. This remains separate from local
finite Python regression and original-source attribution.

**STOP RULE:** a compatible bit codec, word identity, symbolic
commutator, finite collar, C3 orbit, or quantum analogy alone
does not pay the relative source π1 map. Do not promote such
collisions into same-source horn detection or a verified physical
Wilson observable. QID/Dewey unresolved when not inspected.


## Paired curved source error invariance (additional necessary discriminator)

For unitary matrices U=Hol(parent) and V=Hol(actual based
child-commutator word), eta=||U-V||op. This is **not**
the same as the abstract group word identity when curvature is
nonzero. However simultaneous coherent transformations satisfy

    ||U^-1-V^-1||op = ||U-V||op,
    ||GUG^-1-GVG^-1||op = ||U-V||op.

The first follows by inserting unitary factors U^-1 and V^-1
around V-U. The second is unitary conjugation invariance.
Consequently a TRUE source-derived eta<=23/500 survives
changing the orientation of BOTH loops or rebasing the
ENTIRE parent-versus-word pair. It cannot survive an
uncoordinated change to one loop alone.

The original selected W same-matrix numerical test used
V=G W G^-1 with G the source-defined diagonal C3 actor.
The genuine nonzero eta=||W-V||op is exactly preserved
when both U and V invert, and when both are conjugated
by G. A deliberate one-sided rebase sends U->G W G^-1=V,
falsely producing eta'=0 while true eta>0. This is a
SEVERE negative control against promoting any mismatched
basis/whisker comparison into a zero-curvature statement.

The test was independently locally executed and PASS;
`scripts/check_horn_selected_w_fringe_orientation_cut.py`
now includes the same paired-eta controls on its GitHub
source. Lean #84 extends
`HornMarkedMeridianOrientationCut.lean` with
`pairedDefectBasingAndOrientation` and
`pairedCurvedSourceEtaCapTransport`, explicitly
conditional on the operator-norm invariance premise.
Neither the actual Hatcher curved based homotopy nor
its curvature area is supplied. Kernel verification
remains NOT RUN.


## Final concurrent source-owner update: actual specialized chronological weld

In the FINAL live PR recheck, original horn geometry owner #1244
advanced from ae805ee... to
bf77f7c6cda943610a7e6d645178ede34b569044.
It NOW owns the dedicated source-written
`DASHI/Mathematics/Topology/AlexanderHornedC3ChronologicalClopenBridgeExact.agda`,
which literally imports the old `Bin.chronological`,
`EndMass.prefixBitsToBools` and original `Cantor.Cylinder`,
and source-proves that Horn left/right *prepend* corresponds
to chronological Cantor *append*, and that C3 rotation leaves
the chronological cylinder untouched. The specific source
reversal weld is THEREFORE ALREADY OWNED by #1244,
not a novel new result of our #1249 Python 254-history audit.
The latter is only an independently executed negative-control
regression; our genuine new bridge is the GROUP-LEVEL common
whisker / whole-word orientation and the already-owned
selected-W phase-sensitive consumer consequence.

Same owner #1244 additionally committed
`scripts/alexander_horned_c3_clopen_spatial_realization.py`,
a concrete tame C3×binary Cantor subset of R3, with shrinking
disjoint balls and positive sibling gaps. Crucial negative
control: its Euclidean shrinking diameters are REAL but
the embedded set is **tame**, with NO actual Hatcher linked
handlebody group transport. It cannot inhabit the new
selected-W flat norm geometry threshold simply by having
small cylinder diameters. Do not infer a true Hatcher
short meridian from the tame control.

The remaining first-link P0 is unchanged but more precisely
situated: actual source-linked horn satellite pi1 map and
marked generator, plus a Euclidean short loop avoiding the
entire stage. #1244's literal endian/chronological bridge
and C3 spatial tame control may be REUSED but are not the
missing geometric source representation. #1254 remains
the owner of the generic chronological-event proof and
severe Cantor-versus-geometric-link discriminators.
No kernel receipt.
