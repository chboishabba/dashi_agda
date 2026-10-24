# C3-supported Alexander wild ball: geometric same-object existence proof and computational boundary

Date: 2026-10-25. Original sources: J. W. Alexander (1924);
Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed pp171–172,
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf;
Franca Lippert, *The Alexander Horned Sphere and Bing's Hooked Rug*,
§§2.1–2.3, https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf.
The underlying wild sphere, punctured-torus van Kampen, and supported
homeomorphisms are THEIR original mathematics, not DASHI discoveries.

## Theorem (paper-level existence by boundary connected sum)

There exists a compact R-invariant wild embedded B ⊂ R3,
homeomorphic to D3, with R(x,y,z)=(z,x,y), such that
  pi1(S3\B) = G_A * G_A * G_A,
where G_A is Hatcher's one-sector horned-exterior group.
The induced rotation has exact order three in Out(pi1(S3\B)).

Proof relies on the cited classical supported horn construction
and standard tame collar/boundary connected sum/van Kampen theorems.
It is NOT an Agda-kernel derivation nor a fully encoded infinite
Euclidean embedding.

### 1. Choose a supported Hatcher satellite

By Lippert §2.2, the successive homeomorphisms B_(n-1)->B_n
are identity away from shrinking horn-attachment neighbourhoods.
Choose the bases in a small outward patch of a round B0 of
radius 3/4, and preserve an inward round cap, while fitting all
linked tori into a containing unit reference ball. The resulting
wild B_A is homeomorphic to D3 and agrees with B0 on that cap.
In local axial/transverse coordinates, its tame bicollar is
  Phi(u,v,s)=(-sqrt(9/16-u²-v²)+s,u,v),
  u²+v²≤1/16, |s|≤1/8.
The inverse is (x,u,v)->(u,v,x+sqrt(9/16-u²-v²)).
Here s>0 is interior and s<0 exterior.

### 2. Place three copies and attach by an honest tame star

Take a round central unit B_c, centres C_i=9e_i,
B_i = C_i+R^i(B_A), and straight radius-1/4 tubes
  T_i={t e_i+v: t∈[1/2,17/2],
                      v⊥e_i, |v|≤1/4}.
The full endpoint disks lie INSIDE the original radius-3/4
ball: 1/4+1/16=5/16<9/16. Thus the satellite attachment
is to the PRESERVED wild-ball cap, not merely its enclosing
reference unit ball. Exposed tubes are disjoint and do not
meet off-axis satellites; all attachment disks have bicollars.

The connected sum graph is a TREE with central and three
satellite vertices. Gluing a 3-ball to a 3-ball along a
collared 1-handle yields another topological 3-ball; iterate
over three edges and round the finitely many tame corners.
Thus B=B_c∪(∪B_i)∪(∪T_i) is topological D3.
It is exactly R-invariant by construction and remains wild
inside each satellite's untouched wild region.

### 3. Explicit separating sphere and strong contraction

For each i take S_i={|x-C_i|=4}. The three S_i are disjoint,
miss all nonincident tubes and balls, and each meets only T_i
in one closed disk. On S_i (local (t,u,v) axes) the disk is
   t=9-sqrt(16-u²-v²),  u²+v²≤1/16.
The second sphere branch has t>9 and cannot lie in the tube.
The exterior overlap S_i∩(S3\B) is sphere minus that CLOSED
disk, not a plane minus a disk.

The explicit stereographic homeomorphism is
   sigma(t,u,v)=(u/(t-5),v/(t-5)).
It maps precisely onto the OPEN disk
   |y|<16+sqrt(255).
The inverse is
   t=(13+5|y|²)/(1+|y|²),
   u=8y1/(1+|y|²), v=8y2/(1+|y|²).
The linear radial homotopy H_s(y)=(1-s)y contracts the
overlap. A small sphere bicollar is product with an
interval, so the corresponding van Kampen cover overlap
is simply connected. These formulas are now **executable
and finite-audited** in
scripts/alexander_horned_C3_same_object_separator_atlas.py.

### 4. The actual outer and satellite pieces

Cut the exterior along the three S_i. The central piece
depends only on the standard central ball plus radial
tube portions outside S_i, NOT on the wild regions wholly
inside each S_i. Replace the satellites within S_i by
round balls sharing the same tame inward cap. The full
all-round union is a regular neighbourhood of an unknotted
straight star (therefore a tame D3 with simply connected
exterior). Since its cover has contractible overlaps and
each round satellite piece has simply connected exterior,
van Kampen implies the identical central piece has
trivial pi1.

In each wild satellite piece, the attached radial tube
can be slid along its source-specified tame cap bicollar.
This standard **relative collar equivalence** leaves the
wild region untouched and identifies the piece's pi1
with the original Hatcher exterior G_A. Restoring the
ordinary outer region beyond S_i adds a simply connected
ball attached along S², so it does not change pi1.
No arbitrary new source-side quotient is introduced.

The cover nerve is a tree (one central piece and three
satellites); all attaching overlaps are simply connected.
Repeated van Kampen gives
 pi1(S3\B) ≅ 1*G_A*G_A*G_A ≅ G_A*G_A*G_A.
At finite Hatcher handlebody stages, the identical fixed
separator supports stagewise F_(3·2^n) and the original
Hatcher commutator transitions; the infinite group is
their colimit by compactness.

### 5. Genuine outer-C3 action

The fixed basepoint x0=(20,20,20) lies in the exterior
and on R's fixed axis. Choose connecting paths by
cyclic transport; rotation permutes the three satellite
group factors, modulo inner choice of paths.

Retraction onto factor zero sends R(m_0) and R²(m_0)
to 1 for any nontrivial factor-zero meridian m_0, whereas
it sends an inner conjugate of m_0 to a NONTRIVIAL
conjugate. Hence neither R nor R² acts inner; the class
of R has exact order three in Out(pi1).
This is NOT a nonsplit C2 central extension of C3.

### 6. Verification and limitations

**Classical source-backed theorem inputs:** Hatcher's
actual supported horn/linked-torus construction and
stage pi1; Lippert's stable cap and B≅D3; tame boundary
connected sum and relative collar slide; van Kampen.
**New direct calculations:** actual C3 satellite/tube
coordinates; endpoint overlaps; exact open-disk atlas
and homotopy; finite-stage abstract commutator labels.
**Unpaid machine-level gates:** an indexed infinite
coordinate map for every Hatcher pillbox, explicit
ambient isotopy code for wild satellite-side pieces,
Agda topology kernel. These are not needed to present a
paper-level existence proof based on standard theorems,
but remain open for an entirely internally certified
DASHI formal proof.

Do not confuse a finite smooth ball B_n (trivial
exterior pi1) with a Hatcher stage handlebody X_n
(exterior free group) or the limiting wild ball B
(perfect nontrivial exterior). Nor does the geometry
alone produce nontrivial spin connection holonomy:
the ambient Euclidean spin structure is unique; any
nonabelian SU2 monodromy is an additional specified
flat connection, not a free result of wildness.
