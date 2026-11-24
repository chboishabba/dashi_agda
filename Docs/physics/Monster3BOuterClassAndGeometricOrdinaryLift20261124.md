# Monster 3B P5 — outer class and geometric ordinary lift (24 November 2026)

## Source-specific outer C class

The outer standard ATLAS c projects to Suz:2 class 2C, not the inner rotation's Suz class 2B. Direct indexing of the published GAP Character Table Library 1.3.11 data (without running GAP) gives this unique source row:
Suz:2 38 (2C) <- 2.Suz.2 62 (square class 2, the central involution) <- 6.Suz.2 129 -> main 3^(1+12):6.Suz.2 52 -> MN3B 31 -> M 10 (4D).
The MN3B-to-2.Suz.2 map sends 31 back to 62. The previously paid inner rotation path is main 54 -> MN3B 33 -> M 10; these are distinct source classes, with the same Monster fusion. The source scan is the one in scripts/monster3b_atlas_outer_C_class_source_fusion.g. The stored map entries were independently indexed locally; this is not a GAP execution receipt or a hash-pinned import of the full table bytes.

Sources:
- ATLAS Suzuki standard generators: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
- CTblLib 1.3.11 sporadic tables (fusion and power maps): https://sources.debian.org/src/gap-ctbllib/1.3.11-1/data/ctospora.tbl/
- CTblLib 1.3.11 Monster maximal tables: https://sources.debian.org/src/gap-ctbllib/1.3.11-1/data/ctomax18.tbl/

In the preimage of a fixed order-four quotient cyclic subgroup, E is a normal Hall subgroup. Schur–Zassenhaus conjugacy of complements, together with the fixed image of the generator, makes all order-four lifts of that element E-conjugate. Consequently the corrected actual MM C is 4D conditional on the reported authentic quotient chart and order-four relation. Direct literal MM character evaluation remains an independent test; no new MM execution is claimed.

## Structural word correspondence

Assuming the source-cover identification and quotient chart previously established conditionally, both inner covers are the universal central extension 6.Suz of Suz. The quotient isomorphism lifts uniquely to the universal extensions and commutes with their maps to 2.Suz (the universal extension is perfect, so differences of lifts into a central C3 vanish). In particular there is no independent inner generator rephasing freedom once the quotient isomorphism is fixed. For an outer source lift C' with the corresponding quotient image, its fourth power is central and fixed under conjugation by C', which inverts that centre; hence its fourth power is 1. Its square is the unique order-two lift of the quotient central involution. The inner-cover isomorphism intertwines conjugation by the two outer generators, by uniqueness of lifts of the same automorphism. Matching squares then extends it to the outer covers. Choices C', zC', z^2 C' are central-conjugate, not literally equal. This closes structural existence/uniqueness under the source hypotheses, not the explicit source-word evaluation or central phase of the selected D.

## Characteristic-zero geometric reverse lift

Wilson's original odd-local Monster construction identifies E/Z with the complex Leech lattice reduced modulo the ramified Eisenstein prime theta=sqrt(-3). Use the original lattice and its unitary/antiunitary automorphisms, not a fabricated char-zero lift of a mod-31 matrix. The complex Leech lattice has real minimum squared norm m=4. Distinct minimal vectors in the same theta residue differ by theta*u, so their squared distance is at least 3m and at most 4m. Since Leech norms are even, the only possible distance is 12. Thus each pair has real inner product -2. For n distinct vectors in a residue the squared norm of their sum is mn(3-n)/2, hence n<=3. The three vectors v,zeta*v,zeta^2*v belong to the same residue, are distinct and exhaust it. No minimal vector reduces to zero. The 196560 minima therefore occupy exactly 65520 nonzero residues.

For a source quotient generator g, choose 12 independent minimal vectors x_i over Q(zeta), and representatives y_i of the target residues in the source lattice chart. With Hermitian form conjugate-linear in the first variable and outer parity epsilon, seek a_i in F3 such that zeta^(a_j-a_i) h(y_i,y_j)=sigma^epsilon(h(x_i,x_j)). All nonzero Gram edges fix relative phases uniquely if consistent; zero edges must match. If the chosen Gram graph is disconnected, retain component phases, impose extra minimum-vector constraints or enumerate the at most 3^11 relative phase assignments, and check lattice preservation and exact source reduction. The candidate semilinear map is A=Y diag(zeta^a_i) sigma^epsilon(X)^(-1), acting by A sigma^epsilon. Preserve the original Hermitian form, lattice, quotient chart and central phase. This is an alternative exact characteristic-zero construction independent of Steel/Magma, conditional on original lattice coordinates and chart; explicit source matrices were not recovered here. The existing ordinary faithful character selection is not replaced.

## Same-object Hom and zero vacuum

In the source-compatible tensor factorization rho(g)=K_g tensor L_g, select any nonzero coefficient K_g[y,0] in the vacuum column. For the fixed source/target vacuum inclusions and projections, transport the target y component back by T_y^-1. On the actual vacuum multiplicity space this gives P_0 T_y^-1 rho(g) restricted to S_s = K_g[y,0] L_g, with target phase understood. Dividing by this nonzero coefficient recovers L_g exactly. For y=0 this is the existing vacuum sandwich. If K_g[0,0]=0, do not discard the generator or invert zero: choose a supported y from the already compiled Weil column. This proves a constructive ordinary Hom operator formula conditional on actual characteristic-zero W and matching chart, not a numerical matrix extraction. The same algebra works in a good finite characteristic with valid source basis and nonzero coefficient.

## Single-phase signed intertwiner

In the ordinary canonical normalization let A_s and H_s be outer 12/78 transport, with A_- A_+=-I, H_- H_+=I. Let Q_s=Sym^2(A_s^-T). Given one inner intertwiner F_+, define F_-=Q_+ F_+ H_+^-1. Outer covariance transports the full inner intertwining equations; the reverse outer square follows from Q_- Q_+=I and H_- H_+=I. Hence a second independent eigenspace/intertwiner search is not a mathematical obligation. For raw projective packets retain the existing beta^3 residual and normalize before asserting both unit squares. No genuine numerical modular or ordinary F_+ was executed in this turn.

## Endpoint status

L10A: abstract characteristic-zero construction and finite relative phase problem supplied; actual original lattice/Steel coordinates, exact source matrices and literal central phases remain missing.
L10B: global model cochain already paid; nonzero-support alternative removes the zero-vacuum obstruction algebraically; actual source-compatible numerical Hom extraction remains unpaid.
L10C: one-phase signed extension theorem supplied; genuine F_+ on actual source packets remains unexecuted.
L12R: outer 4D fusion source row determined; literal C identification follows under prior authenticated source hypotheses. Structural cover isomorphism unique up to the stated central conjugacy; explicit standard-word/phase evaluation remains.
No characteristic-zero completion, source packet execution, or P6 closure is claimed. Prior ATLAS, Barraclough–Wilson/CTblLib, Wilson lattice, Steel, Nebe, Ibrahim, mmgroup and TOE attribution retained.
