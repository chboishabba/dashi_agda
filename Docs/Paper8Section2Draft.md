# 2. Three Generations from Heegner Discriminants

The matter carrier begins with the nine imaginary quadratic discriminants of
class number one:

\[
-3,\ -4,\ -7,\ -8,\ -11,\ -19,\ -43,\ -67,\ -163.
\]

For a negative fundamental discriminant \(D\), the conductor lane used by the
carrier is its absolute discriminant level

\[
N_D = |D|.
\]

The ordered carrier therefore sees the following Heegner lanes.

| carrier order | discriminant \(D\) | field | conductor \(N_D\) | sector decision |
|---:|---:|---|---:|---|
| 1 | \(-4\) | \(\mathbb{Q}(i)\) | \(4\) | quark lane I |
| 2 | \(-3\) | \(\mathbb{Q}(\sqrt{-3})\) | \(3\) | quark lane II |
| 3 | \(-7\) | \(\mathbb{Q}(\sqrt{-7})\) | \(7\) | quark lane III |
| 4 | \(-8\) | \(\mathbb{Q}(\sqrt{-2})\) | \(8\) | rejected for quark carrier: \(\gcd(8,4)=4\) |
| 5 | \(-11\) | \(\mathbb{Q}(\sqrt{-11})\) | \(11\) | later sector after quark carrier closes |
| 6 | \(-19\) | \(\mathbb{Q}(\sqrt{-19})\) | \(19\) | later sector after quark carrier closes |
| 7 | \(-43\) | \(\mathbb{Q}(\sqrt{-43})\) | \(43\) | later sector after quark carrier closes |
| 8 | \(-67\) | \(\mathbb{Q}(\sqrt{-67})\) | \(67\) | later sector after quark carrier closes |
| 9 | \(-163\) | \(\mathbb{Q}(\sqrt{-163})\) | \(163\) | later sector after quark carrier closes |

The quark carrier is assigned to the first three conductor lanes

\[
D=-4,\qquad D=-3,\qquad D=-7,
\]

with conductors

\[
N_{-4}=4,\qquad N_{-3}=3,\qquad N_{-7}=7.
\]

These conductors are pairwise coprime:

\[
\gcd(4,3)=1,\qquad \gcd(4,7)=1,\qquad \gcd(3,7)=1.
\]

Thus the three quark lanes occupy mutually non-overlapping conductor sectors.
In this paper this is the carrier criterion for a quark generation lane:
within the ordered Heegner list, a quark lane must be one of the initial
occupied conductor sectors and the selected conductors must be pairwise
coprime.

The exhaustion is an exhaustion of the assigned carrier triple, not a claim
that arithmetic produces no later coprime levels.  The triple selected by the
carrier is

\[
\{-4,-3,-7\}
\quad\longleftrightarrow\quad
\{4,3,7\}.
\]

The next Heegner lane, \(D=-8\), has conductor \(8\), and it fails the
pairwise-coprimality test with the already occupied \(D=-4\) lane because

\[
\gcd(8,4)=4.
\]

This closes the contiguous initial carrier block.  The remaining class-number
one discriminants,

\[
-11,\ -19,\ -43,\ -67,\ -163,
\]

do have prime conductors, and those conductors are individually coprime to
\(3\), \(4\), and \(7\).  They are therefore not excluded by a bare
coprimality statement.  They are excluded from the quark count by the
assignment rule: after the contiguous initial quark block \((-4,-3,-7)\) is
filled and the next ordered lane \(-8\) fails the carrier test, the carrier
moves to the lepton and beyond-Standard-Model sectors rather than promoting
later prime lanes to fourth, fifth, or higher quark generations.

The resulting finite statement is therefore

\[
\text{quark generations}
\quad\longleftrightarrow\quad
\{-4,-3,-7\}
\quad\longleftrightarrow\quad
\{4,3,7\}.
\]

The statement is structural rather than phenomenological.  It does not use
the measured quark masses or CKM angles to choose the number three.  The
number of quark lanes comes from the ordered Heegner carrier together with
the pairwise conductor-coprimality criterion and the explicit exhaustion of
the initial carrier block shown above.
