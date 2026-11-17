# Signed child-label stabilizer: complete 48-case audit

Owner: Alexander horned C3 PR #1244, 29 October 2026.

In the free group F(a,b,c), let w=[a,b][b,c]=abAcBC, uppercase denoting inverse.
For the signed permutation group (C2)^3 semidirect S3, size 48, classify all
maps sigma for which sigma(w) is conjugate to w or w^-1. The cyclically reduced
free-group conjugacy criterion gives precisely four:
- (a,b,c): preserves orientation;
- (a,b^-1,c): reverses parent orientation;
- (c,b,a): reverses parent orientation;
- (c,b^-1,a): preserves parent orientation.

These four form a Klein four subgroup. Thus NO signed three-cycle of the
child generators stabilizes the unoriented peripheral conjugacy class.
This is a CONDITIONAL obstruction only when the chosen geometric action
induces a signed permutation in this particular complementary-meridian chart.
It does not classify general Nielsen automorphisms, basepoint-path effects,
or an external C3 permuting three complete root sectors.

The accompanying exact finite script enumerates all 48 cases using reduced
free words and cyclic conjugacy. An equivalent local file executed PASS.
The committed script, Agda kernel and CI have not been executed here.
No actual cap-relative PL slide, embedded punctured-torus complement chart,
geometric stage inclusion, infinite wild limit or exterior pi1 identification
is claimed. G2-G6 remain open, while the G1 tame carrier is independently known.

Credit the classical free-group conjugacy theorem, Alexander/Hatcher for wild
topology, Nielsen and Hensel for handlebody theory, and the original DASHI
owners for the ternary bonding word. Preserve separate ownership of #1414
polynomial monodromy, #1405 Sonic Warfare and Ibrahim Monster 3B. No Monster
same-object inference, physical interpretation or ESD edit follows.
