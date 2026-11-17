# Order-three Nielsen stabilizer of the ternary parent meridian

Date 2026-10-29. Owner: Alexander horned C3 PR #1244.

## Exact theorem in the free group

Let F3=F(a,b,c), w=[a,b][b,c], u=b^-1, v=c^-1 a, z=c and p=aba^-1c.
The explicit inverse basis substitution is a=zv, b=u^-1, c=z,
and w=p[u,v]p^-1.

Define phi(u)=v, phi(v)=v^-1u^-1, phi(z)=z.
By direct free reduction phi^3(u)=u, phi^3(v)=v, phi^3(z)=z.
Also phi([u,v]) is conjugate to [u,v]. As inner conjugation
intertwines free-group conjugacy classes, phi preserves [w].

In original letters the induced automorphism is:
a -> c a^-1 c b
b -> a^-1 c
c -> c.
This is NONTRIVIAL and has exact order three in Aut(F3), rather than
only Out(F3).

## Correction to scope of the previous no-go

The previous 48-case calculation shows that no signed permutation
of child-meridian labels of order three can preserve the unoriented
parent peripheral class. This theorem shows that the same statement
for *all* automorphisms of F3 would be FALSE. One cannot rule out local
C3-equivariance by the signed-permutation classification alone.

## Important 3D limits

The new phi is an algebraic automorphism. Although handlebody
mapping-class theory supplies realisations of free-group automorphisms
up to appropriate equivalence, no actual cap-relative PL homeomorphism
on the selected THREE-CHILD EXTERIOR has been constructed here.
An algebraic automorphism of order three need not lift to a geometric
homeomorphism of order three fixing the required stationary cap.
Nor is the boundary loop yet represented by a proper embedded
punctured torus with the required selected meridians and based paths.
The target remains G2/G3/G4 geometry, followed by G5/G6 nested wild
limit and actual exterior-group certificate. An order-three map that
fixes c is also NOT the same as a cyclic permutation of three horns.

## Verification and attribution

An equivalent local exact free-word calculation passed: all 3 generator
third powers, peripheral conjugacy and the Nielsen basis transport.
Script: scripts/alexander_horned_order_three_peripheral_nielsen.py.
The committed script, Agda kernel, CI and 3D isotopy are not certified
by this local calculation.

Classical credit: Nielsen free-group automorphisms and punctured-torus
mapping-class/peripheral algebra; Alexander/Hatcher for wild topology;
Hensel for handlebody theory. Existing DASHI ternary bonding-map owner,
#1414 polynomial monodromy, #1405 Sonic Warfare and prior Ibrahim
Monster 3B remain separately attributed. No ESD edits and no
Monster/physical same-object promotion.
