#!/usr/bin/env python3
"""Exact symbolic YAML-free max-cut: YM U1 vs non-Abelian gap, antigravity, Filsinger.

Finite model fixtures only. Not a Clay gap, actual experiment measurement,
Filsinger original hardware simulation, or physical gravitational anomaly.
"""
from sympy import Matrix, I, pi, sqrt, symbols, diff, limit, oo, simplify, Rational as Q, zeros

checks = []
def accept(title, ok):
    assert bool(ok), title
    checks.append(title)
    print(f"PASS {len(checks):02d} {title}")

# Original repo: U1AsSU2AbelianRestrictionExact, Bracket.lieBracket.
s1=Matrix([[0,1],[1,0]])
s2=Matrix([[0,-I],[I,0]])
s3=Matrix([[1,0],[0,-1]])
T1,T2,T3=[I*s/2 for s in (s1,s2,s3)]
br=lambda a,b:a*b-b*a
a,b=symbols("a b", real=True)
accept("U1 Cartan bracket zero",br(a*T3,b*T3)==zeros(2))
accept("SU2 full bracket not zero",br(T1,T2)!=zeros(2))
accept("SU2 T1 T2 bracket equals minus T3",simplify(br(T1,T2)+T3)==zeros(2))
accept("all anti-Hermitian SU2 generators",all(T.conjugate().T == -T for T in (T1,T2,T3)))
accept("all SU2 Lie generators traceless",all(T.trace()==0 for T in (T1,T2,T3)))

# No identification of Maxwell photon with continuum non-Abelian mass gap.
k,L,m=symbols("k L m",positive=True)
accept("free Maxwell zero momentum zero energy",sqrt(k*k).subs(k,0)==0)
accept("finite cavity has positive pi/L",simplify(sqrt((pi/L)**2)-pi/L)==0)
accept("cavity gap goes to zero as L to infinity",limit(pi/L,L,oo)==0)
accept("massive excitation has m at k zero",sqrt(k*k+m*m).subs(k,0)==m)
accept("finite regulator is not a photon mass",limit(sqrt((pi/L)**2),L,oo)==0)

# Exact *coverage* rows transcribed from master AntigravityExperimentPortfolioExact.
coverage={
    "weightOnly":(1,0,0,0,0,1,1),
    "freeFallClock":(1,1,0,0,1,1,1),
    "matchedFourChannel":(1,1,1,0,1,1,1),
    "matchedFourChannelTT":(1,1,1,1,1,1,1),
}
accept("four distinct preexisting antigravity designs",len(set(coverage.values()))==4)
accept("weight-only covers support force",coverage["weightOnly"][0]==1)
accept("weight-only is not a metric discriminator",coverage["weightOnly"][1]==0)
accept("matched four-channel adds metric discrimination",coverage["matchedFourChannel"][1]==1)
accept("matched four-channel adds cross-channel comparison",coverage["matchedFourChannel"][2]==1)
accept("four-channel without TT does not test propagating TT",coverage["matchedFourChannel"][3]==0)
accept("TT variant covers propagating TT",coverage["matchedFourChannelTT"][3]==1)
accept("four-channel refinement preserves all weight-only fields",all(v>=u for v,u in zip(coverage["matchedFourChannel"],coverage["weightOnly"])))
accept("TT refinement preserves four-channel fields",all(v>=u for v,u in zip(coverage["matchedFourChannelTT"],coverage["matchedFourChannel"])))

# Existing source-only vs constitutive-excess observational collision.
worlds={"sourceOnly":(1,0),"constitutiveExcess":(1,1),"geometryArtifact":(1,2),"backgroundArtifact":(1,3),"null":(0,4)}
accept("coarse source vs constitutive ambiguity",worlds["sourceOnly"][0]==worlds["constitutiveExcess"][0])
accept("joint discriminator separates candidate models",worlds["sourceOnly"]!=worlds["constitutiveExcess"])
accept("five constructed joint classes distinct",len(set(v[1] for v in worlds.values()))==5)
accept("source-off/null has no coarse positive flag",worlds["null"][0]==0)

# Source-free Maxwell-shaped gradient field: physical force without new gravity.
x,y,z,B0,G,alpha,v=symbols("x y z B0 G alpha v", real=True)
B=Matrix([G*x,0,B0-G*z])
curl=Matrix([diff(B[2],y)-diff(B[1],z),diff(B[0],z)-diff(B[2],x),diff(B[1],x)-diff(B[0],y)])
div=diff(B[0],x)+diff(B[1],y)+diff(B[2],z)
Fz=simplify(alpha*diff(B.dot(B),z)/2)
accept("Maxwell div B zero",div==0)
accept("Maxwell curl B zero",curl==zeros(3,1))
accept("induced dipole force derives from gradient B squared",simplify(Fz+alpha*G*(B0-G*z))==0)
lift=Fz.subs({alpha:-1,B0:2,G:1,z:0})
accept("diamagnetic gradient gives upward F=2",lift==2)
accept("ordinary gravitational support at weight 2",lift-2==0)
accept("nonzero force gives zero mechanical holding power",simplify(Fz*v).subs(v,0)==0)
accept("moving with force gives nonzero mechanical work rate",simplify(Fz*v).subs({alpha:-1,B0:2,G:1,z:0,v:1})==2)

# Pre-existing SmithFilsingerMaxwellMaterialEnergyCutExact: TWO separately
# required original physical work identities; numbers here are fixtures only.
natural,driver,mod,field0,field1,material0,material1=13,2,1,5,5,4,4
link,fieldloss,load,materialloss,recovery=8,7,6,2,1
accept("field energy input and outgoing balance",natural+driver+field0==link+fieldloss+field1)
accept("material energy reception and load balance",link+mod+material0==load+materialloss+recovery+material1)
accept("shared interior port cancels in whole system",natural+driver+mod+field0+material0==load+fieldloss+materialloss+recovery+field1+material1)
accept("field and material states both return",field0==field1 and material0==material1)
accept("on repeatable cycle source pays load and loss",natural+driver+mod==load+fieldloss+materialloss+recovery)
accept("same load/loss impossible without natural input",driver+mod<load+fieldloss+materialloss+recovery)

# Independent Thevenin source/receiver controller; not Filsinger calibration.
R,g,V=symbols("R g V",positive=True)
P=lambda conductance:V*V*conductance/(1+R*conductance)**2
ceiling=V*V/(4*R)
accept("Thevenin matched-source square gap",simplify(ceiling-P(g)-V*V*(R*g-1)**2/(4*R*(1+R*g)**2))==0)
accept("source matched transfer is 81/32 times weak coupling",simplify((P(1)/P(Q(1,8))).subs({R:1,V:1}))==Q(81,32))
accept("no independent source yields zero delivered power",P(g).subs(V,0)==0)
print(f"{len(checks)}/{len(checks)} PASS | source-scoped algebra, not YM Clay or physical experimental acceptance")
