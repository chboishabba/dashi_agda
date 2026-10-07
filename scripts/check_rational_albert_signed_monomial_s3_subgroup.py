#!/usr/bin/env python3
# Signed-permutation model of the explicit Albert automorphisms constructed in
# RationalOctonionSignedMonomialAutomorphismsExact and
# RationalAlbertS3AutomorphismExact.  Coordinates are
#   a,b,c ; x0..x7 ; y0..y7 ; z0..z7.

ID27=(tuple(range(27)),(1,)*27)

def compose(g,h):
    p,s=g; q,t=h # g after h
    r=tuple(p[q[i]] for i in range(len(p)))
    u=tuple(t[i]*s[q[i]] for i in range(len(p)))
    return r,u

def closure(gens):
    seen={ID27}; todo=[ID27]
    while todo:
        a=todo.pop()
        for g in gens:
            b=compose(g,a)
            if b not in seen:
                seen.add(b); todo.append(b)
    return seen

G7=((2,4,6,3,1,7,5),(1,-1,-1,1,1,1,1))
G2=((1,2,3,5,4,7,6),(-1,1,-1,1,1,1,1))

def lift_oct(g):
    p7,s7=g
    p=list(range(27)); s=[1]*27
    for base in (3,11,19):
        for i in range(1,8):
            p[base+i]=base+p7[i-1]
            s[base+i]=s7[i-1]
    return tuple(p),tuple(s)

def cycle():
    p=list(range(27)); s=[1]*27
    p[0],p[1],p[2]=1,2,0
    for k in range(8):
        p[3+k]=11+k; p[11+k]=19+k; p[19+k]=3+k
    return tuple(p),tuple(s)

def swap():
    p=list(range(27)); s=[1]*27
    p[1],p[2]=2,1
    for base_in,base_out in ((3,3),(11,19),(19,11)):
        p[base_in]=base_out
        for k in range(1,8):
            p[base_in+k]=base_out+k
            s[base_in+k]=-1
    return tuple(p),tuple(s)

og7,og2=lift_oct(G7),lift_oct(G2)
r,s=cycle(),swap()
G_oct=closure([og7,og2])
G_s3=closure([r,s])
G_all=closure([og7,og2,r,s])
assert len(G_oct)==1344
assert len(G_s3)==6
assert len(G_all)==8064
# The two subgroups commute generatorwise and have trivial intersection.
for a in (og7,og2):
    for b in (r,s):
        assert compose(a,b)==compose(b,a)
assert G_oct.intersection(G_s3)=={ID27}
print('octonion signed-monomial subgroup:',len(G_oct))
print('coordinate S3 subgroup:',len(G_s3))
print('combined explicit Albert subgroup:',len(G_all))
print('intersection:',len(G_oct.intersection(G_s3)))
print('PASS')
