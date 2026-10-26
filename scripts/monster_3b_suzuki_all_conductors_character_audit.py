#!/usr/bin/env python3
"""Backend-free full-class Q(zeta_n) character audit, arbitrary exact conductor.

Source roots: Barraclough–Wilson (2007), N(3B) table/quotient;
Gabriele Nebe (2025), irreducible Suzuki Sym²12; Serre, finite characters.
Consumes original/source GAP CoeffsCyc(x,Conductor(x)) exports, not their
alleged provenance. Equal full characters != Monster occurrence/intertwiner.
"""
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import gcd,lcm
from pathlib import Path

MAX_CONDUCTOR=4096

def monic_divide(num,den):
    r=list(num);q=[0]*(len(r)-len(den)+1)
    if len(q)<1:raise ValueError("polynomial quotient has negative degree")
    for j in range(len(q)-1,-1,-1):
        v=r[j+len(den)-1];q[j]=v
        for k,t in enumerate(den):r[j+k]-=v*t
    if any(r):raise ValueError("non-exact cyclotomic polynomial quotient")
    return tuple(q)

@lru_cache(None)
def phi_poly(n):
    if type(n)!=int or not (1<=n<=MAX_CONDUCTOR):
        raise ValueError("cyclotomic conductor out of range")
    p=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:p=monic_divide(p,phi_poly(d))
    assert p[-1]==1
    return p

def remainder(poly,mod):
    p=[F(x) for x in poly]
    while len(p)>=len(mod):
        v=p[-1];j=len(p)-len(mod)
        if v:
            for k,t in enumerate(mod):p[j+k]-=v*t
        p.pop()
    return tuple(p+[F(0)]*(len(mod)-1-len(p)))

@dataclass(frozen=True)
class Cyc:
    n:int
    v:tuple
    @classmethod
    def from_coeffs(cls,n,coeff):
        m=phi_poly(n)
        if not isinstance(coeff,(tuple,list)) or len(coeff)!=n:
            raise ValueError("complete conductor coefficient vector required")
        if any(type(v) not in (int,str,F) for v in coeff):
            raise ValueError("cyclotomic coordinates must be exact rationals")
        return cls(n,remainder(coeff,m))
    @classmethod
    def scalar(cls,x):return cls.from_coeffs(1,[x])
    @classmethod
    def wire(cls,x):
        if isinstance(x,dict):
            return cls.from_coeffs(x.get("conductor"),x.get("coefficients"))
        if isinstance(x,(list,tuple)) and len(x)==2:
            return cls.from_coeffs(3,[x[0],x[1],0])
        raise ValueError("bad exact cyclotomic source record")
    def promote(self,n):
        if n%self.n:raise ValueError("non-multiple cyclotomic embedding")
        c=[F(0)]*n
        for j,a in enumerate(self.v):c[j*(n//self.n)]+=a
        return Cyc.from_coeffs(n,c)
    def __add__(self,other):
        if not isinstance(other,Cyc):other=Cyc.scalar(other)
        n=lcm(self.n,other.n)
        return Cyc(n,tuple(a+b for a,b in zip(self.promote(n).v,other.promote(n).v)))
    def __mul__(self,other):
        if not isinstance(other,Cyc):other=Cyc.scalar(other)
        n=lcm(self.n,other.n)
        a=self.promote(n).v;b=other.promote(n).v
        v=[F(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b):
                    if y:v[i+j]+=x*y
        return Cyc(n,remainder(v,phi_poly(n)))
    def __truediv__(self,d):
        v=F(d)
        if not v:raise ZeroDivisionError()
        return Cyc(self.n,tuple(x/v for x in self.v))
    def conjugate(self):
        c=[F(0)]*self.n
        for j,x in enumerate(self.v):c[(-j)%self.n]+=x
        return Cyc.from_coeffs(self.n,c)
    def __eq__(self,other):
        if not isinstance(other,Cyc):other=Cyc.scalar(other)
        n=lcm(self.n,other.n)
        return self.promote(n).v==other.promote(n).v
    def short(self):
        return {"conductor":self.n,"canonical_coefficients":[str(x) for x in self.v]}

def audit(data):
    if not isinstance(data,dict):raise ValueError("source must be object")
    table=data.get("table_id")
    if not isinstance(table,str) or not table:raise ValueError("table_id required")
    orders=data.get("class_orders");power=data.get("power_map_2_zero_based")
    if not isinstance(orders,list) or len(orders)<2 or any(type(x)!=int or x<1 for x in orders):
        raise ValueError("complete class orders required")
    n=len(orders)
    if orders[0]!=1 or not isinstance(power,list) or len(power)!=n or any(type(i)!=int or i not in range(n) for i in power):
        raise ValueError("zero-based full square map required")
    for i,j in enumerate(power):
        if orders[j]!=orders[i]//gcd(orders[i],2):
            raise ValueError(f"class {i}: squared element order inconsistent")
    c2=data.get("central_c2_zero_based");c3=data.get("central_c3_zero_based")
    if type(c2)!=int or type(c3)!=int or c2 not in range(n) or c3 not in range(n) or orders[c2]!=2 or orders[c3]!=3:
        raise ValueError("central C2/C3 class indices invalid")
    sizes=data.get("class_sizes");group_order=data.get("group_order")
    if table=="6.Suz" and (sizes is None or group_order is None):
        raise ValueError("6.Suz requires full class sizes and group order")
    if sizes is not None or group_order is not None:
        if not isinstance(sizes,list) or len(sizes)!=n or any(type(x)!=int or x<1 for x in sizes) or type(group_order)!=int or sum(sizes)!=group_order or sizes[0]!=1 or sizes[c2]!=1 or sizes[c3]!=1:
            raise ValueError("source group order/classes/centre size inconsistent")
    families=[]
    for key,degree in (("degree12",12),("degree78",78)):
        rows=data.get(key)
        if not isinstance(rows,list) or not rows:raise ValueError("missing "+key)
        parsed=[];seen=set()
        for row in rows:
            if not isinstance(row,dict) or not isinstance(row.get("label"),str) or not row["label"] or row["label"] in seen:
                raise ValueError("duplicate/invalid source character label")
            seen.add(row["label"])
            if not isinstance(row.get("values"),list) or len(row["values"])!=n:
                raise ValueError("source character row incomplete")
            values=[Cyc.wire(x) for x in row["values"]]
            if values[0]!=degree:raise ValueError("character has wrong degree")
            if values[c2]!=degree and values[c2]!=-degree:
                raise ValueError("central C2 not scalar on an irreducible")
            parsed.append((row["label"],values))
        families.append(parsed)
    twelve,seventy_eight=families
    if sizes is not None:
        rows=twelve+seventy_eight
        for i,(la,a) in enumerate(rows):
            for j,(lb,b) in enumerate(rows[:i+1]):
                val=Cyc.scalar(0)
                for w,x,y in zip(sizes,a,b):
                    val=val+(x*y.conjugate())*w
                if val!=(group_order if i==j else 0):
                    raise ValueError("source irreducible character orthogonality: "+la+"/"+lb)
    matches=[];differences=[]
    for la,a in twelve:
        sq=[(a[k]*a[k]+a[power[k]])/2 for k in range(n)]
        if sq[0]!=78:raise ValueError("wrong Sym²12 degree")
        for lb,b in seventy_eight:
            for mode,row in (("Sym2",sq),("dualSym2",[v.conjugate() for v in sq])):
                first=next((k for k in range(n) if row[k]!=b[k]),None)
                if first is None:
                    matches.append({"12":la,"78":lb,"mode":mode,"c2_78":b[c2].short(),"c3_78":b[c3].short()})
                else:
                    differences.append({"12":la,"78":lb,"mode":mode,"first_class":first,
                                        "predicted":row[first].short(),"provided":b[first].short()})
    return {"status":"exact_general_cyclotomic_character_audit","table_id_as_provided":table,
            "classes":n,"orthogonality_executed":sizes is not None,
            "matches":matches,"first_disagreements":differences,
            "source_provenance_authenticated":False,"Monster_78_selected":False,
            "GAP_or_Agda_executed":False,"normalizer_intertwiner_proved":False}

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("source_json",type=Path);p.add_argument("--out",type=Path)
    a=p.parse_args()
    result=json.dumps(audit(json.loads(a.source_json.read_text())),indent=2)+"\n"
    if a.out:a.out.write_text(result)
    print(result,end="")
