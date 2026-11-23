#!/usr/bin/env python3
"""J24 exact rational guard boxes on six *numerical* event centres.

No validated ODE inclusion or periodic-orbit interval proof is claimed.
The numeric centre JSON is source-labelled independent J23 SciPy evidence.
"""
import json
from fractions import Fraction as F
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "Artifacts/smith-filsinger/j24_six_hybrid_guard_centres_20261123.json"
def frac(x): return F(str(x))
class I:
    def __init__(self, a, b=None):
        self.a=frac(a);self.b=self.a if b is None else frac(b)
        assert self.a<=self.b
    def __add__(self,v):
        v=iv(v);return I(self.a+v.a,self.b+v.b)
    __radd__=__add__
    def __neg__(self): return I(-self.b,-self.a)
    def __sub__(self,v):return self+-iv(v)
    def __rsub__(self,v):return iv(v)+-self
    def __mul__(self,v):
        v=iv(v);q=[self.a*v.a,self.a*v.b,self.b*v.a,self.b*v.b]
        return I(min(q),max(q))
    __rmul__=__mul__
    def __truediv__(self,v):
        v=iv(v)
        assert not(v.a<=0<=v.b)
        return self*I(F(1,v.b),F(1,v.a))
def iv(x):return x if isinstance(x,I) else I(x)
def positive(x):return I(max(x.a,F(0)),max(x.b,F(0)))
def flow_guards(z,on):
    i,j,u,v,b,q,r,ih,x=z
    k=I(F("0.3495"),F("0.3505"))
    kh=I(F("1.9995"),F("2.0005"))
    ju=positive((u-b-F(".1"))/F(".12"))
    jv=positive((v-b-F(".1"))/F(".12"))
    left=-j-ju+k*q+kh*ih
    right=j-jv
    det=F("1.4")*F("1.55")-1
    ud=(F("1.55")*left+right)/det
    vd=(left+F("1.4")*right)/det
    bd=(ju+jv-F(".018")*b-iv(int(on))*ih)/F(".65")
    return ud,vd,bd
def run():
    src=json.loads(DATA.read_text())
    assert src["state_halfwidth"]=="0.0001"
    assert src["parameter_halfwidths"]=={"k":"0.0005","kh":"0.0005"}
    rows=[]
    for event in src["events"]:
        radius=F(src["state_halfwidth"])
        z=[I(frac(v)-radius,frac(v)+radius) for v in event["x"]]
        u,v,b=flow_guards(z,event["on"])
        if event["kind"]=="spark":
            margin=-b if event["name"]=="off" else b
            other=flow_guards(z,not event["on"])[2]
            determinant=other/b
            assert determinant.b<0
            det_pair=[float(determinant.a),float(determinant.b)]
        else:
            guard=(u-b) if event["name"]=="U" else (v-b)
            margin=iv(event["sign"])*guard
            det_pair=None # continuous diode vector field: identity saltation
        assert margin.a>0
        rows.append(dict(t=event["t"],kind=event["kind"],name=event["name"],
           slope_lower=float(margin.a),slope_upper=float(margin.b),
           spark_saltation_determinant_interval=det_pair))
    assert [(r["kind"],r["name"]) for r in rows]==[
        ("diode","V"),("spark","off"),("spark","on"),
        ("diode","U"),("diode","V"),("diode","U")]
    return dict(status="PASS_EXACT_RATIONAL_CONDITIONAL_EVENT_BOXES_ONLY",
        event_count=len(rows),rows=rows,
        minimum_slope_lower=min(q["slope_lower"] for q in rows),
        source_numerical_event_centres_not_validated_enclosures=True,
        requires_validated_ODE_flow_to_enter_each_box=True,
        requires_validated_return_map_and_jacobian=True,
        exact_periodic_orbit_proved=False,
        original_device_or_environmental_source_proved=False,
        ci_used=False)
if __name__=="__main__":print(json.dumps(run(),indent=2,sort_keys=True))
