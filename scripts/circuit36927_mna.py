"""DASHI independent RLC modified-nodal reference. No vendor wiring/CAD.
Ideal wires merge nodes; R/C/L retain constitutive relations. Backward Euler.
Models passive R,L,C and ideal DC voltage/current sources; NOT switches or
magnetic coupling, measured motor efficiency, or anomalous power.
"""
from dataclasses import dataclass, field
from math import isfinite, exp

@dataclass(frozen=True)
class Part:
    name: str
    kind: str
    value: float

@dataclass
class Circuit:
    parts: tuple[Part,...]
    wires: tuple[tuple[str,str],...]
    ground: str
    attribution: str = "Original DASHI illustrative model"

    def nodes(self):
        names=[p.name for p in self.parts]
        if len(set(names))!=len(names): raise ValueError("duplicate part")
        pins={f"{p.name}.{pin}" for p in self.parts for pin in ("a","b")}
        if self.ground not in pins: raise ValueError("invalid ground")
        for p in self.parts:
            if p.kind not in {"resistor","capacitor","inductor","vsource","isource"}:
                raise ValueError("unsupported part type")
            if not isfinite(p.value) or (p.kind in {"resistor","capacitor","inductor"} and p.value<=0):
                raise ValueError("invalid passive value")
        parent={pin:pin for pin in pins}
        def find(x):
            while parent[x]!=x:
                parent[x]=parent[parent[x]];x=parent[x]
            return x
        for x,y in self.wires:
            if x not in pins or y not in pins: raise ValueError("invalid wire pin")
            parent[find(x)]=find(y)
        groups={pin:find(pin) for pin in pins}
        ground=find(self.ground)
        indexed={g:i for i,g in enumerate(sorted(set(groups.values())-{ground}))}
        return {pin:indexed.get(g) for pin,g in groups.items()}, len(indexed)

def solve(a,b):
    a=[list(row)+[rhs] for row,rhs in zip(a,b)]
    n=len(b)
    for k in range(n):
        pivot=max(range(k,n),key=lambda j:abs(a[j][k]))
        if abs(a[pivot][k])<1e-13: raise ValueError("floating or singular network")
        a[k],a[pivot]=a[pivot],a[k]
        d=a[k][k]
        for j in range(k,n+1): a[k][j]/=d
        for i in range(k+1,n):
            c=a[i][k]
            for j in range(k,n+1): a[i][j]-=c*a[k][j]
    x=[0.0]*n
    for i in range(n-1,-1,-1):
        x[i]=a[i][n]-sum(a[i][j]*x[j] for j in range(i+1,n))
    return x

@dataclass
class Solver:
    network: Circuit
    previous_cap_voltage: dict = field(default_factory=dict)
    previous_inductor_current: dict = field(default_factory=dict)

    def step(self,dt):
        if not isfinite(dt) or dt<=0: raise ValueError("dt must be positive")
        pins,n=self.network.nodes()
        branches=[p for p in self.network.parts if p.kind in ("vsource","inductor")]
        branch={p.name:n+i for i,p in enumerate(branches)}
        size=n+len(branches)
        mat=[[0.0]*size for _ in range(size)]
        rhs=[0.0]*size
        def ends(p):return pins[p.name+".a"],pins[p.name+".b"]
        def stamp(p,g,old=0):
            x,y=ends(p)
            for i,j,co in ((x,x,g),(y,y,g),(x,y,-g),(y,x,-g)):
                if i is not None and j is not None:mat[i][j]+=co
            if x is not None:rhs[x]+=g*old
            if y is not None:rhs[y]-=g*old
        for p in self.network.parts:
            x,y=ends(p)
            if p.kind=="resistor": stamp(p,1/p.value)
            elif p.kind=="capacitor": stamp(p,p.value/dt,self.previous_cap_voltage.get(p.name,0.0))
            elif p.kind=="isource":
                if x is not None:rhs[x]-=p.value
                if y is not None:rhs[y]+=p.value
            else:
                k=branch[p.name]
                for i,sign in ((x,1.0),(y,-1.0)):
                    if i is not None:
                        mat[i][k]+=sign;mat[k][i]+=sign
                if p.kind=="vsource":rhs[k]=p.value
                else:
                    rate=p.value/dt
                    mat[k][k]-=rate
                    rhs[k]=-rate*self.previous_inductor_current.get(p.name,0.0)
        sol=solve(mat,rhs)
        voltages={};currents={};residual=[0.0]*n
        for p in self.network.parts:
            x,y=ends(p)
            v=(sol[x] if x is not None else 0)-(sol[y] if y is not None else 0)
            voltages[p.name]=v
            if p.kind=="resistor":i=v/p.value
            elif p.kind=="capacitor":
                i=p.value*(v-self.previous_cap_voltage.get(p.name,0.0))/dt
                self.previous_cap_voltage[p.name]=v
            elif p.kind=="isource":i=p.value
            else:
                i=sol[branch[p.name]]
                if p.kind=="inductor":self.previous_inductor_current[p.name]=i
            currents[p.name]=i
            if x is not None:residual[x]+=i
            if y is not None:residual[y]-=i
        return {"voltages":voltages,"currents":currents,"node_residual":residual}

def example_rc():
    return Circuit((Part("V","vsource",12),Part("R","resistor",1000),
                    Part("C","capacitor",3.3e-6)),
      (("V.a","R.a"),("R.b","C.a"),("C.b","V.b")),"V.b")

def test():
    rc=Solver(example_rc());dt=.00033;n=100;v=0.
    for _ in range(n):
        old=v;r=rc.step(dt);v=r["voltages"]["C"]
        assert max(map(abs,r["node_residual"]))<1e-9
        assert abs(r["currents"]["R"]-r["currents"]["C"])<1e-9
        assert abs(r["voltages"]["V"]-r["voltages"]["R"]-v)<1e-9
        source=-r["voltages"]["V"]*r["currents"]["V"]
        dissipated=1000*r["currents"]["R"]**2
        storage=0.5*3.3e-6*(v*v-old*old)/dt
        numerical=0.5*3.3e-6*(v-old)**2/dt
        assert abs(source-dissipated-storage-numerical)<1e-8
    expected=12*(1-(1+dt/.0033)**(-n))
    assert abs(v-expected)<1e-8
    assert abs(v-12*(1-exp(-n*dt/.0033)))<.001
    rl=Circuit((Part("V","vsource",10),Part("R","resistor",10),
                Part("L","inductor",1)),
      (("V.a","R.a"),("R.b","L.a"),("L.b","V.b")),"V.b")
    rlstep=Solver(rl).step(.1)
    assert abs(rlstep["currents"]["L"]-.5)<1e-10
    assert max(map(abs,rlstep["node_residual"]))<1e-10
    try:
        Circuit(example_rc().parts,(("V.a","R.missing"),),"V.b").nodes()
        raise AssertionError("invalid pin accepted")
    except ValueError:pass
    try:
        floating=Circuit((Part("R","resistor",10),Part("Q","resistor",20)),(),"R.b")
        Solver(floating).step(1)
        raise AssertionError("floating component accepted")
    except ValueError:pass
    return {"rc_voltage_V":v,"rc_backward_euler_reference_V":expected,
            "rl_first_step_current_A":rlstep["currents"]["L"],
            "node_balance":"passed","discrete_energy_identity":"passed"}
if __name__=="__main__":
    import json
    print(json.dumps(test(),indent=2))
