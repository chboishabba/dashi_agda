"""Physical Leray-projection discriminator for canonical NS B-side repairs.

This is NOT a theorem equating the R681 helical mixed carrier to the
Navier--Stokes nonlinearity. It deliberately distinguishes them.
Exact rational/SymPy finite Fourier witness; not an Agda kernel receipt.
"""
import sympy as s

def test_shear_projected_mixed_carrier_zero_but_raw_R681_nonzero():
    ex=s.Matrix([1,0,0]); ey=s.Matrix([0,1,0]); ez=s.Matrix([0,0,1])
    modes=(ex,-ex,ey,-ey)
    output={}
    for p in modes:
        for q in modes:
            hp=(ez+s.I*p.cross(ez))/2
            hm=(ez-s.I*q.cross(ez))/2
            k=tuple(p+q)
            output[k]=output.get(k,s.zeros(3,1))+hp.cross(hm)
    assert len(output)==9
    relative=s.Integer(0)
    for k,m in output.items():
        if k==(0,0,0):
            assert m==s.zeros(3,1)
            continue
        kv=s.Matrix(k); k2=kv.dot(kv)
        projected=s.simplify(m-kv*(kv.dot(m))/k2)
        assert projected==s.zeros(3,1), (k,projected)
        # Every supported input frequency has squared magnitude 1.
        work=s.simplify(2*(s.conjugate(m).dot(m)))
        relative += s.simplify((2-k2)*work)
    assert s.simplify(relative)==-4

def test_real_shear_Navier_Stokes_nonlinearity_zero_pointwise():
    x,y,z,t=s.symbols("x y z t", real=True)
    velocity=s.Matrix([0,0,2*s.exp(-t)*(s.cos(x)+s.cos(y))])
    xyz=(x,y,z)
    assert all(s.simplify(sum(velocity[j]*s.diff(velocity[i],xyz[j])
                         for j in range(3)))==0 for i in range(3))
    assert s.simplify(sum(s.diff(velocity[i],xyz[i]) for i in range(3)))==0
    assert all(s.simplify(s.diff(velocity[i],t)-sum(
        s.diff(velocity[i],v,2) for v in xyz))==0 for i in range(3))
