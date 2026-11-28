"""F8 original GN normal inverse C5 rational majorants.
Extends scalar_chart_trace and characteristic_jet_caps; does not claim
7th-order tangential energy or source residual control.
"""
from math import comb
from fractions import Fraction as F
from check_f8_characteristic_jet_caps import monomial_caps,sqrt_and_inverse_caps

def derivative_product(x,y,order):
    return [sum(F(comb(j,i))*x[i]*y[j-i] for i in range(j+1)) for j in range(order+1)]

def gn_wall_caps(K,order=5):
    """A=B=t³, At=3t², An=t⁴/g-3t²g, Bn=-t⁴/g-3t²g,
    Atn=dt An, Bnn=16t³+6t, C=tk², Cn=-k²(t²/g+g).
    """
    if F(K)<0:raise ValueError('K must be nonnegative')
    G,I=sqrt_and_inverse_caps(order+1)
    t4,t3,t2,t1=tuple(monomial_caps(z,order+1) for z in (4,3,2,1))
    t4I=derivative_product(t4,I,order+1)
    t2G=derivative_product(t2,G,order+1)
    an=[t4I[j]+3*t2G[j] for j in range(order+2)]
    cnI=derivative_product(t2,I,order+1)
    cn=[F(K)**2*(cnI[j]+G[j]) for j in range(order+1)]
    return {'A':t3[:order+1], 'B':t3[:order+1],
            'C':[F(K)**2*z for z in t1[:order+1]],
            'At':[3*z for z in t2[:order+1]],
            'Bn':an[:order+1], 'An':an[:order+1],
            'Atn':an[1:order+2],
            'Bnn':[16*t3[j]+6*t1[j] for j in range(order+1)],
            'Cn':cn}

def inverse_caps(H,N1,Fjets,Fn,coeff,order=5):
    """Positive envelopes for N2_j,N3_j. Original B=t³>=1."""
    if min(map(len,(H,N1)))<order+3 or min(map(len,(Fjets,Fn)))<order+1:
        raise ValueError('missing seventh tangential/first-normal or source jets')
    if any(len(seq)<order+1 for seq in coeff.values()):
        raise ValueError('missing coefficient caps')
    if min(F(x) for arr in (H,N1,Fjets,Fn,*coeff.values()) for x in arr)<0:
        raise ValueError('negative absolute envelope')
    N2=[];N3=[]
    for j in range(order+1):
        q=F(Fjets[j])+sum(F(comb(j,i))*(coeff['A'][i]*H[j-i+2]
          +coeff['At'][i]*H[j-i+1]+coeff['Bn'][i]*N1[j-i]
          +coeff['C'][i]*H[j-i]) for i in range(j+1))
        q+=sum(F(comb(j,i))*coeff['B'][i]*N2[j-i] for i in range(1,j+1))
        N2.append(q)
        z=F(Fn[j])+sum(F(comb(j,i))*(coeff['An'][i]*H[j-i+2]
          +coeff['A'][i]*N1[j-i+2]+coeff['Atn'][i]*H[j-i+1]
          +coeff['At'][i]*N1[j-i+1]+coeff['Bnn'][i]*N1[j-i]
          +2*coeff['Bn'][i]*N2[j-i]+coeff['Cn'][i]*H[j-i]
          +coeff['C'][i]*N1[j-i]) for i in range(j+1))
        z+=sum(F(comb(j,i))*coeff['B'][i]*N3[j-i] for i in range(1,j+1))
        N3.append(z)
    return N2,N3

def exact():
    from sympy import symbols, sqrt, diff
    t,k=symbols('t k',positive=True);g=sqrt(1+t*t)
    formulas={'An':t**4/g-3*t*t*g,'Bn':-t**4/g-3*t*t*g,
              'Atn':diff(t**4/g-3*t*t*g,t),
              'Bnn':16*t**3+6*t,'Cn':-k*k*(t*t/g+g)}
    coeff=gn_wall_caps(40)
    for key,formula in formulas.items():
        for j in range(6):
            for ti in (1,2,12):
                val=abs(diff(formula,t,j).subs({t:ti,k:40}).evalf())
                assert val<=float(coeff[key][j]),(key,j,ti,val)
    H=[F(1)]*8;N1=[F(1)]*8;F0=[F(0)]*6
    q,r=inverse_caps(H,N1,F0,F0,coeff)
    assert len(q)==len(r)==6 and all(x>=0 for x in q+r)
    f1=F0[:];f1[0]=1
    q1,r1=inverse_caps(H,N1,f1,F0,coeff)
    assert q1[0]>q[0] and r1[0]>r[0]
    fn1=F0[:];fn1[0]=1
    qr,rr=inverse_caps(H,N1,F0,fn1,coeff)
    assert qr==q and rr[0]>r[0]
    try:inverse_caps(H[:7],N1,F0,F0,coeff)
    except ValueError:pass
    else:raise AssertionError('missing H7 accepted')
    print('PASS exact F8 original GN inverse coefficient caps, N2/N3 C5 and F/Fn negative controls')

if __name__=='__main__':exact()
