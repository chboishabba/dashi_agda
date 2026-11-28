"""F8 outgoing m<=6 flux cap in E0..E6 using original GN N(t,1/2).
R=0 supplies a triangular normal-to-time jet elimination. Positive rational
caps are intentionally loose; no independent normal trace assumptions.
"""
from fractions import Fraction as F
from math import comb


def reciprocal_sqrt_caps(order=6):
    # g=sqrt(1+t²) >=1, <=13, |g'|<=1 for t>=1.
    G=[F(13),F(1)]
    for j in range(2,order+1):
        G.append((F(2 if j==2 else 0)+sum(F(comb(j,i))*G[i]*G[j-i] for i in range(1,j)))/2)
    I=[F(1)]
    for j in range(1,order+1):
        I.append(sum(F(comb(j,i))*G[i]*I[j-i] for i in range(1,j+1)))
    return I


def lapse_caps(order=6):
    # N(t,1/2)=cosh(1/2)-t/g sinh(1/2),
    # 3/5<N<7/6, sinh(1/2)<8/15, t<=12.
    I=reciprocal_sqrt_caps(order)
    return [F(7,6)]+[F(8,15)*(12*I[j]+j*I[j-1]) for j in range(1,order+1)]


def outgoing_matrix(order=6):
    # |H_n,t^r|<=sum_i normal[r,i] |H_t^i|.
    # Differentiated outgoing boundary, N0>=3/5.
    nc=lapse_caps(order)
    normal=[];source=[]
    for r in range(order):
        z=[F(0)]*(order+1)
        z[r+1]=1
        for j in range(1,r+1):
            for i,x in enumerate(normal[r-j]):
                z[i]+=comb(r,j)*nc[j]*x
        normal.append([F(5,3)*x for x in z])
    for m in range(1,order+1):
        z=[F(0)]*(order+1)
        for j in range(1,m+1):
            for i,x in enumerate(normal[m-j]):
                z[i]+=comb(m,j)*nc[j]*x
        source.append(z)
    return source


def flux_budget_coeffs(order=6):
    """J_out<=sum_j gamma[m,j] E_j, conditional on exact outgoing R=0.
    B/(4N)=a³/4<=14³/4; |g_m|²<=m sum_i c_i²|H_t^i(out)|².
    FTC trace for i>=1: <=3500/3 E_(i-1)+1250/3 E_i.
    """
    rows=outgoing_matrix(order)
    result=[]
    for m,row in enumerate(rows,1):
        caps=[F(0)]*(order+1)
        for i in range(1,m+1):
            v=F(14**3,4)*m*row[i]**2
            caps[i-1]+=v*F(3500,3)
            caps[i]+=v*F(1250,3)
        result.append(caps)
    return result


def exact():
    caps=flux_budget_coeffs()
    assert len(caps)==6 and all(len(r)==7 for r in caps)
    assert caps[0][0]>0 and caps[0][1]>0
    assert all(c==0 for m,row in enumerate(caps,1) for j,c in enumerate(row) if j>m)
    assert caps[5][6]>0 and caps[5][0]>0
    assert all(c>=0 for row in caps for c in row)
    assert all(x>=0 for x in lapse_caps())
    assert outgoing_matrix(0)==[]
    print('PASS outgoing m1..6 conditional flux <=sum_j gamma[m,j] E_j, finite rational coefficients')
    print('m6 coefficient log10 magnitudes:',
          [len(str(v.numerator))-len(str(v.denominator)) if v else None for v in caps[-1]])


if __name__=='__main__':exact()
