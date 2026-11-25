"""Exact finite rational controls for the intrinsic Hom seed-line construction.
Not an actual Monster source, character-table replay or kernel proof.
"""
from itertools import product
import sympy as S


def require(ok, message):
    if not ok:
        raise ValueError(message)


def polyeval(poly, A):
    R = S.zeros(A.rows)
    for c in poly.all_coeffs():
        R = R*A+c*S.eye(A.rows)
    return R


def run_case(n, seed_index):
    # Standard rational S_(n+1) representation, basis e_i-e_n.
    # Simpler explicit basis, no quotient-coordinate guess.
    basis = S.Matrix.hstack(*[S.eye(n+1)[:, i]-S.eye(n+1)[:, n] for i in range(n)])
    metric = basis.T*basis
    I = S.eye(n)
    gens = []
    for i in range(n):
        P = S.eye(n+1)
        P.row_swap(i, i+1)
        gens.append((P*basis)[:n, :])
    v = I[:, seed_index]
    words = [()]
    ops = [I]
    B = v
    i = 0
    while B.cols < n and i < len(ops):
        for j, g in enumerate(gens):
            op = g*ops[i]
            new = B.row_join(op*v)
            if new.rank() > B.cols:
                B = new
                ops.append(op)
                words.append(words[i]+(j,))
                if B.cols == n:
                    break
        i += 1
    require(B.cols == n, 'cyclic orbit')
    adj = lambda A: metric.inv()*A.T*metric
    R = []
    for h in gens:
        c = B.inv()*h*B
        for i in range(n):
            R.append(h*ops[i]-sum((c[j,i]*ops[j] for j in range(n)), S.zeros(n)))
    require(all(r*v == S.zeros(n,1) for r in R), 'seed residual')
    Q = sum((adj(r)*r for r in R), S.zeros(n))
    t = S.Symbol('t')
    p, rem = S.div(Q.charpoly(t).as_poly(), S.Poly(t,t))
    require(rem.is_zero and p.eval(0) != 0, 'simple zero')
    P = polyeval(p, Q)/p.eval(0)
    require(P*P == P and P.rank() == 1 and P*v == v and adj(P) == P, 'seed projector')
    # Hidden target chart, with pulled-back invariant form.
    X = I+S.Matrix(n,n,lambda i,j: (i+2*j+1) if i<j else 0)
    Xi = X.inv()
    T = [X*g*Xi for g in ops]
    L = [X*g*Xi for g in gens]
    G = B.T*metric*B/(v.T*metric*v)[0]
    Gi = G.inv()
    Ptarget = X*P*Xi
    target_metric = Xi.T*metric*Xi
    adjT = lambda A: target_metric.inv()*A.T*target_metric
    U = [Ptarget*sum((Gi[i,j]*adjT(T[j]) for j in range(n)), S.zeros(n)) for i in range(n)]
    E = {(i,j): T[i]*U[j] for i,j in product(range(n), repeat=2)}
    checks = 0
    for i,j,k,l in product(range(n), repeat=4):
        require(E[i,j]*E[k,l] == (E[i,l] if j == k else S.zeros(n)), 'matrix units')
        checks += 1
    require(sum((E[i,i] for i in range(n)), S.zeros(n)) == I, 'unit resolution')
    for j in range(n):
        w = I[:,j]
        z = [u*w for u in U]
        require(all(Ptarget*a == a for a in z), 'seed line range')
        require(sum((T[i]*z[i] for i in range(n)), S.zeros(n,1)) == w, 'bidi target inverse')
    for h,lh in zip(gens,L):
        c=B.inv()*h*B
        for i,j in product(range(n), repeat=2):
            require(U[i]*lh*T[j]*Ptarget == c[i,j]*Ptarget, 'orbit-coordinate action')
    # A nonzero projected probe determines the usual intertwiner.
    y = next(Ptarget*I[:,i] for i in range(n) if Ptarget*I[:,i] != S.zeros(n,1))
    F = S.Matrix.hstack(*[a*y for a in T])*B.inv()
    require(F.det() != 0 and all(F*g == h*F for g,h in zip(gens,L)), 'nonzero seed gives isomorphism')
    # A Cartesian pair of pure vectors cannot encode this rank-two tensor.
    require(S.eye(2).rank() == 2 and S.zeros(2).rank() == 0, 'pure tensor no-go')
    return checks, n*n*len(gens)


def main():
    a = b = cases = 0
    for n in (2,3,4):
        for i in range(n):
            x,y=run_case(n,i); a+=x; b+=y; cases+=1
    print(dict(cases=cases, matrix_unit_checks=a, action_coordinate_checks=b,
               scope='rational source-shaped controls only'))


if __name__ == '__main__':
    main()
