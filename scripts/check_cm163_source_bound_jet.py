#!/usr/bin/env python3
"""Original CM163 diagonal/slice coefficient replay and signed jet certificate.

UNEXECUTED when authored. Reuses the existing j_unit and dyadic source
owners; independent of descending polynomial extraction, not an independent
analytic j producer. Accepts the signed-hex descending coefficient packet
from check_cm163_backend_parity.py, or constructs it with the original
scalar producers. No floating-point acceptance and no quadratic-field
inversion. Not a native or universal analytic proof.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

import check_cm163_modular_diagonal as base
import check_cm163_derivative_slice as jet
import check_cm163_dyadic_j_integer_certificate as dyadic

P = 41
K = -640320**3
A, B = 13591409, 545140134
PINNED = {
    "check_cm163_modular_diagonal.py": "add8e35866aa1e9f379b4a57059c4487e4c7241c",
    "check_cm163_derivative_slice.py": "0c1f7d04618943d6b9941f433ceed8c5cd9fd590",
    "check_cm163_dyadic_j_integer_certificate.py": "8581a684cfb6ba6bfbfa45adbf6bfe01e9617258",
}

def require(ok, msg):
    if not ok:
        raise AssertionError(msg)

def git_blob(path):
    raw = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

def verify_sources():
    for name, expected in PINNED.items():
        require(git_blob(Path(__file__).resolve().parent / name) == expected,
                "changed source: " + name)

def conv(a, b, degree):
    # Coefficient-oriented replay, rather than the producer's scatter loop.
    return [sum(a[i] * b[k-i]
                for i in range(max(0, k-len(b)+1), min(k+1, len(a))))
            for k in range(degree+1)]

def unit_norm(h, degree):
    """Unique coefficient solution of H*L=tH', then N'=filtered L*N."""
    require(h[0] == 1 and len(h) == P*degree+1, "unit/truncation")
    log = [0]
    for n in range(1, len(h)):
        log.append(n*h[n] - sum(h[i]*log[n-i] for i in range(1,n)))
    norm = [1]
    for n in range(1, degree+1):
        z = sum(log[P*i]*norm[n-i] for i in range(1,n+1))
        q, rem = divmod(z,n)
        require(rem == 0, "norm division at " + str(n))
        norm.append(q)
    return norm

def normalized_product(kind, j):
    degree = 2*P if kind == "diagonal" else P+1
    m = P*degree
    h = [0]*(m+1)
    inf = [0]*(degree+1)
    if kind == "diagonal":
        for i in range(degree+1):
            h[P*i] += j[i]
        for i in range(m-P+2):
            h[i+P-1] -= j[i]
        for i in range(degree-P+2):
            inf[i+P-1] += j[i]
        for i in range(degree//P+1):
            inf[P*i] -= j[i]
    elif kind == "slice":
        h = list(j[:m+1])
        h[1] -= K
        for i in range(degree//P+1):
            inf[P*i] += j[i]
        inf[P] -= K
    else:
        raise ValueError(kind)
    return conv(inf, unit_norm(h,degree), degree)

def polynomial_laurent(coeff, j):
    """Replay q^d poly(j(q)) directly, no triangular coefficient extraction."""
    d = len(coeff)-1
    power = [1]+[0]*d
    out = [0]*(d+1)
    for i, c in enumerate(coeff):  # ascending input
        for k in range(i+1):
            out[d-i+k] += c*power[k]
        if i < d:
            power = conv(power,j[:d+1],d)
    return out

def shift(coeff, center):
    """Integer Horner composition poly(center+x), ascending output."""
    out = [0]
    for c in reversed(coeff):
        nxt = [0]*(len(out)+1)
        for i,v in enumerate(out):
            nxt[i] += center*v
            nxt[i+1] += v
        nxt[0] += c
        out = nxt
    require(out[-1] == 0, "Horner padding")
    return out[:-1]

def read_or_construct(path):
    if path:
        raw = json.loads(Path(path).read_text())
        require(isinstance(raw,list) and len(raw)==2,"two polynomials")
        require(all(isinstance(v,list) and all(isinstance(c,str) for c in v)
                    for v in raw), "signed hexadecimal packet")
        return [list(reversed([int(c,16) for c in v])) for v in raw]
    return [list(reversed([int(c) for c in poly.all_coeffs()]))
            for poly in (base.diagonal(P),jet.slice_poly(P,K))]

def verify(coeff, slice_coeff):
    require(len(coeff)==83 and coeff[-1]==-1,"diagonal degree/leading sign")
    require(len(slice_coeff)==43 and slice_coeff[-1]==1,"slice degree/leading sign")
    j = base.j_unit(P*(2*P))
    require(j[0]==1,"original unit")
    require(polynomial_laurent(coeff,j)==normalized_product("diagonal",j),
            "diagonal original Laurent replay")
    require(polynomial_laurent(slice_coeff,j)==normalized_product("slice",j),
            "slice original Laurent replay")
    dp, sp = shift(coeff,K), shift(slice_coeff,K)
    require(dp[:2]==sp[:2]==[0,0],"constant and linear residuals")
    require(dp[2]!=0 and sp[2]!=0,"nonzero transverse and diagonal coefficient")
    # Exact factorization is the shifted coefficient identity itself.
    a = dp[2:]
    d = len(a)-1
    left = abs(a[0]) << d
    right = sum(abs(c) << (d-i) for i,c in enumerate(a[1:],1))
    require(left>right,"half-unit complementary factor dominance")
    enclosure = dyadic.certify(128)
    lo,hi = enclosure["j_lower_offset"],enclosure["j_upper_offset"]
    require(enclosure["target"]==K and -F(1,2)<lo<=hi<F(1,2),"literal enclosure")
    scale = 1<<128
    require(lo*scale == -121397398953732472506062368501224644 and
            hi*scale == 12147930101178244703017603450764613085,
            "original Agda dyadic endpoint receipt")
    p2,p3,s2,s3 = dp[2],dp[3],sp[2],sp[3]
    require(41*p2==163*s2,"quadratic tangent relation")
    require(p3%2==0,"symmetric cubic integral coefficient")
    c11,c21 = p2-2*s2,p3//2-s3
    require(41*c11==81*s2,"transverse mixed quadratic")
    numerator, denominator = 41*p3-326*s3,163*s2
    require(numerator==2*(41*c21-122*s3),"cubic numerator")
    kappa = F(numerator,denominator)
    require(kappa==F(p3,p2)-2*F(s3,s2),"two-slice invariant")
    correction = 4+3*F(K,K-1728)-6*K*kappa
    require(correction==F(77265280,90856689),"derived CM correction")
    require((1-correction)/6==F(A,B),"terminal ratio")
    require(144*B*B==163*((-K)+1728),"positive normalization")
    return {
        "source_blobs": PINNED, "p":P, "K":K,
        "diagonal_degree":82,"slice_degree":42,
        "shifted_diagonal": [hex(c) for c in dp],
        "shifted_slice": [hex(c) for c in sp],
        "dominance_left":hex(left),"dominance_right":hex(right),
        "kappa":[hex(kappa.numerator),hex(kappa.denominator)],
        "correction":[correction.numerator,correction.denominator],
        "dyadic_offsets":[str(lo),str(hi)],
        "scope":"finite replay only; analytic source binding and kernel reflection external",
    }

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--coefficients", help="existing backend-parity signed-hex packet")
    p.add_argument("--output", help="optional finite receipt JSON")
    args = p.parse_args()
    verify_sources()
    result = verify(*read_or_construct(args.coefficients))
    if args.output:
        Path(args.output).write_text(json.dumps(result,indent=2)+"\n")
    print("PASS finite original CM diagonal/slice Laurent replay, isolation and signed scalar jet")
    print(result["scope"])

if __name__=="__main__":
    main()
