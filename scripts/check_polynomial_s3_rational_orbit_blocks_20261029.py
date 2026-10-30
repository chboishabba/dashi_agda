#!/usr/bin/env python3
"""Exact native 27-code rational S3 block audit for PR #1414.

No third-party dependency. Reads ACTUAL checked-out Agda matrix / code
tables, checks two-sided exact scaled integer inverse certificates,
all 216 regular-block intertwining cases, all 162 native S3 actions,
and nonzero exact determinants of the seven 1/2/3/6 orbit blocks.

This is computational proof-support evidence, not an Agda kernel
receipt, global polynomial Galois proof, or Monster3B same-object claim.
Classical S3 representation theory predates these implementation files.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
PROOFS=ROOT/"DASHI"/"Foundations"
NAMES=[
    "PolynomialS3RegularRationalBlockCertificateExact",
    "PolynomialS3SmallRationalBlockCertificateExact",
    "PolynomialS3RegularOrbitToNativeCodeExact",
    "PolynomialS3TwentySevenOrbitBlockAssemblyExact",
]

def owner(name):
    f=PROOFS/(name+".agda")
    assert f.is_file(), f"missing Agda owner {f}"
    return f.read_text(encoding="utf-8")

def integer_matrices(source,name,n,prefix):
    pat=re.compile(r"^"+name+r" "+prefix+r"([0-9]) "+prefix+
                   r"([0-9]) = (pos|negsuc) ([0-9]+)$",re.M)
    a=[[None for _ in range(n)] for _ in range(n)]
    for i,j,mode,v in pat.findall(source):
        i,j,v=int(i),int(j),int(v)
        assert a[i][j] is None
        a[i][j]=v if mode=="pos" else -v-1
    assert all(isinstance(x,int) for row in a for x in row),(name,a)
    return a

def dot(A,B,i,j):
    return sum(A[i][k]*B[k][j] for k in range(len(A)))

def determinant(A):
    n=len(A);M=[[Fraction(t) for t in row] for row in A];result=Fraction(1)
    for j in range(n):
        pivot=next((k for k in range(j,n) if M[k][j]),None)
        assert pivot is not None, "singular block"
        if pivot!=j:
            M[j],M[pivot]=M[pivot],M[j]
            result=-result
        d=M[j][j];result*=d
        for k in range(j+1,n):
            scale=M[k][j]/d
            for l in range(j,n):
                M[k][l]-=scale*M[j][l]
    return result

PERMS=((0,1,2),(1,2,0),(2,0,1),(1,0,2),(2,1,0),(0,2,1))
CODE=(0,1,2)
REPS=((0,1,2),(1,2,0),(0,2,1),(0,0,0),(0,0,1),(0,0,2),(1,0,0))
SHAPES=("identityBlock","cycleBlock","transpositionBlock","constantBlock",
        "oneFixedBlock","twoFixedBlock","twoCycleBlock")
WORDS={"low":0,"mid":1,"high":2}

def inverse(p):
    return tuple(p.index(i) for i in CODE)

def multiply(p,q):
    return tuple(p[q[i]] for i in CODE)

def conjugate(p,f):
    ip=inverse(p)
    return tuple(p[f[ip[i]]] for i in CODE)

def parity(p):
    return (-1)**sum(p[i]>p[j] for i in CODE for j in CODE if i<j)

def rho(p):
    cols=[]
    for u in (0,1):
        x=[int(i==u)-int(i==2) for i in CODE]
        y=[x[inverse(p)[i]] for i in CODE]
        assert sum(y)==0
        cols.append(y[:2])
    return [[cols[j][i] for j in (0,1)] for i in (0,1)]


def verify_rational_solver_source_integrity():
    """Source/owner integrity, not a substitute for Agda elaboration."""
    rational=owner("PolynomialS3RationalBlockFieldIsomorphismExact")
    adapter=owner("PolynomialC3S3RationalCharacterAlgebraExact")
    assert "Data.Rational.Tactic.RingSolver" in rational
    # The reflected Ring.solve variable-list macro accepts ONLY bound
    # variables (Agda v2.4 Tactic.RingSolver.getVariableIndices), not
    # arbitrary applied terms such as (f Small.pair0).
    # Therefore the rational block proof owner uses universally
    # quantified scalar helper lemmas with the ZERO-argument solve-∀
    # macro and then specializes them to the actual field values.
    q27=owner("PolynomialS3RationalBlockFieldIsomorphismExact")
    scalar=re.findall(r"^([A-Za-z][A-Za-z0-9]*Scalar[A-Za-z0-9]+) = Ring[.]solve-∀$",q27,re.M)
    applied=re.findall(r"^([A-Za-z0-9]+) (?:Perm[.]\w+ )?f(?: g)? (?:Small|Big)[.]\w+ = ([A-Za-z][A-Za-z0-9]*Scalar[A-Za-z0-9]+) ",q27,re.M)
    assert len(scalar)==176,len(scalar)
    assert len(applied)==176,len(applied)
    assert len(set(scalar))==176
    assert set(scalar)==set(n for _,n in applied)
    assert not re.search(r"Ring[.]solve \(",q27)
    assert not re.search(r"= Ring[.]solve-∀[ \t]+",q27)
    for owner_name,needed in (
        ("PolynomialVietaRootSymmetryExact",19),
        ("PolynomialVandermondeDiscriminantExact",14),
    ):
        text=owner(owner_name)
        assert "Ring.solve-∀" not in text
        assert len(re.findall(r"Ring[.]solve \([^\n]* \u2237 \[\]\)",text))==needed
    for dim,n in ((2,2),(3,3),(6,6)):
        assert len(re.findall(r"^scalarField"+str(dim)+r" x[0-9]+",q27,re.M))==n
    print("PASS 176 true scalar solve-∀ lemmas with field instantiations;"
          "19 Vieta and 14 Vandermonde bound-variable solve macros")

    # O69: a previous generated type signature accidentally repeated the
    # function arrow after OrbitBlock27. Catch this at source level before
    # continuing to an Agda kernel check.
    assembly=owner("PolynomialS3TwentySevenOrbitBlockAssemblyExact")
    assert "caseBlockAction : Shape.TriPermutation → OrbitBlock27 → OrbitBlock27\n" in assembly
    assert "OrbitBlock27 Shape.TriPermutation" not in assembly

    # O70--O72: actual native 27-code field operator transport; all
    # declarations must have a source-written definition and TOE exports.
    native_fields=owner("PolynomialS3RationalTwentySevenFieldIsomorphismExact")
    native_receipts=(
        "plusNativeFields",
        "encodeNativeAdditiveAt",
        "decodeNativeAdditiveAt",
        "nativeSourceAction27",
        "nativeActionAgreesWithBlockAt",
        "decodeNativeIntertwinesAt",
        "nativeSourceActionIdentityAt",
        "nativeSourceActionCompositionAt",
        "nativeSourceActionAdditiveAt",
        "encodeNativeRespectsPointwiseAt",
        "decodedNativeEquivAt",
        "encodeNativeIntertwinesAt",
    )
    for name in native_receipts:
        assert len(re.findall(r"^"+name+r" :",native_fields,re.M))==1,name
        assert len(re.findall(r"^"+name+r" [^\n]* =",native_fields,re.M))==1,name
    assert "Atlas.blockActionPreservesNative" in native_fields
    assert "Atlas.blockCodeRoundTrip" in native_fields
    assert "sourceBlockActionAgreesWithNative" in native_fields

    # O73--O76: source-level audit of group-law owner reuse and finite
    # pointwise encoder transport. Count the actual seven constructor
    # cases (1+2+3+3+6+6+6=27 native coordinate observations).
    assert "TernaryEndomorphismS3ActionLawsExact as ActionLaws" in native_fields
    assert "TernaryPermutationS3LawsExact as S3" in native_fields
    assert "ActionLaws.inverseProduct p q" in native_fields
    assert "ActionLaws.conjugateComposition" in native_fields
    assert len(re.findall(r"^encodeNativeRespectsPointwiseAt f g equal ",native_fields,re.M))==7
    assert "encodeNativeRespectsPointwiseAt f g equal Atlas.identityBlock" in native_fields
    assert native_fields.count("equal (Atlas.blockToCode (Atlas.")==26
    for family,arity in (("cycleBlock",2),("transpositionBlock",3),
                         ("constantBlock",3),("oneFixedBlock",6),
                         ("twoFixedBlock",6),("twoCycleBlock",6)):
        assert len(re.findall(r"equal [(]Atlas[.]blockToCode [(]Atlas[.]"+
            family+r" (?:Small|Big)[.]\w+[)]",native_fields))==arity,family
    assert "encodeDecodeNativeCoordinateAt" in native_fields
    assert "decodedNativeEquivAt p f" in native_fields
    assert "decodeNativeIntertwinesAt p (encodeNative27 f) x" in native_fields
    for root in (
        "DASHI/EverythingTOESymmetryResolved369.agda",
        "DASHI/Unifier.agda","DASHI/Unified/Everything.agda"
    ):
        root_text=(ROOT/root).read_text(encoding="utf-8")
        assert "PolynomialS3RationalTwentySevenFieldIsomorphismExact" in root_text
        for name in native_receipts:
            assert name in root_text,(root,name)
        for name in ("polynomialDiscriminantQid", "galoisTheoryQid",
                     "specificPolynomialMonodromyQid", "qidCannotPayPolynomialProof"):
            assert name in root_text,(root,name)
    print("PASS repaired 27-code action type; native addition and S3 "
          "transport source coverage; three TOE exports (kernel pending)")


    # O77: reuse the upstream optional-identity/QID mechanism. A verified
    # label is a navigation coordinate, never a field-theory theorem.
    qid_owner=owner("PolynomialIbrahimParetoSnowballMaxCutExact")
    assert "SnowballExternalIdentityAvailabilityExact as Identity" in qid_owner
    for qid in ('"Q192487"','"Q92552"'):
        assert ("Identity.verified "+qid) in qid_owner,qid
    assert "specificPolynomialMonodromyQid" in qid_owner
    assert "Identity.unresolved" in qid_owner
    assert "qidCannotPayPolynomialProof = Identity.qidDoesNotPaySourceTruth" in qid_owner


    # O78--O79: explicit REUSE in the ORIGINAL orbit-sampling owner,
    # with rational instantiation only in the established Q27 owner.
    sampling=owner("PolynomialC3S3OrbitSamplingProjectionExact")
    sample_names=(
        "projectC3Any", "projectS3Any",
        "projectC3AnyIdempotent", "projectS3AnyIdempotent",
        "projectC3AnyInvariant", "projectS3AnyInvariant",
        "projectS3AnyFixesInvariant",
        "projectC3AnyAfterS3Any", "projectS3AnyAfterC3Any",
        "projectC3AnyMatchesOriginal", "projectS3AnyMatchesOriginal",
        "rotationPreservesAny", "projectC3AnyFixesInvariant",
        "projectC3AnyNaturality", "projectS3AnyNaturality",
    )
    for name in sample_names:
        assert len(re.findall(r"^"+name+r" :",sampling,re.M))==1,name
        assert (re.search(r"^"+name+r" [^\n]* =",sampling,re.M) or
                (name=="projectS3AnyFixesInvariant" and
                 "projectS3AnyFixesInvariant f invariant x\n  with" in sampling)),name
    assert "Data.Rational" not in sampling
    rational_sample_names=(
        "projectRationalC3", "projectRationalS3",
        "projectRationalC3IdempotentAt", "projectRationalS3IdempotentAt",
        "projectRationalC3InvariantAt", "projectRationalS3InvariantAt",
        "projectRationalS3FixesInvariantAt",
        "projectRationalS3AdditiveAt", "projectRationalC3AdditiveAt",
        "projectRationalC3AfterS3At", "projectRationalS3AfterC3At",
        "projectRationalS3NativeActionInvariantAt",
        "projectRationalC3FixesInvariantAt",
        "projectRationalC3NaturalityAt",
        "projectRationalS3NaturalityAt",
    )
    assert "PolynomialC3S3OrbitSamplingProjectionExact as Sampling" in native_fields
    for name in rational_sample_names:
        assert len(re.findall(r"^"+name+r" :",native_fields,re.M))==1,name
        assert re.search(r"^"+name+r"(?: [^\n]*)? =",native_fields,re.M),name
    for root in (
        "DASHI/EverythingTOESymmetryResolved369.agda",
        "DASHI/Unifier.agda", "DASHI/Unified/Everything.agda"
    ):
        root_text=(ROOT/root).read_text(encoding="utf-8")
        for name in rational_sample_names:
            assert name in root_text,(root,name)
    print("PASS generic original orbit retraction reused on rational Q27;"
          " 15 generic and 15 native declarations; 3 TOE roots")

    assert "MoonshineOrbifoldSectorProjectorExact" in adapter
    for name in ("positiveIntertwinesS3Parity",
                 "negativeIntertwinesS3Parity",
                 "s3OnRationalFieldFactorsThroughParity"):
        assert len(re.findall(r"^"+name+r" Perm[.]perm",adapter,re.M))==6,name
    for root in (
        "DASHI/EverythingTOESymmetryResolved369.agda",
        "DASHI/Unifier.agda","DASHI/Unified/Everything.agda"
    ):
        t=(ROOT/root).read_text(encoding="utf-8")
        assert "PolynomialC3S3RationalCharacterAlgebraExact" in t,root
        assert "PolynomialS3RationalBlockFieldIsomorphismExact" in t,root
    print("PASS rational ring-solver explicit argument lint; "
          "reuse of original rational C2 donor; 3 TOE root imports")


def verify_original_polynomial_video_m1_m10():
    """Source ownership + exact algebra; not a kernel or complex-loop receipt."""
    disc=owner("PolynomialVandermondeDiscriminantExact")
    spin=owner("PolynomialMonodromyTernaryQuaternionBridgeExact")
    # Directly consumed v2.4 rational-domain theorem, not a postulate.
    assert "Data.Rational.Properties as ℚProperties" in disc
    assert "ℚProperties.p*q≡0⇒p≡0∨q≡0" in disc
    assert "ℚProperties.+-inverseˡ" in disc
    for name in (
        "zeroDifferenceRational","rationalDomainLawWitness",
        "zeroDiscriminantImpliesCollisionRational",
        "collisionImpliesZeroDiscriminantRational",
        "zeroDiscriminantIffRootCollisionRational",
        "coefficientDiscriminantZeroIffRootCollisionRational",
    ):
        assert len(re.findall(r"^"+name+r" :",disc,re.M))==1,name
        assert re.search(r"^"+name+r"(?: [^\n]*)? =",disc,re.M),name
    for name in (
        "iTimesJIsK","jTimesIIsNegativeK",
        "jTimesKIsI","kTimesJIsNegativeI",
        "kTimesIIsJ","iTimesKIsNegativeJ",
        "positiveSwapOfQuaternionAxesImpossible",
        "positiveSwapIJImpossible","positiveSwapJKImpossible",
        "positiveSwapIKImpossible",
        "spinSignedSwapIJRightInverse","spinSignedSwapIJLeftInverse",
        "signedSwapIJMapsIToJ","signedSwapIJMapsJToI",
        "signedSwapIJMustNegateK","noFullPositiveQuaternionS3Action",
    ):
        assert len(re.findall(r"^"+name+r" :",spin,re.M))==1,name
    assert "FullPositiveQuaternionS3Action" in spin
    # Highest-alpha / Pareto / Ibrahim lane must CONSUME source proofs,
    # not promote boolean receipts or Wikidata concept identity to a proof.
    pareto=owner("PolynomialIbrahimParetoSnowballMaxCutExact")
    for name in ("originalVideoM1CoefficientDiscriminantReceipt",
                 "originalVideoM10OrientationReceipt"):
        assert len(re.findall(r"^"+name+r" :",pareto,re.M))==1,name
    assert "Discriminant.coefficientDiscriminantZeroIffRootCollisionRational" in pareto
    assert "Spin.noFullPositiveQuaternionS3Action" in pareto
    assert "identicalMonster3BObjectPaid = false" in pareto
    assert "PositiveQuaternionBraidGeneratorLift" in spin
    assert "noPositiveQuaternionBraidGeneratorLift" in spin
    assert "permutationImage g" in spin
    assert "originalVideoM2M10BraidQuaternionNoGoReceipt" in pareto
    assert "Spin.noPositiveQuaternionBraidGeneratorLift" in pareto

    assert "Q._*q_ spinSignedSwapIJ spinSignedSwapIJInverse" in spin
    assert "{!!}" not in disc+spin
    for root in (
        "DASHI/EverythingTOESymmetryResolved369.agda",
        "DASHI/Unifier.agda","DASHI/Unified/Everything.agda"
    ):
        t=(ROOT/root).read_text(encoding="utf-8")
        for name in ("zeroDiscriminantIffRootCollisionRational",
                     "coefficientDiscriminantZeroIffRootCollisionRational",
                     "noFullPositiveQuaternionS3Action",
                     "signedSwapIJMustNegateK",
                     "originalVideoM1CoefficientDiscriminantReceipt",
                     "originalVideoM10OrientationReceipt",
                     "noPositiveQuaternionBraidGeneratorLift",
                     "originalVideoM2M10BraidQuaternionNoGoReceipt"):
            assert name in t,(root,name)

    # Original rational Vieta/discriminant target, finite scalar domain:
    # a,b,c ∈ {-2,-1,0,1,2}. This tests 125 triples and every S3 action.
    vals=tuple(map(Fraction,(-2,-1,0,1,2)))
    perms=((0,1,2),(1,2,0),(2,0,1),
           (1,0,2),(2,1,0),(0,2,1))
    count=0
    for roots in product(vals,repeat=3):
        a,b,c=roots
        s1=a+b+c;s2=a*b+a*c+b*c;s3=a*b*c
        discr=(a-b)**2*(a-c)**2*(b-c)**2
        coef_discr=s1*s1*s2*s2-4*s2**3-4*s1**3*s3-27*s3*s3+18*s1*s2*s3
        assert discr==coef_discr
        assert (discr==0)==(a==b or a==c or b==c)
        for perm in perms:
            x,y,z=(roots[j] for j in perm)
            assert (x-y)*(x-z)*(y-z) in (
                (a-b)*(a-c)*(b-c),-((a-b)*(a-c)*(b-c)))
            assert (x-y)**2*(x-z)**2*(y-z)**2==discr
        count+=1
    assert count==125

    def mul(a,b):
        a0,a1,a2,a3=a;b0,b1,b2,b3=b
        return (a0*b0-a1*b1-a2*b2-a3*b3,
                a0*b1+a1*b0+a2*b3-a3*b2,
                a0*b2-a1*b3+a2*b0+a3*b1,
                a0*b3+a1*b2-a2*b1+a3*b0)
    zero=Fraction(0);one=Fraction(1);half=Fraction(1,2)
    I=(zero,one,zero,zero);J=(zero,zero,one,zero)
    K=(zero,zero,zero,one);One=(one,zero,zero,zero)
    neg=lambda x: tuple(-v for v in x)
    assert mul(I,J)==K and mul(J,I)==neg(K)
    assert mul(J,K)==I and mul(K,J)==neg(I)
    assert mul(K,I)==J and mul(I,K)==neg(J)
    q=(zero,one,one,zero)
    qi=(zero,-half,-half,zero)
    assert mul(q,qi)==One and mul(qi,q)==One
    assert mul(mul(q,I),qi)==J
    assert mul(mul(q,J),qi)==I
    assert mul(mul(q,K),qi)==neg(K)
    print("PASS original M1: 125 exact rational triples × 6 root"
          " permutations; Δ=0 iff collision, coefficient formula")
    print("PASS original M10: all six quaternion basis products,"
          " signed odd swap, exact two-sided inverse; kernel pending")


def test():
    verify_rational_solver_source_integrity()
    verify_original_polynomial_video_m1_m10()
    reg,small,native,assembly=map(owner,NAMES)
    B6=integer_matrices(reg,"basis6",6,"slot")
    C6=integer_matrices(reg,"scaledInverse6",6,"slot")
    B3=integer_matrices(small,"basis3",3,"axis")
    C3=integer_matrices(small,"scaledInverse3",3,"axis")
    B2=integer_matrices(small,"basis2",2,"pair")
    C2=integer_matrices(small,"scaledInverse2",2,"pair")
    for B,C,factor in ((B2,C2,2),(B3,C3,3),(B6,C6,54)):
        for i,j in product(range(len(B)),repeat=2):
            target=factor*int(i==j)
            assert dot(B,C,i,j)==target
            assert dot(C,B,i,j)==target
    assert [determinant(M) for M in (B2,B3,B6)]==[-2,3,-54]

    for p in PERMS:
        T=[[0]*6 for _ in range(6)]
        T[0][0]=1
        T[1][1]=parity(p)
        R=rho(p)
        for r,c in product(range(2),repeat=2):
            T[2+r][2+c]=R[r][c]
            T[4+r][4+c]=R[r][c]
        for i,j in product(range(6),repeat=2):
            gi=PERMS[i]
            pi=inverse(p)
            left=PERMS.index(multiply(pi,gi))
            assert B6[left][j]==dot(B6,T,i,j),(p,i,j)
    for p in PERMS:
        M2=[[1,0],[0,parity(p)]]
        for i,j in product(range(2),repeat=2):
            pi=i if parity(p)==1 else 1-i
            assert B2[pi][j]==dot(B2,M2,i,j)
        M3=[[1,0,0],[0,rho(p)[0][0],rho(p)[0][1]],
            [0,rho(p)[1][0],rho(p)[1][1]]]
        for i,j in product(range(3),repeat=2):
            pi=inverse(p)[i]
            assert B3[pi][j]==dot(B3,M3,i,j)

    # Actual 27 native-code label proof, not a numeric-orbit count.
    labels={}
    rx=re.compile(
        r"^codeToBlock \(Base\.tri-(low|mid|high) , "
        r"\(Base\.tri-(low|mid|high) , Base\.tri-(low|mid|high)\)\)"
        r" = (.+)$",re.M)
    for a,b,c,part in rx.findall(assembly):
        code=(WORDS[a],WORDS[b],WORDS[c])
        assert code not in labels
        labels[code]=part
    assert len(labels)==27
    canonical={}
    canonical[REPS[0]]="identityBlock"
    for i,cy in enumerate(((1,2,0),(2,0,1))):
        canonical[cy]=f"cycleBlock Small.pair{i}"
    for title,code_list in (
        ("transpositionBlock",((0,2,1),(2,1,0),(1,0,2))),
        ("constantBlock",((0,0,0),(1,1,1),(2,2,2)))):
        for i,c in enumerate(code_list):
            canonical[c]=f"{title} Small.axis{i}"
    for title,rep in zip(SHAPES[4:],REPS[4:]):
        for i,p in enumerate(PERMS):
            canonical[conjugate(p,rep)]=f"{title} Block.slot{i}"
    assert labels==canonical

    # Sampling projector is a choice of ORIGINAL orbit representative;
    # it is not group averaging, nor is its carrier an abstract polynomial.
    def shape(c):
        return canonical[c].split()[0]
    rep_by_shape=dict(zip(SHAPES,REPS))
    def projector(f,c):
        return f(rep_by_shape[shape(c)])
    f=lambda c: int(c==REPS[4])
    g=lambda c: c[0]*9+c[1]*3+c[2]
    for c in canonical:
        assert projector(lambda x: projector(f,x),c)==projector(f,c)
        assert projector(lambda x: projector(g,x),c)==projector(g,c)
        assert projector(lambda x: f(x)+g(x),c)==(
            projector(f,c)+projector(g,c))
        for p in PERMS:
            assert projector(f,conjugate(p,c))==projector(f,c)
    assert projector(f,REPS[4])==1
    assert sum(f(conjugate(p,REPS[4])) for p in PERMS)==1
    assert Fraction(sum(f(conjugate(p,REPS[4]))
                        for p in PERMS),6)==Fraction(1,6)
    print("PASS 27 native S3 sampling idempotence, invariance, additivity;"
          " non-Reynolds fixture sample=1 vs mean=1/6")

    for p in PERMS:
        for c in canonical:
            observed=labels[conjugate(p,c)]
            part=labels[c]
            if part=="identityBlock":
                expected=part
            elif part.startswith("cycleBlock"):
                index=int(part[-1])
                expected=f"cycleBlock Small.pair{index if parity(p)==1 else 1-index}"
            elif part.startswith(("transpositionBlock","constantBlock")):
                index=int(part[-1])
                expected=part[:-1]+str(p[index])
            else:
                index=int(part[-1])
                next_index=PERMS.index(multiply(p,PERMS[index]))
                expected=part[:-1]+str(next_index)
            assert observed==expected,(p,c,observed,expected)

    # The same original six S3 group elements act on ALL 27 native codes.
    # This is a direct finite audit of the inverse-pullback group law that
    # the source-written nativeSourceActionCompositionAt imports.
    s3_native_cases=0
    for p,q in product(PERMS,repeat=2):
        assert inverse(multiply(p,q))==multiply(inverse(q),inverse(p))
        for c in product(CODE,repeat=3):
            assert conjugate(multiply(p,q),c)==conjugate(p,conjugate(q,c))
            assert conjugate(inverse(multiply(p,q)),c)==(
                conjugate(inverse(q),conjugate(inverse(p),c)))
            s3_native_cases+=1
    assert s3_native_cases==972
    print("PASS 972 original-code S3 composition / inverse-pullback cases")

    det_product=determinant([[1]])
    for M in (B2,B3,B3,B6,B6,B6):
        det_product*=determinant(M)
    assert det_product!=0
    assert abs(det_product)==2834352
    assert len(re.findall(r"^regularBlockIntertwines Perm\.perm\w+ slot\d slot\d = refl$",reg,re.M))==216
    assert len(re.findall(r"^nativeBlockActionByShape Shape\.perm\w+",assembly,re.M))==162
    assert len(re.findall(r"^regularCodeFree (?:rank2OneFixed|rank2TwoFixed|rank2TwoCycle) Block[.]slot",native,re.M))==108
    print("PASS exact 2x2/3x3/6x6 scaled integer inverses")
    print("PASS rational determinants: 1, -2, 3, 3, ±54, ±54, ±54")
    print("PASS 216 regular and 24+54 small-block intertwining cases")
    print("PASS 27 native code labels and 162 original S3 actions")
    print(f"PASS full Q^27 block basis, absolute determinant {abs(det_product)}")
    print("NO CLAIM: Agda kernel acceptance; generic Galois/Monster same-object theorem")

if __name__=="__main__":
    test()
