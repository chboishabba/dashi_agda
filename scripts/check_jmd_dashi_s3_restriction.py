import sympy as s

def check():
    T=s.Matrix([[1,1,2],[1,-1,0],[1,1,-1]])
    x,y,z=s.symbols('x y z')
    v=s.Matrix([x,y,z])
    assert T.inv()*v==s.Matrix([x/6+y/2+z/3,x/6-y/2+z/3,x/3-z/3])
    m=T.inv()*s.Matrix([196884,4372,0])
    assert m==s.Matrix([35000,30628,65628])
    reg=s.Matrix([1,1,2]); perm=s.Matrix([1,0,1])
    k=min(int(m[i]//reg[i]) for i in range(3))
    assert k==30628 and m-k*reg==4372*perm
    assert T*m==s.Matrix([196884,4372,0])
    assert T*reg==s.Matrix([6,0,0]) and T*perm==s.Matrix([3,1,0])
    assert 6*k+3*4372==196884
    assert m-(k+1)*reg==s.Matrix([4371,-1,4370])
    print('PASS: exact character inversion, maximum regular core, ternary residual, maximality negative control')
if __name__=='__main__': check()
