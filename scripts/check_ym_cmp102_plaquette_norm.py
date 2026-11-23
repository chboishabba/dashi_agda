import sympy as s
a,b,c,d=s.symbols('a b c d',real=True)
M=s.Matrix([[a-1+s.I*b,c+s.I*d],[-c+s.I*d,a-1-s.I*b]])
assert s.simplify(M.conjugate().T*M-((a-1)**2+b*b+c*c+d*d)*s.eye(2))==s.zeros(2)
assert s.expand(((a-1)**2+b*b+c*c+d*d)-2*(1-a))==a*a+b*b+c*c+d*d-1
print('PASS operator norm squared = chord squared; normalized Wilson deficit identity')
