import sympy as s
u=s.symbols('u',positive=True); f=s.Function('f')(u); h=s.symbols('h',positive=True); q=s.symbols('q'); count=0
p=[s.Rational(2,5)*(u*u*s.diff(f,u,3)+2*u*s.diff(f,u,2)-2*s.diff(f,u)),s.Rational(4,7)*(u**4*s.diff(f,u,3)-3*u**3*s.diff(f,u,2)+3*u**2*s.diff(f,u)),(u**6*s.diff(f,u,3)-12*u**5*s.diff(f,u,2)+75*u**4*s.diff(f,u)-315*u**3*f)/35]
forms=[s.Rational(2,5)*(s.diff(f,u,4)+4*s.diff(f,u,3)/u),s.Rational(4,7)*(s.diff(f,u,4)+s.diff(f,u,3)/u-6*s.diff(f,u,2)/u**2+6*s.diff(f,u)/u**3), (s.diff(f,u,4)-6*s.diff(f,u,3)/u+15*s.diff(f,u,2)/u**2-15*s.diff(f,u)/u**3)/35]
for i,l in enumerate((0,2,4)):
 assert s.expand(s.diff(p[i],u)+(27*u*u*f if i==2 else 0)-u**(2+l)*forms[i])==0;count+=1
w=s.Matrix([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,-(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6]); dw=s.Matrix([-(3*q*q-6*q+2)/6,(3*q*q-4*q-1)/2,(-3*q*q+2*q+2)/2,(3*q*q-1)/6]); d2=s.Matrix([1-q,3*q-2,1-3*q,q]);
assert all(s.expand(x)==0 for x in w.diff(q)-dw);assert all(s.expand(x)==0 for x in dw.diff(q)-d2);count+=2
for k in range(4):
 assert s.expand(w.dot(s.Matrix([j**k for j in (-1,0,1,2)]))-q**k)==0;count+=1
# cell-average vs nodal interpretation at radial origin
for d in (3,7,11):
 avg0=d*h*h/(4*(d+2));avg1=s.Rational(d,d+2)*((3*h/2)**(d+2)-(h/2)**(d+2))/((3*h/2)**d-(h/2)**d)
 nodal=2*d*(h*h)/h**2; cell=s.simplify(2*d*(avg1-avg0)/h**2)
 assert nodal==2*d;assert cell!=2*d;count+=2
 print('d',d,'origin cell-average polynomial residual',s.simplify(cell-2*d),'relative',s.simplify(cell/(2*d)-1))
print(count,'exact checks PASS')
