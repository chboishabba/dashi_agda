"""Conditional C4 constituent discriminator. Input traces are prior session
candidate values, NOT an authenticated CTblLib or same-word fusion receipt."""
import sympy as s
def run():
    rows=[]
    for a in range(13):
        t=2*a-12
        x=s.I*t
        y=s.expand((x*x-12)/2)
        if s.expand(x+y)==-6:
            rows.append((a,12-a,a*(12-a),a*(a+1)//2+(12-a)*(13-a)//2))
    assert rows==[(6,6,36,42)]
    return rows
if __name__=='__main__':
    print(run())
