"""Linear exact vacuum coordinate change; original ambient carrier unchanged."""
from monster3b_conway_exact_crt import linear_combination, require
from monster3b_char0_orbit_weld import K,Z,col,eye


def coords(v,piv):
    return [(K.convert(int(v.a[j]))+Z*K.convert(int(v.b[j])))/K.convert(v.d) for j in piv]


class OrdinaryCodec:
    def __init__(self,frame,pivots,minor_inverse,ordinary,reverse,basis,dimension):
        self.frame,self.pivots,self.minor_inverse=frame,pivots,minor_inverse
        self.ordinary,self.reverse,self.basis,self.dimension=ordinary,reverse,basis,dimension
        for s in (1,2):
            n=len(pivots[s]);I=eye(n)
            require(ordinary[s]*reverse[s]==I and reverse[s]*ordinary[s]==I,"ordinary maps are not inverses")
    def combine(self,s,x):
        nz=[(c,i) for i,c in enumerate(x) if c]
        return linear_combination((c for c,i in nz),(self.basis(s,i) for c,i in nz),self.dimension)
    def encode_vacuum(self,s,u):
        c=self.minor_inverse[s]*col(coords(u,self.pivots[s]))
        require(self.combine(s,c.transpose().to_list()[0])==u,"exact vacuum closure discrepancy")
        return (self.ordinary[s]*c).transpose().to_list()[0]
    def decode_vacuum(self,s,x):
        c=self.reverse[s]*col(x)
        return self.combine(s,c.transpose().to_list()[0])
    def encode(self,v,s,x):
        return self.encode_vacuum(s,self.frame.recover_weight(v,s,x))
    def decode(self,s,x,c):
        return self.frame.translate(self.decode_vacuum(s,c),x)
