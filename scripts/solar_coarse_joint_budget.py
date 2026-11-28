"""Coarse endpoint-first source/recovery/conversion budget; exact rational.
Dynamic source topology follows nonlinear_retarded_source_port.DynamicUpstream.
No measured actuator, source, or frequency conversion is inferred.
"""
import sympy as S


def recovery_inverse(work, receiver, passive, overhead, gain):
    """Field modulation work positive into field; separate gross tranches."""
    w=list(map(S.Rational,work)); y,p,c,g=map(S.Rational,(receiver,passive,overhead,gain))
    assert min(y,p,c)>=0 and g>0
    buy=sum(max(0,x) for x in w); sell=sum(max(0,-x) for x in w)
    need=p+c+g+buy-y
    return dict(buy=buy,sell=sell,required_recovery=need/sell if sell else None,
                feasible_ideal=need<=sell,margin_ideal=sell-need)


def buffer_cycle(work,eta,export):
    """Ideal recoverable-work buffer; no actuator-force realization implied.
    Export is a separately metered nonnegative scheduled draw.
    Reverse minimum initial charge and capacity, full buffer restoration.
    """
    w=list(map(S.Rational,work)); e=list(map(S.Rational,export));eta=S.Rational(eta)
    assert len(w)==len(e) and w and 0<=eta<=1 and min(e)>=0
    dx=[eta*max(0,-a)-max(0,a)-b for a,b in zip(w,e)]
    prefix=[S.Integer(0)]
    for x in dx:prefix.append(prefix[-1]+x)
    if prefix[-1]!=0:return dict(restored=False,residual=prefix[-1])
    start=-min(prefix);state=[start+x for x in prefix]
    return dict(restored=True,initial=start,capacity=max(state),state=state,
                conversion_loss=(1-eta)*sum(max(0,-a) for a in w))


def source_cycle(channel,voltage,feed,outer,load,cs,cr,h):
    """Exact periodic midpoint of donor two-capacitor topology, fixed channel
    resistance schedule. All storage restored; no ionization actuator claim.
    """
    ch=list(map(S.Rational,channel));v,g,r,L,Cs,Cr,h=map(S.Rational,(voltage,feed,outer,load,cs,cr,h))
    assert ch and min(ch)>0 and min(g,r,L,Cs,Cr,h)>0
    G=S.diag(Cs,Cr);I=S.eye(2);maps=[];M=I;b=S.zeros(2,1)
    for rc in ch:
        k=1/(r+rc);A=G.inv()*S.Matrix([[-g-k,k],[k,-k-L]]);f=G.inv()*S.Matrix([g*v,0]);D=(I-h*A/2).inv();T=D*(I+h*A/2);u=D*h*f
        maps.append((T,u));M=T*M;b=T*b+u
    x=(I-M).inv()*b;initial=x;W={k:S.Integer(0) for k in ('natural','feed','outer','channel','receiver')}
    for rc,(T,u) in zip(ch,maps):
        y=T*x+u;vs,vr=(x+y)/2;i=(vs-vr)/(r+rc);j=g*(v-vs)
        step=dict(natural=h*v*j,feed=h*j*j/g,outer=h*r*i*i,channel=h*rc*i*i,receiver=h*L*vr*vr)
        assert ((y.T*G*y-x.T*G*x)[0]/2)==step['natural']-sum(step[k] for k in ('feed','outer','channel','receiver'))
        for k in W:W[k]+=step[k]
        x=y
    assert x==initial and W['natural']==sum(W[k] for k in ('feed','outer','channel','receiver'))
    return dict(work=W,initial=initial,monodromy=M,restored=True)


def dc_ceiling(voltage,feed,outer,channel_min,load,duration):
    """All periodic resistance schedules with fixed load and constant external V.
    Jensen on feed and series currents; periodic continuity equates means.
    Bound receiver work via total balance, not an assertion of attainability.
    """
    v,g,r,c,L,T=map(S.Rational,(voltage,feed,outer,channel_min,load,duration))
    assert min(g,r,c,L,T)>0
    R=1/g+r+c
    return T*v*v/(4*R)


def static_receiver(voltage,feed,outer,channel_min,load,duration):
    v,g,r,c,L,T=map(S.Rational,(voltage,feed,outer,channel_min,load,duration))
    assert min(g,r,c,L,T)>0
    return T*L*(v/(1+L*(1/g+r+c)))**2


def triad_inverse(required_lf,fast,slow,downstream):
    """Conditional single equal-action decay, not a general conversion bound."""
    y,f,s,e=map(S.Rational,(required_lf,fast,slow,downstream))
    assert y>=0 and f>s>0 and 0<e<=1
    return y*f/(s*e)


def run():
    # Exact prior receipt numbers, treated as supplied premises, not replay.
    P=S.Rational(27169920,1573877233);Y=S.Rational(116989943269599360,10151447527333778689);R=S.Rational(1153028492992310400,10151447527333778689)
    a=recovery_inverse([-R],Y,P,0,S.Rational(1,1000));eta=a['required_recovery'];assert 0<eta<1
    buf=buffer_cycle([-R,0],eta,[0,eta*R]);assert buf['restored'] and buf['capacity']==eta*R
    assert not buffer_cycle([-R,0],eta,[0,0])['restored']
    args=(1,1,1,1,1,1,S.Rational(1,2)) # V,g,Router,Gload,Cs,Cr,h
    passive=source_cycle([1,1],*args);active=source_cycle([1,2],*args)
    p=static_receiver(1,1,1,1,1,1);cap=dc_ceiling(1,1,1,1,1,1)
    assert passive['work']['receiver']==p==S.Rational(1,16)
    assert active['work']['receiver']<p<cap==S.Rational(1,12)
    assert triad_inverse(S.Rational(1,100),1000,1,1)==10
    print('PASS', 'recovery_for_gain',eta,'buffer_capacity',buf['capacity'],'passive',p,'active',active['work']['receiver'],'all_schedule_cap',cap,'unresolved_headroom',cap-p)
if __name__=='__main__':run()
