#!/usr/bin/env python3
"""Nonlinear receiver frequency conversion and noise bookkeeping.
Synthetic mechanism test; no empirically established gravito-EM coupling.
Filsinger source/driver signed work remains separate and required.
"""
import sympy as s

def main():
    signal,nin,nread,npump,nside,eta,G=s.symbols(
        "signal nin nread npump nside eta G",positive=True)
    gls=G**2*signal**2/(G**2*nin+nread)
    assert s.simplify(s.limit(gls,G,s.oo)-signal**2/nin)==0
    # A driven upconverter may translate the cardiac sideband before
    # readout 1/f; no such benefit is assumed for the input field itself.
    converted=eta**2*signal**2/(eta**2*nin+nside+npump)
    assert s.simplify(converted-signal**2/(nin+(nside+npump)/eta**2))==0
    baseline=signal**2/(nin+nread)
    improvement2=s.factor(converted/baseline)
    assert s.simplify(improvement2-
        (nin+nread)/(nin+(nside+npump)/eta**2))==0
    q=s.symbols("q",positive=True)
    assert s.simplify(s.solve(s.Eq(improvement2,q**2),nread)[0]-
      (q**2*(nin+(nside+npump)/eta**2)-nin))==0
    # Ideal single-pole parametric gain-bandwidth tradeoff:
    gamma,k=s.symbols('gamma k',positive=True)
    linewidth=gamma-k
    ideal_gain=gamma/linewidth
    assert s.simplify(ideal_gain*linewidth-gamma)==0
    assert s.simplify(linewidth.subs(k,gamma*(1-s.Rational(1,1076)))/gamma-s.Rational(1,1076))==0
    target=1076
    assert target**2==1157776
    assert 1/s.sqrt(s.Rational(1,1_000_000))<target
    print("PASS exact input-noise ceiling and upconversion channel")
    print("1076x necessary baseline input-noise fraction <",s.Rational(1,target**2))
    print("NO measured 1/f, quantum transduction, gravito-EM or pump energy")
if __name__=="__main__":main()
