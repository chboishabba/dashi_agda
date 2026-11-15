#!/usr/bin/env python3
"""Source-derived *post-hoc* IF-null recurrence, with conservative spacing nulls.
Original ReelAudio 105.8s, source SHA in the accompanying research report.
These 7 minima are from a 500Hz complex baseband reconstruction, NOT
independent physical electrical source-switch timestamps.
"""
import numpy as np
TIMES=np.array([39.546,41.738,43.596,47.064,51.316,53.,55.102])
F=np.linspace(1/2.5,1/1.5,400)
def fit(events):
    score=np.abs(np.exp(2j*np.pi*events[:,None]*F[None,:]).mean(axis=0))
    i=int(np.argmax(score))
    return 1/F[i],score[i]
def sample_null(gap,n=4000,seed=32):
    rng=np.random.default_rng(seed);t=TIMES
    d=t[-1]-t[0]-(len(t)-1)*gap
    for _ in range(n):
        if gap==0:events=np.sort(rng.uniform(t[0],t[-1],len(t)))
        else:events=t[0]+np.r_[0,np.cumsum(gap+d*rng.dirichlet(np.ones(len(t)-1)))]
        yield fit(events)[1]
def main():
    T,score=fit(TIMES)
    assert 1.8<T<2.1 and score>.8
    print('candidate',T,'seconds; beat',1/T,'Hz; phase concentration',score)
    for gap in (0,1.0,1.3,1.5,1.6):
        x=np.fromiter(sample_null(gap),float)
        p=(1+sum(x>=score))/(1+len(x))
        print('min-spacing-null',gap,'post-hoc p',p)
    print('PASS exploratory inverse recurrence; not a hardware clock or source test')
if __name__=='__main__': main()
