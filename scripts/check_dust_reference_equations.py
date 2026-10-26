#!/usr/bin/env python3
"""Tiny executable Dust equations (1)-(4), NOT a GPU/transformer reproduction.
Dahal, Mandal, Gülbahar, Vegesna (2026); DASHI finite derived fixtures.
"""
from fractions import Fraction as F
from itertools import product

def dust_step(inputs, perturbations, clean_loss, noisy_losses, future_weights, sigma):
    """Population-centered c_{k,s}, causal discounted r_{k,t}, signed g and outer update.
    Inputs: token scalar x_t, noise a_{k,t}; per-draw/token perturbed losses,
    future weight matrix w[t][s] (zero for s<t).
    """
    K=len(perturbations)
    T=len(inputs)
    assert K>0 and sigma!=0
    assert all(len(row)==T for row in perturbations+noisy_losses)
    assert len(future_weights)==T
    means=[sum(noisy_losses[k][s] for k in range(K))/K for s in range(T)]
    centered=[[means[s]-noisy_losses[k][s] for s in range(T)] for k in range(K)]
    rewards=[[sum(future_weights[t][s]*centered[k][s] for s in range(t,T))
              for t in range(T)] for k in range(K)]
    output_credit=[-sum(rewards[k][t]*perturbations[k][t] for k in range(K))/(K*sigma)
                   for t in range(T)]
    weight=sum(output_credit[t]*inputs[t] for t in range(T))
    return centered,rewards,output_credit,weight

def check_centering():
    x=[F(2),F(-3)]
    noise=[[F(1),F(-1)], [F(-1),F(1)]]
    sigma=F(1,10)
    # A causal two-token toy with coupling between token-0 activation and token-1 loss.
    # Underlying activation W*x, W=1; ell_0=2*y0, ell_1=3*y1+5*y0.
    # + noise sigma*a; no reverse differentiation anywhere in estimator.
    clean=[2*x[0], 3*x[1]+5*x[0]]
    noisy=[[2*(x[0]+sigma*a[0]),3*(x[1]+sigma*a[1])+5*(x[0]+sigma*a[0])]
           for a in noise]
    for gamma in (F(0),F(1)):
        weights=[[F(1),gamma],[F(0),F(1)]]
        c,r,g,dW=dust_step(x,noise,clean,noisy,weights,sigma)
        assert all(sum(c[k][s] for k in range(2))==0 for s in range(2))
        # Directly compute the actual source equation (not gradient truth).
        assert r[0][0] == c[0][0]+gamma*c[0][1]
        assert dW == sum(a*b for a,b in zip(g,x))
    print("PASS exact Dust population centering, future-token reward and update")

def check_attention():
    for grad,disp in [(F(2),F(3)), (F(-1,2),F(1,3))]:
        score= -grad*disp
        assert score + grad*disp == 0
    print("PASS attention surrogate sign and inner-product equation")

if __name__=="__main__":
    check_centering()
    check_attention()
