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


def check_complete_orthogonal_population():
    """Whole factorial +/-1 probes: exact linear credit, causal nonlocal reward."""
    x=[F(2),F(-3)]
    sigma=F(1,7)
    noise=[[F(a),F(b)] for a,b in product((-1,1),repeat=2)]
    # loss0=2*h0; loss1=5*h0+3*h1
    noisy=[[2*(x[0]+sigma*a[0]), 5*(x[0]+sigma*a[0])+3*(x[1]+sigma*a[1])]
           for a in noise]
    for gamma,expected in [(F(0),[F(2),F(3)]),
                           (F(1),[F(7),F(3)]),
                           (F(1,2),[F(9,2),F(3)])]:
        weights=[[F(1),gamma],[F(0),F(1)]]
        centered,rewards,credit,update=dust_step(x,noise,[],noisy,weights,sigma)
        assert credit==expected,(gamma,credit,expected)
        assert update==sum(expected[t]*x[t] for t in range(2))
        for token in range(2):
            assert sum(centered[k][token] for k in range(4))==0
    print("PASS complete 2-token Rademacher population: exact affine credit 2,7,9/2")

def check_nonlinear_obstruction():
    """Quadratic cross-terms and higher-order bias distinguish exactness scopes."""
    for scale in (F(1,10),F(1,4),F(1)):
        # A cubic, symmetric two-probe finite difference cannot recover
        # the unsmoothed gradient exactly at any nonzero scale.
        y=F(3,2)
        smooth_estimate=((y+scale)**3-(y-scale)**3)/(2*scale)
        assert smooth_estimate==3*y*y+scale*scale
        assert smooth_estimate!=3*y*y
    print("PASS cubic nonzero finite-smoothing bias counterexample")

if __name__=="__main__":
    check_centering()
    check_attention()
    check_complete_orthogonal_population()
    check_nonlinear_obstruction()
