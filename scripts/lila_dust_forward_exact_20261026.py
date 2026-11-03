#!/usr/bin/env python3
"""Exact finite forward-only Dust credit applied to a LILA-style semantic objective.
Toy consumer, not a transformer or deployed LILA training run. stdlib only."""
from fractions import Fraction as F
from itertools import product
import json

TOKENS = [(F(s), F(n), F(s)) for s in (-1, 1) for n in (-1, 1)]
HOLDOUT = [(F(s), F(n), F(s)) for s in (-1, 1) for n in (-2, 2)]
SIGMA = F(1, 8)
ETA = F(1, 8)

def activation(w, t):
    return w[0]*t[0] + w[1]*t[1]

def token_loss(h, t):
    return (h-t[2])**2 / F(2)

def risk(w, examples):
    return sum(token_loss(activation(w,t), t) for t in examples) / len(examples)

def dust_forward_step(w):
    count = len(TOKENS)
    noise = list(product((F(-1), F(1)), repeat=count))
    noisy = [[token_loss(activation(w,t) + SIGMA*a[i],t)
              for i,t in enumerate(TOKENS)] for a in noise]
    means = [sum(row[i] for row in noisy)/len(noise) for i in range(count)]
    centered = [[means[i]-row[i] for i in range(count)] for row in noisy]
    # Identity future-weight matrix: immediate per-token loss contribution.
    credit = [-sum(centered[k][i]*noise[k][i] for k in range(len(noise))) /
              (len(noise)*SIGMA) for i in range(count)]
    gradient = [sum(credit[i]*TOKENS[i][j] for i in range(count))/count
                for j in range(2)]
    updated = tuple(w[j]-ETA*gradient[j] for j in range(2))
    return updated, gradient, credit, len(noise)

def main():
    w = (F(0), F(0))
    updated, gradient, credit, draws = dust_forward_step(w)
    assert draws == 16
    assert gradient == [F(-1), F(0)]
    assert updated == (F(1,8), F(0))
    assert credit == [activation(w,t)-t[2] for t in TOKENS]
    assert risk(updated,TOKENS) < risk(w,TOKENS)
    assert risk(updated,HOLDOUT) < risk(w,HOLDOUT)
    assert all(activation(updated,(F(s),F(-1),F(s))) ==
               activation(updated,(F(s),F(1),F(s))) for s in (-1,1))
    receipt = {
        "source": "Dust population centering + activation credit + outer update",
        "task": "finite paired semantic/nuisance toy objective",
        "noise_draws": draws, "sigma": str(SIGMA), "learning_rate": str(ETA),
        "gradient": list(map(str,gradient)),
        "parameters_after": list(map(str,updated)),
        "train_before": str(risk(w,TOKENS)),
        "train_after": str(risk(updated,TOKENS)),
        "heldout_before": str(risk(w,HOLDOUT)),
        "heldout_after": str(risk(updated,HOLDOUT)),
        "uses_backprop": False,
        "real_LILA_training": False,
        "original_Dust_GPU_reproduction": False
    }
    print(json.dumps(receipt,indent=2))

if __name__ == "__main__":
    main()
