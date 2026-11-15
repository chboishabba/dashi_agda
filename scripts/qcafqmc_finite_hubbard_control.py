#!/usr/bin/env python3
"""Finite Hubbard control for arXiv:2611.08129 equations (16)-(18).

Synthetic labels only. NOT the IonQ dataset, its transformer, or phaseless AFQMC.
Source-first attribution: Provazza, Knitter et al., arXiv:2611.08129.
NumPy required; deterministic seed.
"""
import json
import numpy as np

rng = np.random.default_rng(261108129)
basis = [(a,b) for a in range(2) for b in range(2)]
H = np.zeros((4,4))
for k,(a,b) in enumerate(basis):
    H[k,k] = 4.0 * (a==b)
    H[basis.index((1-a,b)),k] -= 1.0
    H[basis.index((a,1-b)),k] -= 1.0
energies,vectors = np.linalg.eigh(H)
psi = vectors[:,0].astype(complex)
psi *= np.exp(-1j*np.angle(psi[np.argmax(abs(psi))]))

def walker():
    a = rng.normal(size=2)+1j*rng.normal(size=2)
    b = rng.normal(size=2)+1j*rng.normal(size=2)
    return np.outer(a/np.linalg.norm(a),b/np.linalg.norm(b)).reshape(-1)

def samples(w,n,burn=600,thin=3):
    weights = abs(np.conj(psi)*w)
    weights /= sum(weights)
    pos = int(np.argmax(weights))
    result = []
    for j in range(burn+n*thin):
        new = int(rng.integers(3))
        if new >= pos: new += 1
        if rng.random() < min(1.0,weights[new]/weights[pos]):
            pos = new
        if j>=burn and (j-burn)%thin==0:
            result.append(pos)
    return np.asarray(result,dtype=int)

def ratio(w,v,indices):
    z = np.conj(psi)*w
    phase = z[indices]/abs(z[indices])
    return np.sum((v[indices]/w[indices])*phase)/np.sum(phase)

queries = [(walker(),walker()) for _ in range(6)]
errors = []
for w,v in queries:
    exact = np.vdot(psi,v)/np.vdot(psi,w)
    low = abs(ratio(w,v,samples(w,1000))-exact)
    high = abs(ratio(w,v,samples(w,16000))-exact)
    errors.append((float(low),float(high)))

training = np.stack([walker() for _ in range(128)])
attenuation = 0.72
labels = attenuation * (training.conj()@psi)
noise = np.random.default_rng(261108130)
labels += .003*(noise.normal(size=128)+1j*noise.normal(size=128))
coefficient = np.linalg.lstsq(training.conj(),labels,rcond=None)[0]
calibration = np.linalg.norm(coefficient)
learned = coefficient/calibration
learned *= np.exp(-1j*np.angle(np.vdot(psi,learned)))
holdout = np.stack([walker() for _ in range(96)])
rmse = float(np.sqrt(np.mean(abs((holdout.conj()@psi)-(holdout.conj()@learned))**2)))
energy = float(np.vdot(learned,H@learned).real)
result = {
    "scope":"finite Hubbard control with synthetic labels; not IonQ replication",
    "seed":261108129,
    "ground_energy":float(energies[0]),
    "learned_energy":energy,
    "energy_error":abs(energy-float(energies[0])),
    "true_attenuation":attenuation,
    "fitted_attenuation":float(calibration),
    "heldout_overlap_rmse":rmse,
    "mean_ratio_error_1000":float(np.mean([x[0] for x in errors])),
    "mean_ratio_error_16000":float(np.mean([x[1] for x in errors])),
    "six_ratio_errors":errors
}
print(json.dumps(result,indent=2))
assert rmse < .02
assert abs(calibration-attenuation) < .04
assert abs(energy-energies[0]) < .02
assert result["mean_ratio_error_16000"] < result["mean_ratio_error_1000"]
