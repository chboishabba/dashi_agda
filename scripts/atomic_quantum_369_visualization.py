#!/usr/bin/env python3
"""Numerical quantum/atomic atlas for the Atomic 369 programme.

Source roles / attribution:
- NIST DLMF §18.39(ii): normalized hydrogenic Coulomb/Laguerre bound states.
- NIST Atomic Spectroscopy, Spectral Lines: conventional one-electron E1
  selection rules (Delta l = +/-1, Delta m = 0,+/-1).
- DASHI PR #1141 owns the finite depth-one ternary <-> p-shell magnetic C3
  same-action recognition.  This script does NOT promote those finite C3
  facts into a full atomic/ternary identity.

Outputs:
- hydrogenic radial probabilities n<=3;
- p-shell magnetic-basis density slices;
- C3 spatial-rotation and charge-transport matrices;
- weighted hydrogenic n<=3 E1 transition graph;
- JSON execution receipt.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.special import genlaguerre


def radial(n: int, l: int, r, z: float = 1.0):
    r = np.asarray(r)
    rho = 2.0 * z * r / n
    pref = (2.0 * z / n) ** 1.5 * math.sqrt(
        math.factorial(n - l - 1) / (2 * n * math.factorial(n + l))
    )
    return pref * np.exp(-rho / 2) * rho**l * genlaguerre(n-l-1, 2*l+1)(rho)


def Y(l: int, m: int, theta, phi):
    theta = np.asarray(theta)
    phi = np.asarray(phi)
    if l == 0 and m == 0:
        return np.ones_like(theta, dtype=complex) / math.sqrt(4 * math.pi)
    if l == 1:
        if m == -1:
            return math.sqrt(3/(8*math.pi)) * np.sin(theta) * np.exp(-1j*phi)
        if m == 0:
            return math.sqrt(3/(4*math.pi)) * np.cos(theta) + 0j
        if m == 1:
            return -math.sqrt(3/(8*math.pi)) * np.sin(theta) * np.exp(1j*phi)
    if l == 2:
        if m == -2:
            return math.sqrt(15/(32*math.pi)) * np.sin(theta)**2 * np.exp(-2j*phi)
        if m == -1:
            return math.sqrt(15/(8*math.pi)) * np.sin(theta)*np.cos(theta)*np.exp(-1j*phi)
        if m == 0:
            return math.sqrt(5/(16*math.pi)) * (3*np.cos(theta)**2-1) + 0j
        if m == 1:
            return -math.sqrt(15/(8*math.pi)) * np.sin(theta)*np.cos(theta)*np.exp(1j*phi)
        if m == 2:
            return math.sqrt(15/(32*math.pi)) * np.sin(theta)**2 * np.exp(2j*phi)
    raise ValueError((l, m))


def radial_dipole(nf, lf, ni, li):
    f = lambda x: float(radial(nf, lf, x) * radial(ni, li, x) * x**3)
    return quad(f, 0, 100, epsabs=1e-10, epsrel=1e-9, limit=200)[0]


def angular_dipole(lf, mf, li, mi, q):
    x, w = np.polynomial.legendre.leggauss(60)
    theta = np.arccos(x)
    phi = np.linspace(0, 2*math.pi, 120, endpoint=False)
    dphi = 2*math.pi / len(phi)
    value = 0j
    for ti, wi in zip(theta, w):
        t = np.full_like(phi, ti)
        value += wi * np.sum(
            np.conjugate(Y(lf, mf, t, phi))
            * (math.sqrt(4*math.pi/3) * Y(1, q, t, phi))
            * Y(li, mi, t, phi)
        ) * dphi
    return value


def run(out: Path):
    out.mkdir(parents=True, exist_ok=True)

    # Analytic C3 check on the same m=-1,0,+1 basis used by the finite owner.
    alpha = 2*math.pi/3
    theta = np.linspace(.05, math.pi-.05, 81)
    phi = np.linspace(0, 2*math.pi, 121, endpoint=False)
    th, ph = np.meshgrid(theta, phi, indexing='ij')
    c3_residual = {}
    density_residual = {}
    for m in (-1, 0, 1):
        y = Y(1, m, th, ph)
        yr = Y(1, m, th, ph + alpha)
        c3_residual[str(m)] = float(np.max(np.abs(yr - np.exp(1j*m*alpha)*y)))
        density_residual[str(m)] = float(np.max(np.abs(np.abs(yr)**2 - np.abs(y)**2)))

    # Radial probability curves.
    r = np.linspace(0, 25, 1400)
    fig, ax = plt.subplots(figsize=(10, 6))
    for n, l in ((1,0),(2,0),(2,1),(3,0),(3,1),(3,2)):
        ax.plot(r, r*r*np.abs(radial(n,l,r))**2, label=f"{n}{'spdf'[l]}")
    ax.set_xlabel('r / a0')
    ax.set_ylabel('r^2 |R_nl(r)|^2')
    ax.set_title('Hydrogenic radial probability distributions')
    ax.legend(); ax.grid(alpha=.2)
    fig.savefig(out/'hydrogenic_radial_probabilities_n1_n3.png', dpi=220, bbox_inches='tight')
    plt.close(fig)

    # Magnetic-basis 2p density slices.
    grid = np.linspace(-8, 8, 301)
    X, Z = np.meshgrid(grid, grid)
    R = np.sqrt(X*X + Z*Z)
    TH = np.arccos(np.divide(Z, R, out=np.zeros_like(R), where=R>0))
    PH = np.where(X >= 0, 0.0, math.pi)
    for m in (-1, 0, 1):
        psi = radial(2,1,R) * Y(1,m,TH,PH)
        fig, ax = plt.subplots(figsize=(7,7))
        im = ax.imshow(np.abs(psi)**2, extent=[-8,8,-8,8], origin='lower', aspect='equal')
        ax.set_xlabel('x / a0'); ax.set_ylabel('z / a0')
        ax.set_title(f'Hydrogenic 2p magnetic-basis density |psi_2,1,{m}|^2')
        fig.colorbar(im, ax=ax, label='probability density / a0^-3')
        fig.savefig(out/f'hydrogenic_2p_m{m:+d}_density_xz.png', dpi=220, bbox_inches='tight')
        plt.close(fig)

    # Distinct C3 operators on the same basis.
    omega = np.exp(2j*math.pi/3)
    rotation = np.diag([omega**-1, 1, omega])
    charge = np.array([[0,0,1],[1,0,0],[0,1,0]], dtype=complex)

    # Conventional hydrogenic E1 graph n<=3; edge weights are line strengths.
    states = [(n,l,m) for n in range(1,4) for l in range(n) for m in range(-l,l+1)]
    edges = []
    for src in states:
        ni, li, mi = src
        for dst in states:
            nf, lf, mf = dst
            if nf >= ni or abs(lf-li) != 1:
                continue
            q = mf-mi
            if q not in (-1,0,1):
                continue
            rr = radial_dipole(nf,lf,ni,li)
            aa = angular_dipole(lf,mf,li,mi,q)
            strength = float(abs(rr*aa)**2)
            if strength > 1e-8:
                edges.append((src,dst,q,float(rr),float(abs(aa)),strength))

    energy = lambda n: -0.5/(n*n)
    pos = {(n,l,m):(3*l+.55*m, energy(n)) for n,l,m in states}
    fig, ax = plt.subplots(figsize=(11,8))
    for s in states:
        x,y = pos[s]
        n,l,m = s
        ax.scatter([x],[y],s=38,zorder=3)
        ax.text(x,y+.008,f"{n}{'spdf'[l]} m={m:+d}",fontsize=6,ha='center')
    mx = max(e[-1] for e in edges)
    for src,dst,q,rr,aa,strength in edges:
        x0,y0 = pos[src]; x1,y1 = pos[dst]
        ax.annotate('',xy=(x1,y1),xytext=(x0,y0),
                    arrowprops={'arrowstyle':'->','lw':.4+2.2*strength/mx,'alpha':.32})
    ax.set_ylabel('hydrogenic energy / Eh'); ax.set_xticks([]); ax.grid(axis='y',alpha=.2)
    ax.set_title('Hydrogenic n<=3 E1 transition graph — width proportional to line strength')
    fig.savefig(out/'hydrogenic_E1_transition_graph_n1_n3.png',dpi=240,bbox_inches='tight')
    plt.close(fig)

    with (out/'hydrogenic_E1_transition_edges.csv').open('w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['source_n','source_l','source_m','target_n','target_l','target_m','q',
                    'radial_integral_a0','angular_abs','line_strength_a0_sq'])
        for src,dst,q,rr,aa,strength in edges:
            w.writerow([*src,*dst,q,rr,aa,strength])

    receipt = {
        'sources': {
            'DLMF_18_39': {
                'authority': 'NIST Digital Library of Mathematical Functions §18.39(ii)',
                'role': 'normalized hydrogenic Coulomb/Laguerre bound-state reference',
                'promotion': 'analytic hydrogenic execution only; not ternary identity'
            },
            'NIST_E1': {
                'authority': 'NIST Atomic Spectroscopy: Spectral Lines',
                'role': 'conventional one-electron E1 selection-rule reference',
                'promotion': 'transition-surface authority; not measured line-intensity data'
            },
            'DASHI_PR1141': {
                'role': 'finite depth-one ternary <-> p-shell C3 same-action theorem source',
                'promotion': 'finite C3 charge transport only; not full atom identity'
            }
        },
        'c3_execution': {
            'wavefunction_rotation_residual': c3_residual,
            'density_rotation_residual': density_residual,
            'rotation_order3_residual': float(np.linalg.norm(np.linalg.matrix_power(rotation,3)-np.eye(3))),
            'charge_order3_residual': float(np.linalg.norm(np.linalg.matrix_power(charge,3)-np.eye(3))),
            'rotation_charge_commutator_norm': float(np.linalg.norm(rotation@charge-charge@rotation)),
            'noncollapse': 'spatial C3 rotation is diagonal phase action; C3 charge transport is cyclic permutation'
        },
        'E1_graph': {'states': len(states), 'edges': len(edges), 'weight': '|<f|r_q|i>|^2 in a0^2'},
        'frontier': {
            'H': 'analytic hydrogenic + existing repo numerical radial validation',
            'He': 'existing restricted Hartree/HF-limit convergence producer',
            'Li_Be': 'same-object multi-orbital SCF/HF state tracking still required'
        }
    }
    (out/'atomic_quantum_369_receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    return receipt


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', default='outputs/atomic_quantum_369')
    args = p.parse_args()
    print(json.dumps(run(Path(args.out)), indent=2))

if __name__ == '__main__':
    main()
