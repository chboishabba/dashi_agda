"""
Minimal end-to-end SL pipeline skeleton for DA51 → SL → Agda.
Keeps to the contract: structure/MDL/admissibility only; no proof semantics.
"""

import numpy as np
from dataclasses import dataclass
from typing import List, Tuple, Sequence, Dict, Any
import json
import hashlib


# ---------------------------
# Data structures
# ---------------------------

@dataclass
class DA51Trace:
    id: str
    exponents: List[int]
    hot: int
    cold: int
    basin: int
    j_fixed: bool


@dataclass
class TraceVector:
    raw: np.ndarray
    normalized: np.ndarray


@dataclass
class TraceInvariant:
    hot_cold_ratio: Tuple[int, int]
    basin: int
    j_fixed: bool
    entropy: float
    mdl_cost: float


@dataclass
class TraceWitness:
    vector: TraceVector
    invariant: TraceInvariant
    admissible: bool


@dataclass
class CanonicalWitness:
    trace_id: str
    residue_vector: List[float]
    basin_id: int
    invariants: Dict[str, float]
    proof_signature: str


# ---------------------------
# Core transforms
# ---------------------------

def normalize(vec: np.ndarray) -> np.ndarray:
    norm = np.linalg.norm(vec)
    return vec / norm if norm != 0 else vec


def entropy(vec: np.ndarray) -> float:
    p = np.abs(vec)
    total = p.sum()
    if total == 0:
        return 0.0
    p = p / total
    return float(-(p * np.log(p + 1e-9)).sum())


def mdl_cost(vec: np.ndarray) -> float:
    return float(np.abs(vec).sum() + entropy(vec))


# ---------------------------
# Cone constraint
# ---------------------------

def cosine_similarity(a: np.ndarray, b: np.ndarray) -> float:
    denom = np.linalg.norm(a) * np.linalg.norm(b)
    if denom == 0:
        return 0.0
    return float(np.dot(a, b) / denom)


def admissible(vec: np.ndarray, attractor: np.ndarray, threshold: float = 0.9993) -> bool:
    return cosine_similarity(vec, attractor) >= threshold


# ---------------------------
# Pipeline
# ---------------------------

def process_trace(trace: DA51Trace, attractor: np.ndarray) -> TraceWitness:
    raw = np.array(trace.exponents, dtype=float)
    norm = normalize(raw)

    vector = TraceVector(raw=raw, normalized=norm)

    inv = TraceInvariant(
        hot_cold_ratio=(trace.hot, trace.cold),
        basin=trace.basin,
        j_fixed=trace.j_fixed,
        entropy=entropy(raw),
        mdl_cost=mdl_cost(raw),
    )

    is_valid = admissible(norm, attractor)

    return TraceWitness(vector, inv, is_valid)


def best_attractor(vec: np.ndarray, attractors: Sequence[np.ndarray]) -> Tuple[np.ndarray, float]:
    if not attractors:
        raise ValueError("attractors must be non-empty")
    sims = [cosine_similarity(vec, a) for a in attractors]
    idx = int(np.argmax(sims))
    return attractors[idx], sims[idx]


def canonical_witness(trace: DA51Trace, attractors: Sequence[np.ndarray], threshold: float = 0.9993) -> CanonicalWitness:
    raw = np.array(trace.exponents, dtype=float)
    norm = normalize(raw)
    attractor, sim = best_attractor(norm, attractors)
    valid = sim >= threshold
    invariants = {
        "entropy": entropy(raw),
        "mdl_cost": mdl_cost(raw),
        "hot": float(trace.hot),
        "cold": float(trace.cold),
        "basin": float(trace.basin),
        "similarity": sim,
    }
    sig_src = f"{trace.id}:{norm.tolist()}:{sim:.8f}"
    signature = hashlib.sha256(sig_src.encode("utf-8")).hexdigest()
    return CanonicalWitness(
        trace_id=trace.id,
        residue_vector=norm.tolist(),
        basin_id=trace.basin,
        invariants=invariants,
        proof_signature=signature if valid else "",
    )


# ---------------------------
# Basin clustering (simple k-means)
# ---------------------------

def kmeans(traces: Sequence[DA51Trace], k: int) -> List[int]:
    if k <= 0:
        raise ValueError("k must be positive")
    data = np.array([t.exponents for t in traces], dtype=float)
    n = data.shape[0]
    if n == 0:
        return []
    # initialize centroids with first k
    centroids = data[:k].copy()
    assignments = np.zeros(n, dtype=int)
    for _ in range(10):
        # assign
        dists = ((data[:, None, :] - centroids[None, :, :]) ** 2).sum(axis=2)
        assignments = dists.argmin(axis=1)
        # update
        for i in range(k):
            mask = assignments == i
            if mask.any():
                centroids[i] = data[mask].mean(axis=0)
    return assignments.tolist()


# ---------------------------
# Cross-run invariance check
# ---------------------------

def invariance_score(witnesses: Sequence[TraceWitness]) -> float:
    if not witnesses:
        return 0.0
    vecs = np.stack([w.vector.normalized for w in witnesses], axis=0)
    # lower variance => higher invariance
    variance = float(np.var(vecs))
    return 1.0 / (1.0 + variance)


def silhouette_score(traces: Sequence[DA51Trace], assignments: Sequence[int], k: int) -> float:
    if k <= 1 or len(traces) != len(assignments):
        return 0.0
    data = np.array([t.exponents for t in traces], dtype=float)
    a = np.zeros(len(traces))
    b = np.zeros(len(traces))
    for i in range(len(traces)):
        same = assignments[i]
        mask_same = np.array(assignments) == same
        mask_other = np.array(assignments) != same
        if mask_same.sum() > 1:
            a[i] = np.mean(np.linalg.norm(data[i] - data[mask_same], axis=1))
        else:
            a[i] = 0.0
        if mask_other.any():
            dists = []
            for c in range(k):
                if c == same:
                    continue
                mask_c = np.array(assignments) == c
                if mask_c.any():
                    dists.append(np.mean(np.linalg.norm(data[i] - data[mask_c], axis=1)))
            b[i] = min(dists) if dists else 0.0
        else:
            b[i] = 0.0
    s = (b - a) / np.maximum(a, b + 1e-9)
    return float(np.mean(s))


# ---------------------------
# Example run
# ---------------------------

if __name__ == "__main__":
    attractor = normalize(np.ones(15))

    trace = DA51Trace(
        id="example",
        exponents=[0, 0, 2, 4, 3, 1, 19, 7, 6, 2, 9, 0, 1, 0, 10],
        hot=15,
        cold=7,
        basin=0,
        j_fixed=False,
    )

    witness = process_trace(trace, attractor)

    print("Admissible:", witness.admissible)
    print("Entropy:", witness.invariant.entropy)
    print("MDL cost:", witness.invariant.mdl_cost)

    # demo clustering and invariance (single element)
    cluster_ids = kmeans([trace], k=1)
    print("Cluster assignment:", cluster_ids)
    inv_score = invariance_score([witness])
    print("Invariance score:", inv_score)
