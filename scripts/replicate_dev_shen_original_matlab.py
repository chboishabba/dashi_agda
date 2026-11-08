#!/usr/bin/env python3
"""Source-data consumer for Dev & Shen, Light Sci Appl 15, 396 (2026).

Original scientific work and data: Vasu Dev and Yijie Shen,
DOI 10.1038/s41377-026-02533-w, dataset DOI 10.21979/N9/AJB6FD
(DR-NTU version 2.0, CC BY-NC 4.0).

Independent DASHI contribution: MATLAB intake, six-channel Stokes
reconstruction, validity mask, open-patch solid-angle integral, hashes,
provenance receipts. Citation does not import proof or physical authority.
An integer-degree result needs a justified boundary compactification;
this script does not invent one. A file in the repository dataset is
not assumed to be an experimental measurement: the repository calls
the dataset 'simulation data'.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.io import loadmat, savemat

CHANNELS = ("IH", "IV", "ID", "IA", "IR", "IL")
SOURCE = {
    "original_authors": "Vasu Dev; Yijie Shen",
    "original_article_doi": "10.1038/s41377-026-02533-w",
    "original_dataset_doi": "10.21979/N9/AJB6FD",
    "dataset_version": "2.0",
    "dataset_license": "CC BY-NC 4.0",
    "adapter": "DASHI independently written analysis"
}

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def read_mat(path):
    try:
        doc = loadmat(path, squeeze_me=True)
        choices = [(k, v) for k, v in doc.items()
                   if not k.startswith("__") and isinstance(v, np.ndarray)
                   and v.ndim == 2 and np.issubdtype(v.dtype, np.number)]
    except NotImplementedError:
        import h5py
        with h5py.File(path) as h:
            choices = [(k, np.asarray(h[k]).T) for k in h
                       if isinstance(h[k], h5py.Dataset)
                       and h[k].ndim == 2
                       and np.issubdtype(h[k].dtype, np.number)]
    if len(choices) != 1:
        raise ValueError(f"{path}: expected exactly one 2D numeric variable; found {[k for k,_ in choices]}")
    a = np.asarray(choices[0][1], dtype=float)
    if min(a.shape) < 3 or not np.isfinite(a).all() or a.min() < -1e-10:
        raise ValueError(f"{path}: invalid image data")
    return np.maximum(a, 0.0)

def discover(root):
    out = {}
    for p in Path(root).rglob("*.mat"):
        if p.stem.upper() in CHANNELS:
            case = str(p.parent.relative_to(root))
            out.setdefault(case, {})[p.stem.upper()] = p
    return out

def channels(paths):
    missing = sorted(set(CHANNELS) - set(paths))
    if missing:
        raise ValueError(f"missing original polarization channels: {missing}")
    img = {k: read_mat(paths[k]) for k in CHANNELS}
    if len({v.shape for v in img.values()}) != 1:
        raise ValueError("channel shapes differ; calibration/registration required")
    return img

def stokes(img, dark=0., intensity_fraction=.001, handedness=1.):
    v = {k: np.maximum(0, np.asarray(img[k],float)-dark) for k in CHANNELS}
    totals = [v["IH"]+v["IV"], v["ID"]+v["IA"], v["IR"]+v["IL"]]
    ref = np.mean(totals, axis=0)
    raw = np.zeros((3,) + ref.shape, dtype=float)
    valid = ref > max(ref.max()*intensity_fraction, 1e-30)
    for t in totals:
        valid &= t > max(ref.max()*intensity_fraction, 1e-30)
    for i, delta in enumerate((v["IH"]-v["IV"], v["ID"]-v["IA"],
                               handedness*(v["IR"]-v["IL"]))):
        np.divide(delta, totals[i], out=raw[i], where=valid)
    degree = np.linalg.norm(raw, axis=0)
    valid &= degree > .5
    n = np.full_like(raw, np.nan)
    np.divide(raw, degree[None], out=n, where=valid[None])
    spread = max(float(np.mean(np.abs(t-ref)) / max(np.mean(ref), 1e-30))
                 for t in totals)
    return n, valid, {
        "valid_pixel_fraction": float(valid.mean()),
        "pair_totals_relative_mismatch": spread,
        "handedness_not_independently_calibrated": True,
        "normalized_stokes_convention": "(H-V, D-A, handedness*(R-L))"
    }

def triangle(a,b,c):
    triple = np.sum(a*np.cross(b,c,axis=0),axis=0)
    denom = 1+np.sum(a*b+b*c+c*a,axis=0)
    result = 2*np.arctan2(triple,denom)
    result[(np.abs(triple)<1e-12)&(np.abs(denom)<1e-12)] = np.nan
    return result

def charge(n,valid):
    a,b,c,d = n[:,:-1,:-1], n[:,:-1,1:], n[:,1:,1:], n[:,1:,:-1]
    good = valid[:-1,:-1]&valid[:-1,1:]&valid[1:,1:]&valid[1:,:-1]
    omega = triangle(a,b,c)+triangle(a,c,d)
    good &= np.isfinite(omega)
    return {
        "open_patch_charge": float(np.sum(omega[good])/(4*np.pi)),
        "complete_cell_fraction": float(good.mean()),
        "incomplete_cells": int(good.size-good.sum()),
        "integer_degree_certified": False,
        "reason": "open field of view, unproven boundary, source mask and handedness"
    }

def run(root,case,outdir):
    groups=discover(root)
    if case not in groups:
        raise ValueError(f"case {case!r} not found; available prefixes: {list(groups)[:10]}")
    paths=groups[case]
    img=channels(paths)
    n,valid,quality=stokes(img)
    receipt={"source": SOURCE, "case":case,
        "source_data_files":{k: {"path":str(paths[k].relative_to(root)), "sha256":sha256(paths[k])}
                             for k in CHANNELS},
        "data_provenance":"dataset describes data type as simulation; individual experimental status unverified",
        "pixel_shape":list(n.shape[1:]), "quality":quality,
        "topology":charge(n,valid), "experimental_replication_certified":False}
    target=Path(outdir);target.mkdir(parents=True,exist_ok=True)
    (target/"receipt.json").write_text(json.dumps(receipt,indent=2))
    np.savez_compressed(target/"stokes.npz",stokes=n,valid=valid)
    return receipt

def tests():
    from tempfile import TemporaryDirectory
    with TemporaryDirectory() as d:
        coord=np.linspace(-7,7,81)
        x,y=np.meshgrid(coord,coord)
        r=x*x+y*y
        n=np.stack((2*x/(1+r),2*y/(1+r),(r-1)/(1+r)))
        target=Path(d)/"SYNTHETIC"/"BP"/"0";target.mkdir(parents=True)
        for name,plane in zip(CHANNELS,(n[0],-n[0],n[1],-n[1],n[2],-n[2])):
            savemat(target/(name+".mat"),{name:.5*(1+plane)})
        receipt=run(d,"SYNTHETIC/BP/0",Path(d)/"output")
        q=receipt["topology"]["open_patch_charge"]
        assert abs(q+1)<.025, q
        assert receipt["quality"]["valid_pixel_fraction"]==1.
        assert all(len(f["sha256"])==64 for f in receipt["source_data_files"].values())
        assert (Path(d)/"output"/"stokes.npz").exists()
        z=channels(discover(d)["SYNTHETIC/BP/0"])
        z["IR"]=np.zeros_like(z["IR"]);z["IL"]=np.zeros_like(z["IL"])
        _,good,_=stokes(z)
        assert not good.any()
        return {"synthetic_six_channel_replay":"PASS",
                "open_patch_BP_charge":q,"real_dataset_bytes_acquired":False}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--test",action="store_true")
    p.add_argument("--root",type=Path)
    p.add_argument("--case")
    p.add_argument("--out",default="replay_output")
    p.add_argument("--list",action="store_true")
    a=p.parse_args()
    if a.test:
        print(json.dumps(tests(),indent=2))
    elif a.root and a.list:
        print(json.dumps({k:list(v) for k,v in discover(a.root).items()},indent=2))
    elif a.root and a.case:
        print(json.dumps(run(a.root,a.case,a.out),indent=2))
    else:
        p.error("use --test, or --root <original dataset directory> --case C4/10_35/0")
