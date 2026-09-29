#!/usr/bin/env python3
"""Differentiable TESSERA v2 student sensor attribution with independent labels.

Use *real* upstream checkpoint and preprocessed Sentinel input arrays. This
adapter replicates the upstream student/infer.py deterministic fixed-mask,
fixed-bin path *with torch tensors*, permitting end-to-end autograd.
Missingness, bin selection and repeated source indices are discrete and NOT
differentiated. Model is loaded only from explicit trusted checkpoint.

Reference upstream: ucam-eo/tessera/tessera_infer_v2/student/{model,infer}.py.
S2 channels are B04,B02,B03,B08,B8A,B05,B06,B07,B11,B12.
S1 channels VV,VH; ascending and descending have different z-score stats.
No elevation/vegetation interpretation without externally measured labels.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

import numpy as np
import torch

S2_BANDS = ("B04", "B02", "B03", "B08", "B8A", "B05", "B06", "B07", "B11", "B12")
S1_BANDS = ("VV", "VH")
VALID_PREFIXES = (16,32,64,128)


def checked_inputs(s2, doy, mask, s1a, d1a, s1d, d1d):
    s2=np.asarray(s2)
    if s2.ndim != 3 or s2.shape[0] != 1 or s2.shape[2] != 10:
        raise ValueError("S2 requires (1,T,10) raw bands in documented order")
    if np.asarray(doy).shape != (1,s2.shape[1]) or np.asarray(mask).shape != (1,s2.shape[1]):
        raise ValueError("S2 DOY and masks must be (1,T)")
    if not np.isin(mask,[0,1]).all() or not ((np.asarray(doy)>=1)&(np.asarray(doy)<=365)).all():
        raise ValueError("1 means clear, 0 cloud; DOY in 1..365")
    if not np.isfinite(s2).all():
        raise ValueError("nonfinite S2, no invented imputation")
    if not np.any(mask):
        raise ValueError("at least one valid S2 acquisition required")
    for name,band,times in (("S1 ascending",s1a,d1a),("S1 descending",s1d,d1d)):
        if band is None:
            if times is not None: raise ValueError(f"{name} has timestamps without bands")
            continue
        if np.asarray(band).ndim!=3 or np.asarray(band).shape[0]!=1 or np.asarray(band).shape[2]!=2:
            raise ValueError(f"{name} must have shape (1,T,2)")
        if np.asarray(times).shape != (1,np.asarray(band).shape[1]):
            raise ValueError(f"{name} DOY mismatch")
        if not np.isfinite(band).all() or not ((np.asarray(times)>=1)&(np.asarray(times)<=365)).all():
            raise ValueError(f"{name} nonfinite or invalid DOY")


def selection(valid, infer):
    idx=np.flatnonzero(np.asarray(valid,dtype=bool))
    if not len(idx): return np.empty(0,dtype=np.int64)
    bin_size=infer.get_bin_size(len(idx))
    if bin_size == 0: return np.empty(0,dtype=np.int64)
    return idx[infer._pad_pattern(len(idx),bin_size)]


def prepare_torch(s2,doy,mask,s1a,d1a,s1d,d1d,infer,student,device="cpu"):
    checked_inputs(s2,doy,mask,s1a,d1a,s1d,d1d)
    device=torch.device(device)
    s2_raw=torch.tensor(s2,dtype=torch.float32,device=device,requires_grad=True)
    s2_valid=np.asarray(mask)[0].astype(bool)
    s2_idx=selection(s2_valid,infer)
    s2_mean=torch.as_tensor(student.S2_BAND_MEAN,device=device)
    s2_std=torch.as_tensor(student.S2_BAND_STD,device=device)
    s2_z=(s2_raw[:,s2_idx,:]-s2_mean)/(s2_std+1e-9)
    s2_time=torch.as_tensor(np.asarray(doy)[:,s2_idx,None],dtype=torch.float32,device=device)
    s2_input=torch.cat([s2_z,s2_time],dim=-1)
    s2_raw.retain_grad()

    streams=[]
    valid=[]
    times=[]
    raw_refs=[]
    for raw,raw_doy,mean,std in (
            (s1a,d1a,student.S1A_BAND_MEAN,student.S1A_BAND_STD),
            (s1d,d1d,student.S1D_BAND_MEAN,student.S1D_BAND_STD)):
        if raw is None:
            raw_refs.append(None)
            continue
        raw_t=torch.tensor(raw,dtype=torch.float32,device=device,requires_grad=True)
        raw_refs.append(raw_t)
        streams.append((raw_t-torch.as_tensor(mean,device=device))/
                       (torch.as_tensor(std,device=device)+1e-9))
        valid.extend(np.any(np.asarray(raw)[0]!=0,axis=-1).tolist())
        times.extend(np.asarray(raw_doy)[0].tolist())
    if streams:
        merged=torch.cat(streams,dim=1)
        s1_idx=selection(valid,infer)
        if not len(s1_idx):
            s1_input=torch.zeros((1,1,3),dtype=torch.float32,device=device)
        else:
            s1_z=merged[:,s1_idx,:]
            s1_time=torch.tensor(np.array(times,dtype=np.float32)[s1_idx],
                                 dtype=torch.float32,device=device).reshape(1,-1,1)
            s1_input=torch.cat([s1_z,s1_time],dim=-1)
    else:
        s1_idx=np.empty(0,dtype=np.int64)
        s1_input=torch.zeros((1,1,3),dtype=torch.float32,device=device)
    return (s2_input,s1_input),(s2_raw,raw_refs),{
        "s2_original_indices":s2_idx.tolist(),
        "s1_merged_indices":s1_idx.tolist(),
        "s2_valid_count":int(s2_valid.sum()),
        "s1_valid_count":int(np.count_nonzero(valid))}


def jacobians(model, inputs, raws, *, prefix=128, decoder=None):
    """Returns local coordinate gradients on original raw sensor observations.

    If decoder is a fitted differentiable PyTorch head, compute dY/dInput.
    With no decoder, computes d(embedding[:prefix])/dInput (large output!).
    """
    if prefix not in VALID_PREFIXES: raise ValueError("unsupported prefix")
    s2_input,s1_input=inputs
    s2_raw,raw_s1=raws
    sources=[s2_raw]+[a for a in raw_s1 if a is not None]
    if any(a.device != s2_raw.device for a in sources):
        raise ValueError("inconsistent tensor devices")
    model.eval()
    embedding=model.encode(s2_input,s1_input)
    if embedding.shape != (1,128):
        raise ValueError(f"expected student v2 output (1,128), got {tuple(embedding.shape)}")
    predicted=embedding[:,:prefix]
    if decoder is not None:
        decoder.eval()
        predicted=decoder(predicted)
        if predicted.ndim != 2 or predicted.shape[0]!=1:
            raise ValueError("decoder must output (1,M)")
    derivs=[]
    for index in range(predicted.shape[1]):
        derivatives=torch.autograd.grad(predicted[0,index],sources,
          retain_graph=index+1<predicted.shape[1],allow_unused=True)
        derivs.append([torch.zeros_like(raw) if grad is None else grad
                       for raw,grad in zip(sources,derivatives)])
    # Each element has dimensions (output features, 1, time, spectral band).
    gradients=[torch.stack([out[k] for out in derivs],dim=0).detach().cpu().numpy()
               for k in range(len(sources))]
    return embedding.detach().cpu().numpy(), predicted.detach().cpu().numpy(), gradients


def integrated_gradients(model, inputs, raws, *, prefix, decoder, steps=32):
    """IG between fixed valid raw sensor inputs and zero-valued raw baseline.

    Crucial: baseline is applied AFTER discrete mask/time/selection decisions;
    it does not change which raw timesteps are declared valid.
    Zero is *not* claimed as a physically possible atmospheric observation.
    Report completeness error and baseline dependence.
    """
    if steps < 1: raise ValueError("steps must be >=1")
    tensor_inputs, raw_tensors=inputs, raws
    # Reconstruct selected standardized inputs by interpolating spectral bands
    # to a zero *standardized* reference, leaving DOY unchanged.
    s2,s1=tensor_inputs
    b2=torch.cat((torch.zeros_like(s2[:,:,:10]),s2[:,:,10:]),dim=-1)
    b1=torch.cat((torch.zeros_like(s1[:,:,:2]),s1[:,:,2:]),dim=-1)
    def f(a,b):
        enc=model.encode(a,b)[:,:prefix]
        return decoder(enc).sum() if decoder is not None else enc.sum()
    sums2=torch.zeros_like(s2)
    sums1=torch.zeros_like(s1)
    for k in range(1,steps+1):
        a=(b2+(s2-b2)*float(k)/steps).detach().requires_grad_(True)
        b=(b1+(s1-b1)*float(k)/steps).detach().requires_grad_(True)
        grad=torch.autograd.grad(f(a,b),(a,b),allow_unused=True)
        sums2 += grad[0].detach() if grad[0] is not None else 0
        sums1 += grad[1].detach() if grad[1] is not None else 0
    attr2=(s2-b2)*sums2/steps
    attr1=(s1-b1)*sums1/steps
    delta=(f(s2,s1)-f(b2,b1)).item()
    estimated=(attr2.sum()+attr1.sum()).item()
    return {"s2_standardized":attr2.detach().cpu().numpy().tolist(),
            "s1_standardized":attr1.detach().cpu().numpy().tolist(),
            "input_output_change":delta,
            "attribution_sum":estimated,
            "completeness_residual":abs(delta-estimated),
            "baseline":"zero standardized spectral bands, unchanged DOY/mask/indices",
            "steps":steps}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--upstream-student",required=True,help="path to upstream tessera_infer_v2/student")
    p.add_argument("--checkpoint",required=True,help="trusted upstream student .pt")
    p.add_argument("--input-npz",required=True,help="raw inputs and fixed QA arrays")
    p.add_argument("--output",required=True)
    p.add_argument("--prefix",type=int,choices=VALID_PREFIXES,default=128)
    p.add_argument("--device",default="cpu")
    a=p.parse_args()
    sys.path.insert(0,str(Path(a.upstream_student).resolve()))
    import model as student
    import infer
    model=student.load_model(a.checkpoint,torch.device(a.device))
    with np.load(a.input_npz,allow_pickle=False) as data:
        arrays={name:data[name] if name in data else None for name in
                ("s2_bands","s2_doys","s2_masks","s1_asc_bands","s1_asc_doys",
                 "s1_desc_bands","s1_desc_doys")}
    if any(arrays[name] is None for name in ("s2_bands","s2_doys","s2_masks")):
        raise ValueError("missing required S2 arrays or cloud mask")
    inputs,raws,indices=prepare_torch(
        arrays["s2_bands"],arrays["s2_doys"],arrays["s2_masks"],
        arrays["s1_asc_bands"],arrays["s1_asc_doys"],
        arrays["s1_desc_bands"],arrays["s1_desc_doys"],infer,student,a.device)
    emb,out,grad=jacobians(model,inputs,raws,prefix=a.prefix)
    # No fitted physical decoder here: gradients relate embedding coords to
    # selected sensor channels, not vegetation density or other labels.
    np.savez_compressed(a.output,embedding=emb,prefix=out,
                        grad_s2=grad[0],
                        **{f"grad_s1_{i}":g for i,g in enumerate(grad[1:])})
    digest=hashlib.sha256(Path(a.checkpoint).read_bytes()).hexdigest()
    receipt={"checkpoint_sha256":digest,"upstream_student":str(a.upstream_student),
             "input_sha256":hashlib.sha256(Path(a.input_npz).read_bytes()).hexdigest(),
             "prefix":a.prefix,"indices":indices,
             "gradient_shape":[list(g.shape) for g in grad],
             "claim":"Local sensor gradients of student embedding coordinates, not causal physical effects.",
             "physical_decoder":"NONE; requires independent field-labelled training and validation",
             "preprocessing":"upstream v2 student means/std, frozen discrete acquisition selection"}
    Path(str(a.output)+".json").write_text(json.dumps(receipt,indent=2)+"\n")


if __name__=="__main__":
    main()
