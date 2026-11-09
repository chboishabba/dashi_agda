#!/usr/bin/env python3
"""Independent seniority-zero 16-qubit neural state for (8e,8o).

Constrained upCCD support = exactly four doubly occupied spatial orbitals out
of eight, 70 determinants. Model is NOT claimed to be Provazza/Knitter's
published 13,096-parameter architecture or trained weights.

References: Provazza et al. arXiv:2611.08129v1, §III.1 and Eq.(15).
"""
import argparse
import hashlib
import json
from pathlib import Path
from math import comb
import numpy as np
import torch
from torch import nn

def paired_occupations(n_orbitals=8,n_pairs=4):
    from itertools import combinations
    result=[]
    for occupied in combinations(range(n_orbitals),n_pairs):
        x=np.zeros((2*n_orbitals,),dtype=np.int64)
        for orbital in occupied:x[orbital]=x[orbital+n_orbitals]=1
        result.append(x)
    return np.array(result,dtype=np.int64)

class PairedSpatialNQS(nn.Module):
    def __init__(self,n=8,embed=16,heads=2,feedforward=64):
        super().__init__()
        self.n=n
        self.embedding=nn.Embedding(3,embed)
        self.position=nn.Parameter(torch.zeros(1,n,embed))
        layer=nn.TransformerEncoderLayer(embed,heads,feedforward,
                     dropout=0.,batch_first=True,activation="gelu",norm_first=True)
        self.transformer=nn.TransformerEncoder(layer,1,
                                               enable_nested_tensor=False)
        self.modulus=nn.Linear(embed,2)
        self.phase=nn.Sequential(nn.Linear((n-1)*embed,64),nn.ReLU(),
                                 nn.Linear(64,64),nn.ReLU(),nn.Linear(64,2))
        self.log_calibration=nn.Parameter(torch.tensor(-.3))

    def forward(self,occupations,n_pairs=4):
        if occupations.ndim!=2 or occupations.shape[1]!=2*self.n:
            raise ValueError("expected [batch,16] occupation vectors")
        x=occupations.long()
        pair=x[:,:self.n]
        in_support=(x[:,self.n:]==pair).all(dim=1)&(pair.sum(dim=1)==n_pairs)
        shifted=torch.cat((torch.full_like(pair[:,:1],2),pair[:,:-1]),dim=1)
        hidden=self.embedding(shifted)+self.position
        causal=torch.triu(torch.ones(self.n,self.n,dtype=torch.bool,device=pair.device),1)
        out=self.transformer(hidden,mask=causal)
        logits=self.modulus(out)
        logprob=torch.zeros(x.shape[0],device=x.device)
        for pos in range(self.n):
            occupied=pair[:,:pos].sum(dim=1)
            remaining=self.n-pos-1
            choose_zero=(n_pairs-occupied)<=remaining
            choose_one=(n_pairs-occupied)>0
            scores=logits[:,pos,:].clone()
            scores[:,0]=scores[:,0].masked_fill(~choose_zero,-1e8)
            scores[:,1]=scores[:,1].masked_fill(~choose_one,-1e8)
            logprob+=torch.log_softmax(scores,dim=1).gather(
                                  1,pair[:,pos,None]).flatten()
        angle=torch.pi*torch.tanh(self.phase(out[:,:-1,:].reshape(len(x),-1))
                          .gather(1,pair[:,-1,None]).flatten())
        value=torch.exp(.5*logprob)*torch.exp(1j*angle)
        return torch.where(in_support,value,torch.zeros_like(value))

def read_paired_dataset(path):
    with np.load(path,allow_pickle=False) as z:
        required={"occupations","walker_amplitudes","overlap_labels",
                  "dataset_kind","source_url"}
        if not required.issubset(z.files):
            raise ValueError("missing paired training keys: "+str(sorted(required-set(z.files))))
        d={key:z[key].copy() for key in required}
    occupations=d["occupations"]
    expected=paired_occupations()
    if not np.array_equal(occupations,expected):
        raise ValueError("70 configurations must match canonical full paired-sector ordering")
    walkers=d["walker_amplitudes"]
    labels=d["overlap_labels"]
    if walkers.ndim!=2 or walkers.shape[1]!=70 or labels.shape!=(len(walkers),):
        raise ValueError("walker/overlap data shape mismatch")
    if not np.isfinite(walkers).all() or not np.isfinite(labels).all():
        raise ValueError("nonfinite shadow overlap data")
    if len(labels)<8:raise ValueError("insufficient independent overlap observations")
    if not str(d["source_url"]).strip():raise ValueError("missing source")
    for optional in ("orbital_frame_sha256","geometry_sha256"):
        with np.load(path,allow_pickle=False) as z:
            if optional in z.files:d[optional]=str(z[optional])
    if str(d["dataset_kind"])=="original" and not all(
            d.get(k) for k in ("orbital_frame_sha256","geometry_sha256")):
        raise ValueError("original-source labels need geometry and MO frame hashes")
    return d

def train_paired(path,checkpoint,epochs=100,seed=17,lr=.0025,ridge=0.):
    torch.manual_seed(seed)
    source=Path(path).resolve()
    d=read_paired_dataset(source)
    x=torch.as_tensor(d["occupations"],dtype=torch.long)
    walkers=torch.as_tensor(d["walker_amplitudes"],dtype=torch.complex64)
    labels=torch.as_tensor(d["overlap_labels"],dtype=torch.complex64)
    ids=np.random.default_rng(seed).permutation(len(walkers))
    split=int(.8*len(ids))
    tr=torch.as_tensor(ids[:split]);va=torch.as_tensor(ids[split:])
    model=PairedSpatialNQS()
    opt=torch.optim.AdamW([
        {"params":[p for name,p in model.named_parameters()
                   if name!="log_calibration"],"weight_decay":.01},
        {"params":[model.log_calibration],"weight_decay":0}],
        lr=lr,betas=(.9,.999),eps=1e-8)
    best=float("inf");best_model=None
    for _ in range(epochs):
        model.train();opt.zero_grad()
        predicted=walkers@model(x).conj()
        amp=torch.exp(model.log_calibration)
        loss=(abs(amp*predicted[tr]-labels[tr])**2).mean()+ridge*amp**2
        loss.backward()
        nn.utils.clip_grad_norm_(model.parameters(),1.)
        opt.step()
        model.eval()
        with torch.no_grad():
            check=walkers@model(x).conj()
            value=float((abs(torch.exp(model.log_calibration)*
                             check[va]-labels[va])**2).mean())
            if value<best:
                best=value
                best_model={name:p.detach().clone()
                            for name,p in model.state_dict().items()}
    if best_model is None:raise ValueError("no model state")
    checkpoint=Path(checkpoint).resolve()
    checkpoint.parent.mkdir(parents=True,exist_ok=True)
    torch.save({"architecture":"paired-spatial-v1",
                "weights":best_model,"n_alpha":4,"n_beta":4,
                "orbital_frame_sha256":d.get("orbital_frame_sha256"),
                "geometry_sha256":d.get("geometry_sha256")},checkpoint)
    receipt={"scope":"independent seniority-zero constrained NQS",
             "source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
             "dataset_kind":str(d["dataset_kind"]),
             "source_url":str(d["source_url"]),
             "orbital_frame_sha256":d.get("orbital_frame_sha256"),
             "geometry_sha256":d.get("geometry_sha256"),
             "train_walkers":int(len(tr)),"validation_walkers":int(len(va)),
             "validation_mse":best,
             "parameter_count":sum(p.numel() for p in model.parameters()),
             "paired_determinants":comb(8,4),
             "original_ionq_checkpoint":False,
             "checkpoint":str(checkpoint)}
    checkpoint.with_suffix(".receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("dataset")
    p.add_argument("--checkpoint",required=True)
    p.add_argument("--epochs",type=int,default=100)
    p.add_argument("--seed",type=int,default=17)
    p.add_argument("--ridge",type=float,default=0.)
    a=p.parse_args()
    print(json.dumps(train_paired(a.dataset,a.checkpoint,a.epochs,a.seed,
                                  ridge=a.ridge),indent=2))
