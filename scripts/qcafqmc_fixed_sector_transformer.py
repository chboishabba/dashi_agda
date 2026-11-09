#!/usr/bin/env python3
"""Fixed-particle 16-qubit autoregressive complex neural quantum state.

Independent PyTorch implementation inspired by Provazza et al.,
arXiv:2611.08129 (2026). NOT their unreleased 13k-parameter checkpoint
or a substitution for matchgate shadow tomography.

Requires source-provided complex walker overlap labels in NPZ format:
  walker_amplitudes: complex [Nexamples, Nconfigs]
  overlap_labels: complex [Nexamples]
  occupations: int {0,1} [Nconfigs, 16]
  dataset_kind: scalar 'original' / 'synthetic' / 'processed-external'
  source_url: scalar source locator
  n_alpha, n_beta: scalar integers

Input observations must ALREADY be estimated from shadows by a physically
validated matchgate estimator; this code does not invent that estimator.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import torch
from torch import nn

class AutoregressiveNQS(nn.Module):
    def __init__(self,n=16,width=24,heads=4,layers=1,ff=48):
        super().__init__()
        self.n=n
        self.embedding=nn.Embedding(3,width)
        self.position=nn.Parameter(torch.zeros(1,n,width))
        self.net=nn.TransformerEncoder(
            nn.TransformerEncoderLayer(width,heads,ff,dropout=0.,
              activation="gelu",batch_first=True,norm_first=True),
            num_layers=layers,enable_nested_tensor=False)
        self.logits=nn.Linear(width,2)
        self.phase=nn.Linear(width,1)
        self.log_attenuation=nn.Parameter(torch.tensor(-.30))

    def forward(self,bits,n_alpha,n_beta):
        if bits.shape[-1]!=self.n or self.n!=16:
            raise ValueError("16-qubit input expected")
        b=bits.long()
        shifted=torch.cat((torch.full_like(b[:,:1],2),b[:,:-1]),dim=1)
        hidden=self.embedding(shifted)+self.position
        mask=torch.triu(torch.ones((self.n,self.n),device=b.device,dtype=torch.bool),1)
        out=self.net(hidden,mask=mask)
        logits=self.logits(out)
        # Legal completions for fixed (N_alpha,N_beta) particle sectors.
        logprob=torch.zeros(b.shape[0],device=b.device)
        for segment,target,start in ((0,n_alpha,0),(1,n_beta,8)):
            del segment
            for pos in range(start,start+8):
                local=b[:,start:pos]
                count=local.sum(dim=1)
                remain=8-(pos-start)
                allow0=(target-count)<=remain-1
                allow1=(target-count)>0
                selectable=logits[:,pos,:].clone()
                selectable[:,0]=selectable[:,0].masked_fill(~allow0,-1e8)
                selectable[:,1]=selectable[:,1].masked_fill(~allow1,-1e8)
                probs=torch.log_softmax(selectable,dim=-1)
                logprob+=probs.gather(1,b[:,pos,None]).squeeze(1)
        if not torch.all(b[:,:8].sum(dim=1)==n_alpha) or not torch.all(b[:,8:].sum(dim=1)==n_beta):
            raise ValueError("occupation violates fixed particle sectors")
        angle=torch.tanh(self.phase(out)).squeeze(-1).sum(dim=1)
        return torch.exp(.5*logprob)*torch.exp(1j*angle)

def read_data(path):
    with np.load(path,allow_pickle=False) as z:
        required={"walker_amplitudes","overlap_labels","occupations",
                  "dataset_kind","source_url","n_alpha","n_beta"}
        if not required.issubset(set(z.files)):
            raise ValueError("missing NPZ keys: "+str(sorted(required-set(z.files))))
        data={k:z[k].copy() for k in required}
    occ=data["occupations"]
    wa=data["walker_amplitudes"]
    labels=data["overlap_labels"]
    na=int(data["n_alpha"]);nb=int(data["n_beta"])
    if occ.ndim!=2 or occ.shape[1]!=16 or not np.isin(occ,[0,1]).all():
        raise ValueError("occupations must be 16-bit arrays")
    if len(set(map(tuple,occ.tolist())))!=len(occ):
        raise ValueError("duplicate configurations")
    if not ((occ[:,:8].sum(axis=1)==na).all() and (occ[:,8:].sum(axis=1)==nb).all()):
        raise ValueError("particle sector mismatch")
    if wa.ndim!=2 or wa.shape[1]!=len(occ) or labels.shape!=(len(wa),):
        raise ValueError("walker/label shapes inconsistent")
    if not 0<=na<=8 or not 0<=nb<=8:raise ValueError("electron numbers invalid")
    from math import comb
    expected=comb(8,na)*comb(8,nb)
    if len(occ)!=expected:
        raise ValueError("need complete fixed-particle sector for normalized overlap evaluation")
    if len(occ)>5000:raise ValueError("unsafe enumeration; use stochastic overlap evaluation")
    if not str(data["source_url"]).strip():raise ValueError("source URL required")
    return data

def train(path,output,epochs=100,seed=17,lr=.001,train_fraction=.8):
    torch.manual_seed(seed); np.random.seed(seed)
    source=Path(path).resolve()
    d=read_data(source)
    n=len(d["overlap_labels"])
    if n<8:raise ValueError("need >=8 independently labeled walkers")
    if not .5<=train_fraction<1.:raise ValueError("train_fraction")
    perm=np.random.default_rng(seed).permutation(n)
    cut=int(n*train_fraction)
    trainids=perm[:cut];validids=perm[cut:]
    cfg=torch.as_tensor(d["occupations"],dtype=torch.long)
    wa=torch.as_tensor(d["walker_amplitudes"],dtype=torch.complex64)
    obs=torch.as_tensor(d["overlap_labels"],dtype=torch.complex64)
    model=AutoregressiveNQS()
    optim=torch.optim.Adam(model.parameters(),lr=lr)
    na=int(d["n_alpha"]);nb=int(d["n_beta"])
    best=float("inf");best_state=None
    history=[]
    for epoch in range(epochs):
        model.train()
        optim.zero_grad()
        psi=model(cfg,na,nb)
        # Overlap = sum_x conjugate(psi[x])*walker[x].
        predicted=wa@psi.conj()
        amp=torch.exp(model.log_attenuation)
        loss=torch.mean(torch.abs(amp*predicted[trainids]-obs[trainids])**2)
        loss.backward()
        optim.step()
        model.eval()
        with torch.no_grad():
            psi=model(cfg,na,nb)
            pred=wa@psi.conj()
            val=float(torch.mean(torch.abs(torch.exp(model.log_attenuation)*pred[validids]-obs[validids])**2))
            tr=float(loss.detach())
            history.append([tr,val])
            if val<best:
                best=val
                best_state={k:v.detach().clone() for k,v in model.state_dict().items()}
    model.load_state_dict(best_state)
    output=Path(output).resolve()
    output.parent.mkdir(parents=True,exist_ok=True)
    torch.save({"weights":best_state,"n_alpha":na,"n_beta":nb,
                "architecture":"independent fixed-sector autoregressive transformer"},
                output)
    receipt={
      "source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
      "source_url":str(d["source_url"]),
      "dataset_kind":str(d["dataset_kind"]),
      "original_ionq_weights":False,
      "matchgate_tomography_proved_here":False,
      "nconfigs":len(cfg),"nobservations":n,
      "parameter_count":sum(p.numel() for p in model.parameters()),
      "fit_attenuation":float(torch.exp(model.log_attenuation).detach()),
      "best_validation_complex_overlap_mse":best,
      "train_count":len(trainids),"validation_count":len(validids),
      "seed":seed,"epochs":epochs,"checkpoint":str(output)}
    output.with_suffix(".receipt.json").write_text(json.dumps(receipt,indent=2))
    return receipt

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("dataset")
    p.add_argument("--output",required=True)
    p.add_argument("--epochs",type=int,default=100)
    p.add_argument("--seed",type=int,default=17)
    a=p.parse_args()
    print(json.dumps(train(a.dataset,a.output,a.epochs,a.seed),indent=2))
