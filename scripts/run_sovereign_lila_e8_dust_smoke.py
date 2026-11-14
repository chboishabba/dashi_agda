#!/usr/bin/env python3
"""Run the restricted Dust optimizer on the REAL Sovereign-LILA E8GPT checkout.
Execute from an environment where SPUTNIKAI/sovereign-lila-e8 is already present.

Original model: SPUTNIKAI; mirrored by meta-introspector.
Original Dust: Dahal/Mandal/Gülbahar/Vegesna. DASHI owns this bridge.
"""
import argparse
import sys
from pathlib import Path
import torch
from sovereign_lila_dust_projection_step import dust_e8_projection_step

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--lila-checkout",required=True,type=Path)
    p.add_argument("--checkpoint",type=Path)
    p.add_argument("--vocab-size",type=int,default=32)
    p.add_argument("--d-model",type=int,default=64)
    p.add_argument("--n-heads",type=int,default=4)
    p.add_argument("--n-layers",type=int,default=1)
    p.add_argument("--seq-len",type=int,default=4)
    p.add_argument("--k",type=int,default=8)
    p.add_argument("--sigma",type=float,default=.05)
    p.add_argument("--lr",type=float,default=.001)
    args=p.parse_args()
    if not (args.lila_checkout/"models"/"model.py").is_file():
        p.error("Expected source checkout with models/model.py")
    sys.path.insert(0,str(args.lila_checkout.resolve()))
    from config.config import E8Config
    from models.model import E8GPT
    torch.set_num_threads(1)
    torch.manual_seed(12)
    cfg=E8Config(vocab_size=args.vocab_size,d_model=args.d_model,
                 n_heads=args.n_heads,n_layers=args.n_layers,
                 block_size=max(args.seq_len,4),dropout=0.)
    model=E8GPT(cfg)
    if args.checkpoint:
        # Explicitly refuse unsafe untrusted checkpoint deserialization.
        state=torch.load(args.checkpoint,map_location="cpu",weights_only=True)
        if isinstance(state,dict) and "model" in state:
            state=state["model"]
        model.load_state_dict(state)
    x=torch.randint(0,args.vocab_size,(2,args.seq_len))
    y=torch.roll(x,-1,dims=1)
    receipt=dust_e8_projection_step(model,x,y,k=args.k,sigma=args.sigma,lr=args.lr)
    assert receipt.update_norm>0 and receipt.forward_calls==args.k+2
    assert all(param.grad is None for param in model.parameters())
    print(receipt)
    print("Original E8GPT instantiated; this is a synthetic-token smoke, not language pretraining.")

if __name__=="__main__":
    main()
