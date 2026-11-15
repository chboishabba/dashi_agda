#!/usr/bin/env python3
"""Forward-only Dust-style *real parameter update* for Sovereign-LILA E8GPT.

Upstream model: SPUTNIKAI/sovereign-lila-e8 (mirror: meta-introspector).
Original Dust algorithm: Dahal, Mandal, Gülbahar, Vegesna (2026).
DASHI owns this restricted final-E8-projection trainer adapter.

This adapter updates E8GPT.core.layers[-1].from_e8.weight without backward().
It does NOT train the whole model, implement head-cache Dust, or reproduce Noise.
"""
from __future__ import annotations
from dataclasses import dataclass
import torch
import torch.nn.functional as F

@dataclass
class DustReceipt:
    loss_before: float
    loss_after: float
    update_norm: float
    forward_calls: int
    k: int
    sigma: float
    gamma: float

@torch.no_grad()
def dust_e8_projection_step(model, inputs, targets, *, k=8, sigma=0.05,
                            lr=0.001, gamma=0.0, seed=1729):
    if k < 2 or sigma <= 0 or lr <= 0 or not (0 <= gamma <= 1):
        raise ValueError("requires k>=2, sigma>0, lr>0, gamma in [0,1]")
    projection = model.core.layers[-1].from_e8
    if not isinstance(projection, torch.nn.Linear):
        raise TypeError("expected source E8TransformerLayer.from_e8 as nn.Linear")
    # Fix dropout and pre-existing LILA training noise by evaluating cleanly.
    previous_mode = model.training
    model.eval()
    captured = []
    perturbation = [None]
    def capture(_module, args):
        captured.append(args[0].detach())
    def inject(_module, _args, result):
        noise = perturbation[0]
        return result if noise is None else result + sigma * noise
    in_hook = projection.register_forward_pre_hook(capture)
    out_hook = projection.register_forward_hook(inject)
    try:
        torch.manual_seed(seed)
        baseline_logits, _ = model(inputs, targets)
        baseline_token_loss = F.cross_entropy(
            baseline_logits.transpose(1,2), targets, reduction="none")
        # Last-layer from_e8 input is upstream of its output perturbation.
        projection_input = captured[0]
        # Freeze the input to the parameter chart used by this update.
        losses, directions = [], []
        generator = torch.Generator(device=baseline_logits.device)
        generator.manual_seed(seed + 1)
        for _ in range(k):
            eps = torch.randn(
                (inputs.shape[0], inputs.shape[1], projection.out_features),
                device=baseline_logits.device, dtype=projection.weight.dtype,
                generator=generator)
            perturbation[0] = eps
            logits, _ = model(inputs, targets)
            losses.append(F.cross_entropy(
                logits.transpose(1,2), targets, reduction="none"))
            directions.append(eps)
        perturbation[0] = None
        noisy_loss = torch.stack(losses)
        noise = torch.stack(directions)
        centered = noisy_loss.mean(dim=0, keepdim=True) - noisy_loss
        # Future-token causal reward: r_t=sum_{s>=t} gamma^(s-t)c_s
        reward = torch.empty_like(centered)
        accum = torch.zeros_like(centered[:, :, -1])
        for t in range(inputs.shape[1]-1, -1, -1):
            accum = centered[:, :, t] + gamma * accum
            reward[:, :, t] = accum
        activation_gradient = -(reward.unsqueeze(-1)*noise).mean(dim=0)/sigma
        # Source's outer product; CE is averaged over B*T.
        dw = torch.einsum("btc,bti->ci", activation_gradient,
                          projection_input)/(inputs.shape[0]*inputs.shape[1])
        old = projection.weight.detach().clone()
        projection.weight.add_(dw, alpha=-lr)
        logits_after, _ = model(inputs, targets)
        after = F.cross_entropy(logits_after.transpose(1,2), targets).item()
        delta = torch.linalg.vector_norm(projection.weight-old).item()
        return DustReceipt(baseline_token_loss.mean().item(), after,
                           delta, k+2, k, sigma, gamma)
    finally:
        in_hook.remove()
        out_hook.remove()
        model.train(previous_mode)
