#!/usr/bin/env python3
"""Small dependency-free-data PyTorch contract smoke for E8GPT hook interface.
Requires installed torch and sibling script; NOT original-model reproduction.
"""
import torch
from torch import nn
import torch.nn.functional as F
from sovereign_lila_dust_projection_step import dust_e8_projection_step

class ShapeCompatibleModel(nn.Module):
    def __init__(self):
        super().__init__()
        self.emb = nn.Embedding(8, 8)
        self.core = nn.Module()
        layer = nn.Module()
        layer.from_e8 = nn.Linear(8, 8, bias=False)
        self.core.layers = nn.ModuleList([layer])
        self.head = nn.Linear(8, 8)
    def forward(self, tokens, targets=None):
        logits = self.head(self.core.layers[-1].from_e8(self.emb(tokens)))
        loss = None if targets is None else F.cross_entropy(
            logits.transpose(1, 2), targets)
        return logits, loss

def main():
    torch.manual_seed(12)
    model = ShapeCompatibleModel()
    x = torch.tensor([[1, 2, 3]], dtype=torch.long)
    y = torch.tensor([[2, 3, 4]], dtype=torch.long)
    receipt = dust_e8_projection_step(model, x, y, k=8, sigma=.05,
                                      lr=.01, gamma=0, seed=1729)
    assert receipt.update_norm > 0
    assert receipt.forward_calls == 10
    assert not any(p.grad is not None for p in model.parameters())
    print(receipt)

if __name__ == "__main__":
    main()
