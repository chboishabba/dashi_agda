#!/usr/bin/env python3
"""Regenerate checkpoint-bearing Mod97 grokking runs without rewriting history.

The checked-in Mod97 receipt fixes task geometry and several training coordinates,
but it does not record the original embedding/hidden widths or exact split-generation
procedure. Therefore every run produced here is a *new run family* unless later
primary provenance pays those missing coordinates. The script never reconstructs
historical checkpoints from final-accuracy receipts.

The pure manifest/split/schedule helpers intentionally have no torch dependency so
provenance tests remain cheap. PyTorch is imported only when numerical training is
requested.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

MODULUS = 97
TOTAL_PAIRS = MODULUS * MODULUS
TRAINING_PAIRS = 2822
TEST_PAIRS = TOTAL_PAIRS - TRAINING_PAIRS
HORIZON = 15000
MEASUREMENT_CADENCE = 20
LEARNING_RATE = 0.001


@dataclass(frozen=True)
class Mod97RunConfig:
    seed: int
    split_seed: int
    weight_decay_milli: int
    embedding_dim: int
    hidden_dim: int
    checkpoint_cadence: int
    pair_composition: str = "concat"
    horizon: int = HORIZON
    measurement_cadence: int = MEASUREMENT_CADENCE

    def __post_init__(self) -> None:
        if self.embedding_dim <= 0:
            raise ValueError("embedding_dim must be positive")
        if self.hidden_dim <= 0:
            raise ValueError("hidden_dim must be positive")
        if self.checkpoint_cadence <= 0:
            raise ValueError("checkpoint_cadence must be positive")
        if self.measurement_cadence <= 0:
            raise ValueError("measurement_cadence must be positive")
        if self.horizon <= 0:
            raise ValueError("horizon must be positive")
        if self.weight_decay_milli < 0:
            raise ValueError("weight_decay_milli must be non-negative")
        if self.pair_composition != "concat":
            raise ValueError("only pair_composition='concat' is currently implemented")

    @property
    def weight_decay(self) -> float:
        return self.weight_decay_milli / 1000.0


def checkpoint_epochs(horizon: int, cadence: int) -> list[int]:
    if horizon < 0:
        raise ValueError("horizon must be non-negative")
    if cadence <= 0:
        raise ValueError("cadence must be positive")
    epochs = list(range(0, horizon + 1, cadence))
    if not epochs or epochs[-1] != horizon:
        epochs.append(horizon)
    return epochs


def deterministic_split_indices(
    total_pairs: int, training_pairs: int, split_seed: int
) -> tuple[list[int], list[int]]:
    if total_pairs <= 0:
        raise ValueError("total_pairs must be positive")
    if training_pairs <= 0 or training_pairs >= total_pairs:
        raise ValueError("training_pairs must lie strictly between zero and total_pairs")
    indices = list(range(total_pairs))
    random.Random(split_seed).shuffle(indices)
    train = indices[:training_pairs]
    test = indices[training_pairs:]
    return train, test


def build_manifest(config: Mod97RunConfig) -> dict[str, Any]:
    return {
        "producer": "scripts/mod97_checkpoint_producer.py",
        "task": {
            "name": "modular multiplication",
            "modulus": MODULUS,
            "total_pairs": TOTAL_PAIRS,
            "training_pairs": TRAINING_PAIRS,
            "test_pairs": TEST_PAIRS,
        },
        "architecture": {
            "shared_residue_embedding": True,
            "embedding_dim": config.embedding_dim,
            "pair_composition": config.pair_composition,
            "hidden_layers": 1,
            "hidden_dim": config.hidden_dim,
            "activation": "ReLU",
            "output_classes": MODULUS,
        },
        "training": {
            "optimizer": "AdamW",
            "learning_rate": LEARNING_RATE,
            "weight_decay_milli": config.weight_decay_milli,
            "weight_decay": config.weight_decay,
            "full_batch": True,
            "device": "cpu",
            "seed": config.seed,
            "split_seed": config.split_seed,
            "horizon": config.horizon,
            "measurement_cadence": config.measurement_cadence,
            "checkpoint_cadence": config.checkpoint_cadence,
            "checkpoint_epochs": checkpoint_epochs(
                config.horizon, config.checkpoint_cadence
            ),
        },
        "provenance": {
            "historical_receipt_surface": "DASHI/Learning/Mod97WeightDecayReceipt.agda",
            "historical_receipt_same_run": False,
            "historical_receipt_same_configuration": False,
            "historical_checkpoint_reconstruction": False,
            "historical_gap": (
                "The checked-in receipt does not pay the original embedding/hidden widths "
                "or exact split-generation procedure; pair-composition details are likewise "
                "not sufficient to assert same-configuration identity."
            ),
            "claim_scope": (
                "This producer creates a new checkpoint-bearing run family under explicit "
                "configuration. Matching weight decay/seed or final accuracy does not make "
                "it the historical run."
            ),
        },
    }


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _all_pairs() -> tuple[list[tuple[int, int]], list[int]]:
    pairs: list[tuple[int, int]] = []
    targets: list[int] = []
    for left in range(MODULUS):
        for right in range(MODULUS):
            pairs.append((left, right))
            targets.append((left * right) % MODULUS)
    return pairs, targets


def run_training(config: Mod97RunConfig, output_dir: Path) -> dict[str, Any]:
    try:
        import torch
        from torch import nn
    except ImportError as exc:  # pragma: no cover - environment-dependent boundary
        raise RuntimeError(
            "PyTorch is required for numerical training; use --plan-only for provenance-only output"
        ) from exc

    torch.manual_seed(config.seed)
    torch.use_deterministic_algorithms(True)

    pairs, targets = _all_pairs()
    train_indices, test_indices = deterministic_split_indices(
        TOTAL_PAIRS, TRAINING_PAIRS, config.split_seed
    )

    def tensorize(indices: list[int]):
        left = torch.tensor([pairs[i][0] for i in indices], dtype=torch.long)
        right = torch.tensor([pairs[i][1] for i in indices], dtype=torch.long)
        y = torch.tensor([targets[i] for i in indices], dtype=torch.long)
        return left, right, y

    train_left, train_right, train_y = tensorize(train_indices)
    test_left, test_right, test_y = tensorize(test_indices)

    class SharedEmbeddingMLP(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.embedding = nn.Embedding(MODULUS, config.embedding_dim)
            self.hidden = nn.Linear(2 * config.embedding_dim, config.hidden_dim)
            self.output = nn.Linear(config.hidden_dim, MODULUS)

        def forward(self, left, right):
            joined = torch.cat((self.embedding(left), self.embedding(right)), dim=-1)
            return self.output(torch.relu(self.hidden(joined)))

    model = SharedEmbeddingMLP().cpu()
    optimizer = torch.optim.AdamW(
        model.parameters(), lr=LEARNING_RATE, weight_decay=config.weight_decay
    )
    criterion = nn.CrossEntropyLoss()

    output_dir.mkdir(parents=True, exist_ok=True)
    checkpoints_dir = output_dir / "checkpoints"
    checkpoints_dir.mkdir(parents=True, exist_ok=True)
    checkpoint_set = set(checkpoint_epochs(config.horizon, config.checkpoint_cadence))
    metrics: list[dict[str, Any]] = []
    checkpoint_receipts: list[dict[str, Any]] = []
    test95_epoch: int | None = None

    def accuracy(left, right, y) -> float:
        model.eval()
        with torch.no_grad():
            predictions = model(left, right).argmax(dim=-1)
            return float((predictions == y).float().mean().item())

    def measure(epoch: int) -> None:
        nonlocal test95_epoch
        train_acc = accuracy(train_left, train_right, train_y)
        test_acc = accuracy(test_left, test_right, test_y)
        metrics.append(
            {"epoch": epoch, "train_accuracy": train_acc, "test_accuracy": test_acc}
        )
        if test95_epoch is None and test_acc >= 0.95:
            test95_epoch = epoch

    def save_checkpoint(epoch: int) -> None:
        path = checkpoints_dir / f"epoch-{epoch:05d}.pt"
        torch.save(
            {
                "epoch": epoch,
                "config": asdict(config),
                "model_state_dict": model.state_dict(),
                "optimizer_state_dict": optimizer.state_dict(),
                "historical_receipt_same_run": False,
                "historical_receipt_same_configuration": False,
            },
            path,
        )
        checkpoint_receipts.append(
            {"epoch": epoch, "path": str(path), "sha256": _sha256(path)}
        )

    measure(0)
    if 0 in checkpoint_set:
        save_checkpoint(0)

    for epoch in range(1, config.horizon + 1):
        model.train()
        optimizer.zero_grad(set_to_none=True)
        logits = model(train_left, train_right)
        loss = criterion(logits, train_y)
        loss.backward()
        optimizer.step()

        if epoch % config.measurement_cadence == 0 or epoch == config.horizon:
            measure(epoch)
        if epoch in checkpoint_set:
            save_checkpoint(epoch)

    manifest = build_manifest(config)
    receipt = {
        **manifest,
        "producer_sha256": _sha256(Path(__file__)),
        "run": {
            "metrics": metrics,
            "test95_first_passage": (
                {"kind": "observedAt", "epoch": test95_epoch}
                if test95_epoch is not None
                else {"kind": "rightCensored", "horizon": config.horizon}
            ),
            "checkpoints": checkpoint_receipts,
        },
        "non_promotion_boundary": (
            "Checkpoint production pays only a new-run empirical trajectory. It does not "
            "recover historical checkpoint custody, circuit mechanism identity, beta "
            "transition timing, or GrokkingMechanismWitness."
        ),
    }
    receipt_path = output_dir / "run-receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--split-seed", type=int, required=True)
    parser.add_argument("--weight-decay-milli", type=int, required=True)
    parser.add_argument("--embedding-dim", type=int, required=True)
    parser.add_argument("--hidden-dim", type=int, required=True)
    parser.add_argument("--checkpoint-cadence", type=int, default=1000)
    parser.add_argument("--horizon", type=int, default=HORIZON)
    parser.add_argument("--measurement-cadence", type=int, default=MEASUREMENT_CADENCE)
    parser.add_argument("--output-dir", type=Path, default=Path("Artifacts/grokking/mod97-checkpoints"))
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args()

    config = Mod97RunConfig(
        seed=args.seed,
        split_seed=args.split_seed,
        weight_decay_milli=args.weight_decay_milli,
        embedding_dim=args.embedding_dim,
        hidden_dim=args.hidden_dim,
        checkpoint_cadence=args.checkpoint_cadence,
        horizon=args.horizon,
        measurement_cadence=args.measurement_cadence,
    )

    if args.plan_only:
        print(json.dumps(build_manifest(config), indent=2, sort_keys=True))
        return

    receipt = run_training(config, args.output_dir)
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
