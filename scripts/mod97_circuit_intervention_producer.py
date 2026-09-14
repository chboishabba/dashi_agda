#!/usr/bin/env python3
"""Produce raw hidden-unit intervention receipts from a Mod97 checkpoint.

Candidate hidden units are selected using training activations only. The candidate
set is then frozen and singleton/joint ablations are evaluated on the held-out test
split. This pays a raw intervention surface only: it does not infer requirement
edges, promote conflict/independence classes, certify beta maximality, or establish
a Grokking mechanism.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable

try:
    from scripts.mod97_checkpoint_producer import (
        MODULUS,
        TOTAL_PAIRS,
        TRAINING_PAIRS,
        Mod97RunConfig,
        deterministic_split_indices,
    )
except ModuleNotFoundError:
    from mod97_checkpoint_producer import (
        MODULUS,
        TOTAL_PAIRS,
        TRAINING_PAIRS,
        Mod97RunConfig,
        deterministic_split_indices,
    )

LOSS_DAMAGE_SCALE = 1_000_000


def select_candidates_from_training(
    activations: Iterable[Iterable[float]], candidate_count: int
) -> list[int]:
    rows = [list(row) for row in activations]
    if not rows:
        raise ValueError("training activations must be non-empty")
    width = len(rows[0])
    if width == 0:
        raise ValueError("training activations must have positive width")
    if any(len(row) != width for row in rows):
        raise ValueError("training activation rows must have equal width")
    if candidate_count <= 0 or candidate_count > width:
        raise ValueError("candidate_count must lie between one and hidden width")

    scores = []
    for unit in range(width):
        score = sum(abs(row[unit]) for row in rows) / len(rows)
        scores.append((score, unit))
    scores.sort(key=lambda item: (-item[0], item[1]))
    return [unit for _, unit in scores[:candidate_count]]


def interaction_excess(left_effect: float, right_effect: float, joint_effect: float) -> float:
    return joint_effect - (left_effect + right_effect)


def canonical_damage_microunits(loss_increase: float) -> int:
    """Map signed held-out loss change to the non-negative Nat damage carrier.

    Negative loss changes mean the intervention improved held-out loss. They remain
    present in the raw receipt but contribute zero damage to the Nat adapter; this
    avoids silently encoding a signed quantity in the existing non-negative formal
    classifier. The scale is local experiment metadata, not a source-derived unit.
    """

    return max(0, int(round(loss_increase * LOSS_DAMAGE_SCALE)))


def build_intervention_receipt(
    *,
    checkpoint_path: str,
    checkpoint_sha256: str,
    selected_units: list[int],
    baseline_test_loss: float,
    singleton_effects: dict[int, float],
    pair_effects: dict[tuple[int, int], float],
) -> dict[str, Any]:
    pairs = []
    for (left, right), joint_effect in sorted(pair_effects.items()):
        raw_excess = interaction_excess(
            singleton_effects[left], singleton_effects[right], joint_effect
        )
        pairs.append(
            {
                "left": left,
                "right": right,
                "left_effect": singleton_effects[left],
                "right_effect": singleton_effects[right],
                "joint_effect": joint_effect,
                "interaction_excess": raw_excess,
                "left_damage_microunits": canonical_damage_microunits(
                    singleton_effects[left]
                ),
                "right_damage_microunits": canonical_damage_microunits(
                    singleton_effects[right]
                ),
                "joint_damage_microunits": canonical_damage_microunits(joint_effect),
            }
        )

    return {
        "producer": "scripts/mod97_circuit_intervention_producer.py",
        "checkpoint": {
            "path": checkpoint_path,
            "sha256": checkpoint_sha256,
        },
        "selection": {
            "carrier": "training activations",
            "rule": "top mean absolute post-ReLU hidden activation; deterministic unit-index tie break",
            "selected_units": selected_units,
            "held_out_outcome_used": False,
            "selection_frozen_before_evaluation": True,
        },
        "requirement_evidence": {
            "candidate_layer": "single shared hidden layer",
            "intervention_site": "post-ReLU hidden activation",
            "directed_hidden_to_hidden_path": False,
            "canonical_requirement_semantics": (
                "selection closure: selecting one candidate may require another to close "
                "an operator/seam compatibility condition"
            ),
            "canonical_requirement_is_causal_path_claim": False,
            "same_layer_pair_ablations_pay_direction": False,
            "direction_unpaid_reason": (
                "the symmetric singleton/joint pair-ablation surface does not identify "
                "which directed closure requirement holds"
            ),
            "boundary": (
                "Absence of a hidden-to-hidden wire is architecture context, not the "
                "definition of gluingRequirement. The payment failure is informational: "
                "the observed pair-ablation surface cannot distinguish opposite directed "
                "selection-closure worlds."
            ),
        },
        "evaluation": {
            "carrier": "held-out test split",
            "baseline_test_loss": baseline_test_loss,
            "effect_orientation": "larger held-out loss is worse",
            "canonical_damage_scale": LOSS_DAMAGE_SCALE,
            "canonical_damage_rule": "max(0, round(loss_increase * scale))",
            "singleton_effects": [
                {
                    "unit": unit,
                    "loss_increase": singleton_effects[unit],
                    "damage_microunits": canonical_damage_microunits(
                        singleton_effects[unit]
                    ),
                }
                for unit in selected_units
            ],
            "pair_effects": pairs,
        },
        "promotion": {
            "raw_interventions_measured": True,
            "nat_damage_adapter_paid": True,
            "requirement_edges_paid": False,
            "relation_classification_paid": False,
            "beta_maximality_paid": False,
            "grokking_mechanism_paid": False,
        },
        "non_promotion_boundary": (
            "Raw singleton/joint ablation effects and their orientation-aware Nat damage "
            "adapter are observation receipts. The symmetric pair surface does not identify "
            "directed gluing-requirement closure. It does not by itself establish a complete "
            "relation graph, closed-compatible beta, or Grokking mechanism identity."
        ),
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


def run_interventions(
    checkpoint_path: Path, candidate_count: int, receipt_path: Path | None = None
) -> dict[str, Any]:
    try:
        import torch
        from torch import nn
    except ImportError as exc:  # pragma: no cover - environment-dependent boundary
        raise RuntimeError("PyTorch is required to evaluate checkpoint interventions") from exc

    checkpoint = torch.load(checkpoint_path, map_location="cpu", weights_only=False)
    config = Mod97RunConfig(**checkpoint["config"])
    if checkpoint.get("historical_receipt_same_run") is not False:
        raise ValueError("checkpoint must explicitly deny historical same-run promotion")
    if checkpoint.get("historical_receipt_same_configuration") is not False:
        raise ValueError("checkpoint must explicitly deny historical same-configuration promotion")

    class SharedEmbeddingMLP(nn.Module):
        def __init__(self) -> None:
            super().__init__()
            self.embedding = nn.Embedding(MODULUS, config.embedding_dim)
            self.hidden = nn.Linear(2 * config.embedding_dim, config.hidden_dim)
            self.output = nn.Linear(config.hidden_dim, MODULUS)

        def hidden_state(self, left, right):
            joined = torch.cat((self.embedding(left), self.embedding(right)), dim=-1)
            return torch.relu(self.hidden(joined))

        def logits_from_hidden(self, hidden):
            return self.output(hidden)

    model = SharedEmbeddingMLP().cpu()
    model.load_state_dict(checkpoint["model_state_dict"])
    model.eval()

    pairs, targets = _all_pairs()
    train_indices, test_indices = deterministic_split_indices(
        TOTAL_PAIRS, TRAINING_PAIRS, config.split_seed
    )

    def tensorize(indices: list[int]):
        left = torch.tensor([pairs[i][0] for i in indices], dtype=torch.long)
        right = torch.tensor([pairs[i][1] for i in indices], dtype=torch.long)
        y = torch.tensor([targets[i] for i in indices], dtype=torch.long)
        return left, right, y

    train_left, train_right, _ = tensorize(train_indices)
    test_left, test_right, test_y = tensorize(test_indices)
    criterion = nn.CrossEntropyLoss()

    with torch.no_grad():
        training_hidden = model.hidden_state(train_left, train_right)
    selected_units = select_candidates_from_training(
        training_hidden.tolist(), candidate_count
    )

    with torch.no_grad():
        test_hidden = model.hidden_state(test_left, test_right)
        baseline_test_loss = float(
            criterion(model.logits_from_hidden(test_hidden), test_y).item()
        )

    def ablated_loss(units: tuple[int, ...]) -> float:
        with torch.no_grad():
            hidden = test_hidden.clone()
            hidden[:, list(units)] = 0.0
            return float(criterion(model.logits_from_hidden(hidden), test_y).item())

    singleton_effects: dict[int, float] = {}
    for unit in selected_units:
        singleton_effects[unit] = ablated_loss((unit,)) - baseline_test_loss

    pair_effects: dict[tuple[int, int], float] = {}
    for i, left in enumerate(selected_units):
        for right in selected_units[i + 1 :]:
            pair_effects[(left, right)] = (
                ablated_loss((left, right)) - baseline_test_loss
            )

    receipt = build_intervention_receipt(
        checkpoint_path=str(checkpoint_path),
        checkpoint_sha256=_sha256(checkpoint_path),
        selected_units=selected_units,
        baseline_test_loss=baseline_test_loss,
        singleton_effects=singleton_effects,
        pair_effects=pair_effects,
    )
    receipt["producer_sha256"] = _sha256(Path(__file__))
    receipt["checkpoint"]["epoch"] = checkpoint["epoch"]
    receipt["checkpoint"]["historical_receipt_same_run"] = False
    receipt["checkpoint"]["historical_receipt_same_configuration"] = False
    receipt["selection"]["candidate_count"] = candidate_count
    receipt["selection"]["hidden_width"] = config.hidden_dim

    text = json.dumps(receipt, indent=2, sort_keys=True)
    if receipt_path is not None:
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(text + "\n", encoding="utf-8")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--candidate-count", type=int, default=12)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    receipt = run_interventions(args.checkpoint, args.candidate_count, args.receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
