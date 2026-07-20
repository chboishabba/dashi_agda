#!/usr/bin/env python3
"""Executable reference for the bounded DASHI DNA production channel.

This file intentionally keeps three layers distinct:

1. finite biochemical-policy state and legal-base enumeration;
2. reversible mixed-radix payload mapping (bits <-> legal DNA);
3. a byte-normalized arithmetic coder for the state-dependent rank stream.

The benchmark emits a JSON receipt. It is empirical evidence, not an Agda proof.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import math
import os
import random
import time
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Iterable, Sequence

BASES = ("A", "C", "G", "T")
COMPLEMENT = {"A": "T", "T": "A", "C": "G", "G": "C"}
FORBIDDEN4 = {"GATC", "CTAG"}
MAX_RUN = 3
MIN_DEBT = -2
MAX_DEBT = 2
HAIRPIN_STEM = 3
HAIRPIN_LOOP = 4


@dataclasses.dataclass(frozen=True, slots=True)
class State:
    previous: str | None = None
    run: int = 0
    debt: int = 0
    history: str = ""

    def key(self) -> tuple[str | None, int, int, str]:
        return self.previous, self.run, self.debt, self.history


def is_gc(base: str) -> bool:
    return base in "CG"


def next_debt(debt: int, base: str) -> int:
    return debt + (1 if is_gc(base) else -1)


def completes_hairpin(history: str, base: str) -> bool:
    # left stem (3), loop (4), right stem prefix (2), candidate (1)
    if len(history) < HAIRPIN_STEM + HAIRPIN_LOOP + HAIRPIN_STEM - 1:
        return False
    window = history[-(HAIRPIN_STEM + HAIRPIN_LOOP + HAIRPIN_STEM - 1) :]
    left = window[:HAIRPIN_STEM]
    right = window[-(HAIRPIN_STEM - 1) :] + base
    return right == "".join(COMPLEMENT[b] for b in reversed(left))


def legal(state: State, base: str) -> bool:
    if base not in BASES:
        return False
    if state.previous == base and state.run >= MAX_RUN:
        return False
    debt = next_debt(state.debt, base)
    if not (MIN_DEBT <= debt <= MAX_DEBT):
        return False
    if (state.history + base)[-4:] in FORBIDDEN4:
        return False
    if completes_hairpin(state.history, base):
        return False
    return True


def step(state: State, base: str) -> State:
    if not legal(state, base):
        raise ValueError(f"illegal base {base!r} from {state}")
    run = state.run + 1 if state.previous == base else 1
    history = (state.history + base)[-9:]
    return State(base, run, next_debt(state.debt, base), history)


def legal_bases(state: State) -> tuple[str, ...]:
    return tuple(base for base in BASES if legal(state, base))


@lru_cache(maxsize=None)
def completion_count(horizon: int, state: State) -> int:
    """Exact horizon-indexed completion table entry."""
    if horizon < 0:
        raise ValueError("horizon must be non-negative")
    if horizon == 0:
        return 1
    return sum(completion_count(horizon - 1, step(state, b)) for b in legal_bases(state))


def viable_bases(state: State, horizon: int) -> tuple[str, ...]:
    if horizon <= 0:
        return legal_bases(state)
    return tuple(
        b
        for b in legal_bases(state)
        if completion_count(horizon - 1, step(state, b)) > 0
    )


@dataclasses.dataclass(frozen=True, slots=True)
class PayloadFrame:
    bit_length: int
    symbol_count: int
    final_state: int


def payload_to_dna(payload: bytes, *, horizon: int = 8) -> tuple[str, PayloadFrame]:
    """Map payload bytes to legal DNA using a sentinel mixed-radix ANS state.

    The sentinel preserves leading zero bytes. Arity-one transitions emit forced
    bases without consuming state; a horizon table prevents entering dead ends.
    """
    bit_length = len(payload) * 8
    value = int.from_bytes(payload, "big")
    ans_state = (1 << bit_length) | value
    state = State()
    out: list[str] = []
    forced_without_progress = 0

    while ans_state != 1:
        choices = viable_bases(state, horizon)
        arity = len(choices)
        if arity == 0:
            raise RuntimeError("constraint machine reached a dead state")
        if arity == 1:
            digit = 0
            forced_without_progress += 1
            if forced_without_progress > 64:
                raise RuntimeError("more than 64 forced transitions without payload progress")
        else:
            digit = ans_state % arity
            ans_state //= arity
            forced_without_progress = 0
        base = choices[digit]
        out.append(base)
        state = step(state, base)

    return "".join(out), PayloadFrame(bit_length, len(out), ans_state)


def dna_to_payload(dna: str, frame: PayloadFrame, *, horizon: int = 8) -> bytes:
    if len(dna) != frame.symbol_count:
        raise ValueError("symbol count does not match frame")
    state = State()
    digits: list[tuple[int, int]] = []
    for base in dna:
        choices = viable_bases(state, horizon)
        try:
            digit = choices.index(base)
        except ValueError as exc:
            raise ValueError(f"illegal DNA symbol {base!r} from {state}") from exc
        digits.append((len(choices), digit))
        state = step(state, base)

    ans_state = 1
    for arity, digit in reversed(digits):
        if arity > 1:
            ans_state = ans_state * arity + digit

    sentinel = 1 << frame.bit_length
    if not (sentinel <= ans_state < sentinel * 2):
        raise ValueError("decoded state does not contain the expected sentinel")
    value = ans_state - sentinel
    return value.to_bytes((frame.bit_length + 7) // 8, "big")


# ---------------------------------------------------------------------------
# Byte-normalized arithmetic coder for the legal-rank stream.

TOP = 1 << 32
HALF = TOP >> 1
QUARTER = HALF >> 1
THREE_QUARTER = QUARTER * 3


class BitWriter:
    def __init__(self) -> None:
        self.bits: list[int] = []

    def write(self, bit: int) -> None:
        self.bits.append(bit & 1)

    def to_bytes(self) -> bytes:
        out = bytearray((len(self.bits) + 7) // 8)
        for i, bit in enumerate(self.bits):
            out[i // 8] |= bit << (7 - (i % 8))
        return bytes(out)


class BitReader:
    def __init__(self, data: bytes) -> None:
        self.data = data
        self.index = 0

    def read(self) -> int:
        if self.index >= len(self.data) * 8:
            self.index += 1
            return 0
        bit = (self.data[self.index // 8] >> (7 - self.index % 8)) & 1
        self.index += 1
        return bit


@dataclasses.dataclass(slots=True)
class ArithmeticStats:
    renormalizations: int = 0
    pending_flushes: int = 0
    symbols: int = 0


class ArithmeticEncoder:
    def __init__(self) -> None:
        self.low = 0
        self.high = TOP - 1
        self.pending = 0
        self.writer = BitWriter()
        self.stats = ArithmeticStats()

    def _emit(self, bit: int) -> None:
        self.writer.write(bit)
        opposite = bit ^ 1
        while self.pending:
            self.writer.write(opposite)
            self.pending -= 1
            self.stats.pending_flushes += 1

    def encode_uniform(self, rank: int, arity: int) -> None:
        if not 1 <= arity <= 4 or not 0 <= rank < arity:
            raise ValueError("invalid uniform symbol")
        width = self.high - self.low + 1
        new_low = self.low + (width * rank) // arity
        new_high = self.low + (width * (rank + 1)) // arity - 1
        self.low, self.high = new_low, new_high
        self.stats.symbols += 1

        while True:
            if self.high < HALF:
                self._emit(0)
            elif self.low >= HALF:
                self._emit(1)
                self.low -= HALF
                self.high -= HALF
            elif self.low >= QUARTER and self.high < THREE_QUARTER:
                self.pending += 1
                self.low -= QUARTER
                self.high -= QUARTER
            else:
                break
            self.low = self.low * 2
            self.high = self.high * 2 + 1
            self.stats.renormalizations += 1
            assert 0 <= self.low <= self.high < TOP

    def finish(self) -> tuple[bytes, int, ArithmeticStats]:
        self.pending += 1
        self._emit(0 if self.low < QUARTER else 1)
        return self.writer.to_bytes(), len(self.writer.bits), self.stats


class ArithmeticDecoder:
    def __init__(self, data: bytes) -> None:
        self.low = 0
        self.high = TOP - 1
        self.reader = BitReader(data)
        self.code = 0
        self.renormalizations = 0
        for _ in range(32):
            self.code = (self.code << 1) | self.reader.read()

    def decode_uniform(self, arity: int) -> int:
        if not 1 <= arity <= 4:
            raise ValueError("invalid arity")
        width = self.high - self.low + 1
        scaled = ((self.code - self.low + 1) * arity - 1) // width
        rank = min(arity - 1, scaled)
        new_low = self.low + (width * rank) // arity
        new_high = self.low + (width * (rank + 1)) // arity - 1
        self.low, self.high = new_low, new_high

        while True:
            if self.high < HALF:
                pass
            elif self.low >= HALF:
                self.low -= HALF
                self.high -= HALF
                self.code -= HALF
            elif self.low >= QUARTER and self.high < THREE_QUARTER:
                self.low -= QUARTER
                self.high -= QUARTER
                self.code -= QUARTER
            else:
                break
            self.low = self.low * 2
            self.high = self.high * 2 + 1
            self.code = self.code * 2 + self.reader.read()
            self.renormalizations += 1
            assert 0 <= self.low <= self.code <= self.high < TOP
        return rank


def arithmetic_encode_dna(dna: str, *, horizon: int = 8) -> tuple[bytes, int, ArithmeticStats]:
    state = State()
    enc = ArithmeticEncoder()
    for base in dna:
        choices = viable_bases(state, horizon)
        enc.encode_uniform(choices.index(base), len(choices))
        state = step(state, base)
    return enc.finish()


def arithmetic_decode_dna(
    encoded: bytes, symbol_count: int, *, horizon: int = 8
) -> tuple[str, int]:
    state = State()
    dec = ArithmeticDecoder(encoded)
    out: list[str] = []
    for _ in range(symbol_count):
        choices = viable_bases(state, horizon)
        rank = dec.decode_uniform(len(choices))
        base = choices[rank]
        out.append(base)
        state = step(state, base)
    return "".join(out), dec.renormalizations


# ---------------------------------------------------------------------------
# Compressive macro summaries and compact invariants.


def macro3(block: str) -> tuple[int, int]:
    if len(block) != 3:
        raise ValueError("macro3 requires three bases")
    gc_mask = sum((1 << i) for i, b in enumerate(block) if is_gc(b))
    phase_parity = sum(b in "TG" for b in block) & 1
    return gc_mask, phase_parity


def macro_stream(dna: str) -> list[tuple[int, int]]:
    return [macro3(dna[i : i + 3]) for i in range(0, len(dna) - 2, 3)]


def crc16_ccitt(data: bytes) -> int:
    crc = 0xFFFF
    for byte in data:
        crc ^= byte << 8
        for _ in range(8):
            crc = ((crc << 1) ^ 0x1021) & 0xFFFF if crc & 0x8000 else (crc << 1) & 0xFFFF
    return crc


def dna_invariant(dna: str) -> dict[str, int | str]:
    packed = bytes("ACGT".index(b) for b in dna)
    return {
        "length": len(dna),
        "crc16": crc16_ccitt(packed),
        "sha256_64": hashlib.sha256(packed).hexdigest()[:16],
    }


def hamming(a: str, b: str) -> int:
    if len(a) != len(b):
        raise ValueError("Hamming distance requires equal lengths")
    return sum(x != y for x, y in zip(a, b))


def benchmark(payload: bytes, *, horizon: int, rounds: int) -> dict[str, object]:
    start = time.perf_counter()
    dna = ""
    frame: PayloadFrame | None = None
    for _ in range(rounds):
        dna, frame = payload_to_dna(payload, horizon=horizon)
    encode_seconds = time.perf_counter() - start
    assert frame is not None

    start = time.perf_counter()
    recovered = b""
    for _ in range(rounds):
        recovered = dna_to_payload(dna, frame, horizon=horizon)
    decode_seconds = time.perf_counter() - start
    assert recovered == payload

    compressed, compressed_bits, astats = arithmetic_encode_dna(dna, horizon=horizon)
    decoded_dna, decoder_renorm = arithmetic_decode_dna(
        compressed, len(dna), horizon=horizon
    )
    assert decoded_dna == dna

    state = State()
    arities: Counter[int] = Counter()
    debt_values: Counter[int] = Counter()
    max_run = 0
    for base in dna:
        choices = viable_bases(state, horizon)
        arities[len(choices)] += 1
        state = step(state, base)
        debt_values[state.debt] += 1
        max_run = max(max_run, state.run)

    # Deterministic single-substitution detection sample for the compact checks.
    mutations = 0
    crc_detected = 0
    hash_detected = 0
    original_inv = dna_invariant(dna)
    for i in range(min(len(dna), 4096)):
        replacement = next(b for b in BASES if b != dna[i])
        mutated = dna[:i] + replacement + dna[i + 1 :]
        inv = dna_invariant(mutated)
        mutations += 1
        crc_detected += inv["crc16"] != original_inv["crc16"]
        hash_detected += inv["sha256_64"] != original_inv["sha256_64"]

    macro_count = len(macro_stream(dna))
    payload_bits = len(payload) * 8
    return {
        "schema": "dashi.dna-production-benchmark.v1",
        "payload_bytes": len(payload),
        "payload_bits": payload_bits,
        "dna_bases": len(dna),
        "payload_bits_per_base": payload_bits / len(dna) if dna else 0.0,
        "arithmetic_bits": compressed_bits,
        "arithmetic_bits_per_base": compressed_bits / len(dna) if dna else 0.0,
        "roundtrip": recovered == payload and decoded_dna == dna,
        "horizon": horizon,
        "completion_cache": completion_count.cache_info()._asdict(),
        "branch_arity_histogram": dict(sorted(arities.items())),
        "debt_histogram": dict(sorted(debt_values.items())),
        "max_homopolymer_run": max_run,
        "forbidden_motifs_present": [m for m in FORBIDDEN4 if m in dna],
        "bounded_hairpins_present": sum(
            completes_hairpin(dna[:i], dna[i]) for i in range(len(dna))
        ),
        "macro3_count": macro_count,
        "macro3_source_bits": macro_count * 6,
        "macro3_summary_bits": macro_count * 4,
        "arithmetic_encoder_renormalizations": astats.renormalizations,
        "arithmetic_decoder_renormalizations": decoder_renorm,
        "single_substitution_samples": mutations,
        "crc16_detected": crc_detected,
        "sha256_64_detected": hash_detected,
        "crc16_collision_bound_per_random_error": "<= 1/65536 under uniform syndrome assumption",
        "sha256_64_collision_bound_per_random_error": "<= 1/2^64 under ideal-hash assumption",
        "encode_seconds": encode_seconds,
        "decode_seconds": decode_seconds,
        "encode_payload_mib_per_second": (len(payload) * rounds / (1024**2)) / encode_seconds,
        "decode_payload_mib_per_second": (len(payload) * rounds / (1024**2)) / decode_seconds,
        "dna_invariant": original_inv,
        "python": os.sys.version,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bytes", type=int, default=4096)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--horizon", type=int, default=8)
    parser.add_argument("--seed", type=int, default=369)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    payload = bytes(rng.randrange(256) for _ in range(args.bytes))
    receipt = benchmark(payload, horizon=args.horizon, rounds=args.rounds)
    text = json.dumps(receipt, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
