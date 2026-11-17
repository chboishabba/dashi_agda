#!/usr/bin/env python3
"""Evidence-constrained reverse engineering of P30-shaped codec candidates.

NOT January Walker's original/P30 proprietary implementation.
Three-step operation units here are counted ACCOUNTING STAGES, not actual
machine instructions, energy expenditures, or thermodynamic erasures.

Source: January N. Walker, NISTIR 6025 Information Physics Mapping,
Infoton presentation PDF linked from https://infoton.ai/infoton-p30,
page 28 (phi(30) proposal), page 29 (163/489/167 and size modes).
Author of this candidate implementation: DASHI research integration.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter
from math import log2
from typing import Literal
import struct
import zlib

UNITS30 = (1, 7, 11, 13, 17, 19, 23, 29)
INDEX = {u: i for i, u in enumerate(UNITS30)}
assert len(INDEX) == 8

# ASCII-normalized transcription of visible quotation on PDF slide 29.
# The illustrated slide uses typographic display punctuation; *byte-perfect*
# identity to the original demo's internal input stream is NOT established.
QUOTE_ASCII = (
    "The Great Salt Lake can be fully restored to full health within "
    "as little as 3 years by returning 1,150,000 AF/yr. "
    "Resulting Utah's lake effect and water security."
)
assert len(QUOTE_ASCII.encode('ascii')) == 163

Mapping = Literal['natural', 'gray']


def gray_encode(byte: int) -> int:
    return byte ^ (byte >> 1)


def gray_decode(code: int) -> int:
    n = code
    while code:
        code >>= 1
        n ^= code
    return n


def rank(byte: int, mapping: Mapping) -> int:
    if not 0 <= byte <= 255:
        raise ValueError('unsigned byte needed')
    if mapping == 'natural':
        return byte
    if mapping == 'gray':
        return gray_encode(byte)
    raise ValueError('unknown mapping')


def unrank(code: int, mapping: Mapping) -> int:
    if not 0 <= code <= 255:
        raise ValueError('invalid packed position')
    if mapping == 'natural':
        return code
    if mapping == 'gray':
        return gray_decode(code)
    raise ValueError('unknown mapping')


@dataclass(frozen=True)
class WheelPosition:
    unit: int
    depth: int


def encode_position(byte: int, mapping: Mapping = 'natural') -> WheelPosition:
    # 3 ACCOUNTING STAGES: select mapping; split rank; lookup U(30) ray.
    code = rank(byte, mapping)
    depth, ray = divmod(code, 8)
    return WheelPosition(UNITS30[ray], depth)


def decode_position(pos: WheelPosition, mapping: Mapping = 'natural') -> int:
    if pos.unit not in INDEX or not 0 <= pos.depth < 32:
        raise ValueError('out-of-wheel position')
    return unrank((pos.depth << 3) | INDEX[pos.unit], mapping)


def encode_positions(data: bytes, mapping: Mapping = 'natural') -> tuple[WheelPosition, ...]:
    return tuple(encode_position(b, mapping) for b in data)


def decode_positions(positions: tuple[WheelPosition, ...],
                     mapping: Mapping = 'natural') -> bytes:
    return bytes(decode_position(p, mapping) for p in positions)


def pack_pos(pos: WheelPosition) -> int:
    if pos.unit not in INDEX or not 0 <= pos.depth < 32:
        raise ValueError('not encodable')
    return (pos.depth << 3) | INDEX[pos.unit]


def unpack_pos(byte: int) -> WheelPosition:
    return WheelPosition(UNITS30[byte & 7], byte >> 3)


def pack_char(data: bytes, mapping: Mapping = 'natural') -> bytes:
    """4-byte frame length + one physical byte per wheel position.

    The 4-byte header and mapping are *INFERRED*, not observed. Mapping is
    selected out-of-band; a self-describing format costs more metadata.
    """
    return struct.pack('>I', len(data)) + bytes(
        pack_pos(p) for p in encode_positions(data, mapping))


def unpack_char(frame: bytes, mapping: Mapping = 'natural') -> bytes:
    if len(frame) < 4:
        raise ValueError('missing header')
    size, = struct.unpack('>I', frame[:4])
    if size != len(frame)-4:
        raise ValueError('length mismatch')
    return decode_positions(tuple(unpack_pos(b) for b in frame[4:]), mapping)


def pack_with_crc32(data: bytes, mapping: Mapping = 'natural') -> bytes:
    """4-byte length + 4-byte CRC + wheel positions; not SECDED.

    CRC is an illustrative INFERRED integrity mechanism, not source P30.
    Crucially, CRC verification runs on read and costs operations.
    """
    return (struct.pack('>II', len(data), zlib.crc32(data)) +
            bytes(pack_pos(p) for p in encode_positions(data, mapping)))


def unpack_with_crc32(frame: bytes, mapping: Mapping = 'natural') -> bytes:
    if len(frame) < 8:
        raise ValueError('missing CRC header')
    size, expected_crc = struct.unpack('>II', frame[:8])
    if size != len(frame)-8:
        raise ValueError('length mismatch')
    result = decode_positions(tuple(unpack_pos(b) for b in frame[8:]), mapping)
    if zlib.crc32(result) != expected_crc:
        raise ValueError('payload integrity failure')
    return result


def multiplicative_orders_mod30() -> dict[int, int]:
    orders = {}
    for u in UNITS30:
        current, count = 1, 0
        while True:
            current = current * u % 30
            count += 1
            if current == 1:
                orders[u] = count
                break
    return orders


def entropy_lower_bound_bytes(data: bytes) -> float:
    if not data:
        return 0.0
    counts = Counter(data)
    h = -sum(c / len(data) * log2(c / len(data)) for c in counts.values())
    return len(data) * h / 8


def reconstruction_receipt() -> dict:
    payload = QUOTE_ASCII.encode('ascii')
    candidates = {}
    for mapping in ('natural', 'gray'):
        chars = pack_char(payload, mapping)
        packed = pack_with_crc32(payload, mapping)
        assert unpack_char(chars, mapping) == payload
        assert unpack_with_crc32(packed, mapping) == payload
        candidates[mapping] = {
            'source_fixture_bytes': len(payload),
            'accounting_stages_three_per_character': 3 * len(payload),
            'char_positions_with_inferred_four_symbol_header': len(chars),
            'char_roundtrip_total_bytes': len(chars),
            'crc_packed_roundtrip_total_bytes': len(packed),
            'packed_has_crc_read_verification': True,
            'crc_corrects_bit_errors': False,
            'empty_invalid_positions_in_eight_by_thirtytwo_mapping': 0,
        }
    assert pack_char(payload, 'natural') != pack_char(payload, 'gray')
    return {
        'provenance': 'Two independent constructed candidate encoders; neither original P30',
        'source_reported': {
            'characters': 163, 'encode_operations': 489,
            'char_positions': 167, 'char_roundtrip_bytes': 167,
            'packed_roundtrip_bytes': 171, 'direct_write_only_bytes': 116,
        },
        'wheel_unit_group': UNITS30,
        'unit_group_orders': multiplicative_orders_mod30(),
        'unit_group_structure': 'C2 x C4; not cyclic C8; phi(30)=8',
        'per_position_state_capacity': len(UNITS30)*32,
        'per_position_unused_states': len(UNITS30)*32-256,
        'position_serialization_bits': 8,
        'source_fixture_is_original_byte_exact': False,
        'source_fixture_ascii_bytes': len(payload),
        'source_fixture_shannon_ideal_payload_bytes': round(entropy_lower_bound_bytes(payload), 3),
        'candidates': candidates,
        'counterfactual_original_p30_proved': False,
        'direct_116_mode_reconstructed': False,
        'source_integrity_mechanism_identified': False,
        'physical_energy_or_erasure_savings_measured': False,
        'identifiability': 'At least two distinct reversible encoders match all known count constraints; cannot uniquely infer original map.',
    }


if __name__ == '__main__':
    import json
    print(json.dumps(reconstruction_receipt(), indent=2))
