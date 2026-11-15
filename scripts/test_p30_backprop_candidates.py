#!/usr/bin/env python3
import unittest
import random
from dataclasses import replace
from itertools import combinations
from p30_backprop_candidates import (
    UNITS30, QUOTE_ASCII, WheelPosition, encode_position, decode_position,
    pack_char, unpack_char, pack_with_crc32, unpack_with_crc32,
    reconstruction_receipt, multiplicative_orders_mod30,
    encode_positions, decode_positions,
)


class CandidateReverseEngineering(unittest.TestCase):
    def test_exact_demo_ascii_length(self):
        self.assertEqual(len(QUOTE_ASCII.encode('ascii')),163)

    def test_phi30_and_unit_orders(self):
        self.assertEqual(len(UNITS30),8)
        orders=multiplicative_orders_mod30()
        self.assertEqual(orders[1],1)
        self.assertEqual(max(orders.values()),4)
        self.assertEqual(sum(1 for x in orders.values() if x==4),4)

    def test_every_byte_in_both_maps_roundtrips(self):
        for map_name in ('natural','gray'):
            for b in range(256):
                p=encode_position(b,map_name)
                self.assertTrue(p.unit in UNITS30 and 0 <= p.depth <32)
                self.assertEqual(decode_position(p,map_name),b)

    def test_each_position_unique_exhaustive(self):
        for name in ('natural','gray'):
            self.assertEqual(len({encode_position(b,name) for b in range(256)}),256)

    def test_both_distinct_mappings(self):
        a=bytes(range(256))
        self.assertNotEqual(pack_char(a,'gray'),pack_char(a,'natural'))
        self.assertEqual(unpack_char(pack_char(a,'gray'),'gray'),a)
        self.assertEqual(unpack_char(pack_char(a,'natural'),'natural'),a)

    def test_both_match_163_489_167_171(self):
        receipt=reconstruction_receipt()
        for item in receipt['candidates'].values():
            self.assertEqual((item['source_fixture_bytes'],
                              item['accounting_stages_three_per_character'],
                              item['char_positions_with_inferred_four_symbol_header'],
                              item['crc_packed_roundtrip_total_bytes']),
                             (163,489,167,171))

    def test_zero_and_random_full_roundtrip(self):
        r=random.Random(20261116)
        corpora=[b'',bytes(163),bytes(range(256)),b'\x00\xff'*163,
                 r.randbytes(1000), 'qutrit\u0394'.encode('utf8')]
        for data in corpora:
            for name in ('natural','gray'):
                self.assertEqual(unpack_char(pack_char(data,name),name),data)
                self.assertEqual(unpack_with_crc32(pack_with_crc32(data,name),name),data)

    def test_char_frame_carries_no_crc_and_valid_fault_mutates_data(self):
        data=QUOTE_ASCII.encode('ascii')
        frame=bytearray(pack_char(data))
        frame[4] ^=1
        changed=unpack_char(bytes(frame))
        self.assertNotEqual(changed,data)
        self.assertEqual(len(changed),len(data))

    def test_crc_detects_each_payload_single_bit_flip(self):
        data=QUOTE_ASCII.encode('ascii')
        frame=pack_with_crc32(data)
        for i in range(8,len(frame)):
            for bit in range(8):
                changed=bytearray(frame)
                changed[i]^=1<<bit
                with self.assertRaisesRegex(ValueError,'integrity'):
                    unpack_with_crc32(bytes(changed))

    def test_crc_does_not_fix_damage(self):
        data=QUOTE_ASCII.encode('ascii')
        frame=bytearray(pack_with_crc32(data));frame[8]^=1
        with self.assertRaises(ValueError):unpack_with_crc32(bytes(frame))

    def test_invalid_lengths_rejected(self):
        data=b'abc'; frame=pack_char(data)
        with self.assertRaises(ValueError):unpack_char(frame[:2])
        with self.assertRaises(ValueError):unpack_char(frame+b'0')
        packed=pack_with_crc32(data)
        with self.assertRaises(ValueError):unpack_with_crc32(packed+b'0')

    def test_invalid_rays_or_depths_rejected(self):
        for p in (WheelPosition(0,1),WheelPosition(2,1),WheelPosition(7,32),WheelPosition(1,-1)):
            with self.assertRaises(ValueError):decode_position(p)

    def test_valid_ray_substitution_undetected_without_crc(self):
        before=encode_position(0)
        modified=WheelPosition(UNITS30[1],before.depth)
        self.assertNotEqual(decode_position(before),decode_position(modified))

    def test_no_intrinsic_redundancy_available(self):
        self.assertEqual(len(UNITS30)*32,256)
        self.assertEqual(len({encode_position(x) for x in range(256)}),256)

    def test_116_mode_not_falsely_solved(self):
        self.assertFalse(reconstruction_receipt()['direct_116_mode_reconstructed'])

    def test_inferred_protocol_mapping_out_of_band(self):
        data=bytes([7,35,100,254])
        gray=pack_char(data,'gray')
        # Decoder has to know variant, otherwise a false *plausible* payload.
        self.assertNotEqual(unpack_char(gray,'natural'),data)


if __name__=='__main__':unittest.main()
