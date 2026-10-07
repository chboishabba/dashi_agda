#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def b(x: bool) -> str:
    return "true" if x else "false"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: render_twob_char2_extension_runtime_certificate.py "
            "<duad-stable.json> <fi22-natural.json> <output.agda>"
        )

    duad_path = Path(sys.argv[1])
    fi22_path = Path(sys.argv[2])
    out = Path(sys.argv[3])
    duad = json.loads(duad_path.read_text())
    fi22 = json.loads(fi22_path.read_text())
    out.parent.mkdir(parents=True, exist_ok=True)

    quotient_dim = duad["selected_upper_dimension"] - duad["selected_lower_dimension"]
    duad_paid = bool(duad["finite_duad_same_quotient_Bprime_Cprime_paid"])
    fi22_paid = bool(fi22["finite_source_native_completion10_module_identified"])

    module = f'''module DASHI.Moonshine.Generated.TwoBChar2ExtensionRuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT: CHARACTERISTIC-TWO EXTENSION MAX-CUT
--
-- Input 1: explicit MeatAxe composition series for the M22:2 restriction of
--          the M24 duad-276 permutation module.  A selected N<=S chain and
--          quotient action are retained in the JSON artifact.
-- Input 2: ATLAS Fi22:2 maximal subgroup 2^10:M22:2, with the conjugation
--          action on the normal elementary-abelian 2^10 kernel.
--
-- This certificate records finite/source-native module facts only.  It does
-- NOT identify either finite ten-space with the actual Monster 2B Tate head.
------------------------------------------------------------------------

duadReceiptSha256 : String
duadReceiptSha256 = "{sha256(duad_path)}"

fi22ReceiptSha256 : String
fi22ReceiptSha256 = "{sha256(fi22_path)}"

duadAmbientDimension : Nat
duadAmbientDimension = {duad['dimension']}

duadCompositionFactorCount : Nat
duadCompositionFactorCount = {len(duad['factor_dimensions'])}

duadTenFactorCount : Nat
duadTenFactorCount = {duad['ten_factor_count']}

selectedSeriesFactorIndex : Nat
selectedSeriesFactorIndex = {duad['selected_factor_index']}

selectedLowerDimension : Nat
selectedLowerDimension = {duad['selected_lower_dimension']}

selectedUpperDimension : Nat
selectedUpperDimension = {duad['selected_upper_dimension']}

selectedQuotientDimension : Nat
selectedQuotientDimension = {quotient_dim}

selectedOuterJ2x5MatchCount : Nat
selectedOuterJ2x5MatchCount = {duad['selected_outer_J2x5_match_count']}

finiteDuadSameQuotientBprimeCprimePaid : Bool
finiteDuadSameQuotientBprimeCprimePaid = {b(duad_paid)}

selectedQuotientDimensionIsTen : selectedQuotientDimension ≡ 10
selectedQuotientDimensionIsTen = refl

fi22d2NormalKernelOrder : Nat
fi22d2NormalKernelOrder = {fi22['normal_kernel_order']}

fi22d2NaturalModuleDimension : Nat
fi22d2NaturalModuleDimension = {fi22['natural_module_dimension']}

fi22d2AtlasTenMatchCount : Nat
fi22d2AtlasTenMatchCount = {len(fi22['atlas_m22d2_10d_matches'])}

fi22d2OuterJ2x5MatchCount : Nat
fi22d2OuterJ2x5MatchCount = {fi22['outer_J2x5_match_count']}

finiteSourceNativeCompletion10DonorPaid : Bool
finiteSourceNativeCompletion10DonorPaid = {b(fi22_paid)}

fi22d2NaturalModuleDimensionIsTen : fi22d2NaturalModuleDimension ≡ 10
fi22d2NaturalModuleDimensionIsTen = refl

-- Same-object promotion firewall: neither finite receipt constructs the actual
-- characteristic-two Tate extension chain.
actualTwoBTateStableSubquotientPaid : Bool
actualTwoBTateStableSubquotientPaid = false

actualTwoBTateOuterActionOnSameQPaid : Bool
actualTwoBTateOuterActionOnSameQPaid = false
'''

    out.write_text(module)


if __name__ == "__main__":
    main()
