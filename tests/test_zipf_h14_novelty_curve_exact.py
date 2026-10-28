"""H14 exact complete-Heaps-curve injection and H15 identity boundary.

Finite independent word/flag checks. Agda source-written, not kernel-checked.
Original Heaps/Herdan/temporal research priority preserved; repository test
Johl Brown with OpenAI ChatGPT assistance, 28 October 2026.
"""
from itertools import product
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from zipf_heaps_bridge import observed_prefix_diversity, novelty_flags


def curve_from_flags(flags, start=0):
    if type(start) is not int or start < 0:
        raise ValueError('valid nonnegative starting vocabulary required')
    n=start
    result=[n]
    for flag in flags:
        if type(flag) is not bool:
            raise ValueError('novelty flags must be boolean')
        n += int(flag)
        result.append(n)
    return tuple(result)


def test_prefix_curve_is_injective_for_every_binary_word_up_to_ten():
    for start in range(5):
        for length in range(11):
            flags_space=product((False,True),repeat=length)
            curves={curve_from_flags(flags,start) for flags in flags_space}
            assert len(curves)==2**length


def test_actual_word_heaps_curve_equals_curve_of_novelty_events():
    for alphabet in range(1,4):
        for n in range(7):
            for word in product(range(alphabet),repeat=n):
                assert observed_prefix_diversity(word)==curve_from_flags(novelty_flags(word))


def test_same_terminal_vocabulary_does_not_determine_full_curve():
    a,b=(True,False,True),(True,True,False)
    assert curve_from_flags(a)[-1]==curve_from_flags(b)[-1]==2
    assert curve_from_flags(a)!=curve_from_flags(b)


def test_complete_curve_identifies_novelty_but_not_repeated_label():
    a,b=(0,1,0,2,1),(0,1,1,2,0)
    curve=observed_prefix_diversity(a)
    assert curve==observed_prefix_diversity(b)
    assert curve==curve_from_flags((True,True,False,True,False))
    assert novelty_flags(a)==novelty_flags(b)
    assert a[2]!=b[2]


def test_invalid_flags_and_start_are_not_silently_coerced():
    for start in (-1,True,0.2):
        try:
            curve_from_flags((),start)
        except ValueError:
            pass
        else:
            assert False
    for flags in ((0,), (1,), (None,), ('true',), (True,1)):
        try:
            curve_from_flags(flags)
        except ValueError:
            pass
        else:
            assert False


def test_h14_h15_agda_source_preserves_two_distinct_theorem_boundaries():
    h14=(ROOT/'DASHI/Statistics/ZipfNoveltyCurveInjectiveExact.agda').read_text()
    h15=(ROOT/'DASHI/Statistics/ZipfFullHeapsCurveIdentityNoGoExact.agda').read_text()
    umbrella=(ROOT/'DASHI/Statistics/ZipfFamilyEverything.agda').read_text()
    assert 'curveFromFlagsInjective' in h14
    assert 'zeroBasedFlagsInjective' in h14
    assert 'fullCurveCannotRecoverRepeatedIdentity' in h15
    assert 'leftCurveIsFlagCurve' in h15
    assert 'Novelty.curveFromZero witnessFlags' in h15
    assert 'import DASHI.Statistics.ZipfNoveltyCurveInjectiveExact' in umbrella
    for agda in (h14,h15):
        assert '{!!}' not in agda
        assert 'postulate\n' not in agda
        assert 'allow-unsolved-metas' not in agda
