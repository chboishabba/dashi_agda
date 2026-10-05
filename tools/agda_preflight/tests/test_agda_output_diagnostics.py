from pathlib import Path

from agda_preflight.scope_backend import parse_agda_diagnostics


def test_parses_named_warning_with_multiline_body():
    output = """\
/repo/DASHI/Physics/Foundations/SmithChartMobiusMatrixExact.agda:130.11-21: warning: -W[no]RewritesNothing
`rewrite' did not apply
when checking that the clause
foo = refl
has type Bar
"""

    diagnostics = parse_agda_diagnostics(output)

    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.path == Path("/repo/DASHI/Physics/Foundations/SmithChartMobiusMatrixExact.agda")
    assert (diag.line, diag.column) == (130, 11)
    assert diag.severity == "warning"
    assert diag.agda_class == "RewritesNothing"
    assert diag.code == "TSAGDA301"
    assert "`rewrite' did not apply" in diag.message
    assert "has type Bar" in diag.message


def test_parses_user_warning_deprecation_from_vendor():
    output = """\
/repo/vendor/bishop/Sequence.agda:2206.62-73: warning: -W[no]UserWarning
Warning: ↥[p/q]≡p was deprecated in v2.0.
Please use ↥[n/d]≡n instead.
when scope checking ℚP.↥[p/q]≡p
"""

    diagnostics = parse_agda_diagnostics(output)

    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.code == "TSAGDA302"
    assert diag.agda_class == "UserWarning"
    assert diag.severity == "warning"
    assert "deprecated in v2.0" in diag.message
    assert "↥[n/d]≡n" in diag.message
    assert "/vendor/" in str(diag.path)


def test_parses_pattern_shadow_warning():
    output = """\
/repo/DASHI/Physics/Closure/NSTriadKNPhysicalTriadEnumeration.agda:159.11-15: warning: -W[no]PatternShadowsConstructor
The pattern variable pair has the same name as the constructor
Cube.pair
when checking the clause left hand side
pairTriad pair
"""

    diagnostics = parse_agda_diagnostics(output)

    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.code == "TSAGDA300"
    assert diag.agda_class == "PatternShadowsConstructor"
    assert "Cube.pair" in diag.message


def test_parses_bracketed_agda_error():
    output = """\
/repo/DASHI/Moonshine/JInvariant369ModularLevelCuspObserversExact.agda:1003.51: error: [ParseError]
in the name reflectionIdentifiedWithCuspInversionAt3_9_27, the part 9 is not valid because it is a literal
Agda failed for: DASHI/Moonshine/OggSSP2BSameObjectMaxCutFrontierExact.agda
"""

    diagnostics = parse_agda_diagnostics(output)

    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.path == Path("/repo/DASHI/Moonshine/JInvariant369ModularLevelCuspObserversExact.agda")
    assert (diag.line, diag.column) == (1003, 51)
    assert diag.severity == "error"
    assert diag.agda_class == "ParseError"
    assert diag.code == "TSAGDA390"
    assert "part 9 is not valid" in diag.message
    assert "Agda failed for:" not in diag.message


def test_unknown_named_warning_gets_generic_native_warning_code():
    output = """\
/repo/DASHI/Foo.agda:7.2-4: warning: -W[no]FutureWarningClass
future warning body
"""

    diagnostics = parse_agda_diagnostics(output)

    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.code == "TSAGDA399"
    assert diag.agda_class == "FutureWarningClass"
    assert diag.message == "future warning body"


def test_multiple_diagnostics_do_not_absorb_checking_progress_lines():
    output = """\
( 804/1034) Checking DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact (/repo/DASHI/Mathematics/NumberTheory/FiniteProductEnumerationExact.agda).
/repo/vendor/bishop/Sequence.agda:1259.51-62: warning: -W[no]UserWarning
Warning: <-transʳ was deprecated in v2.0. Please use ≤-<-trans instead.
when scope checking ℕP.<-transʳ
( 848/1034) Checking DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact (/repo/DASHI/Moonshine/Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact.agda).
/repo/DASHI/Moonshine/JInvariant369ModularLevelCuspObserversExact.agda:1003.51: error: [ParseError]
bad literal in name
"""

    diagnostics = parse_agda_diagnostics(output)

    assert [diag.code for diag in diagnostics] == ["TSAGDA302", "TSAGDA390"]
    assert diagnostics[0].message.endswith("ℕP.<-transʳ")
    assert "Checking DASHI" not in diagnostics[0].message
