from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = ROOT / "vendor" / "meta-introspector-aok-goldbach29.VENDOR"


def main():
    text = PIN.read_text()
    assert "goldbach29_program_blob: ff3f10a3e4c72771ac415a7f4bfb70a209478025" in text
    assert "goldbach30_program_blob: ff748e1d68bf01d19e0c0998f6ac8d3a1c73e2f3" in text
    assert "rules 1 through 25 are identical annotated rules" in text
    assert "Goldbach30 rule 27 is NT.B[b,c] -> RA.A[a,d^2,f]" in text
    assert "Goldbach29 rule 28 is the same failure rule" in text
    assert "all post-prefix differences are confined to the success routing" in text
    assert "exact DASHI macro contract therefore fixes s=0, g=0 and verdict f=1" in text
    assert "c may be zero on entry" in text
    assert "arbitrary f>1 is intentionally excluded" in text
    print("vendor blob/tail-delta provenance regression: OK")


if __name__ == "__main__":
    main()
