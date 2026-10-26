# Local fail-closed JSON quote helper for SOURCE ATLAS character labels.
# Preserve the original CTblLib label verbatim after correct JSON escaping.
# NOT a character-table algorithm, a source-authentication claim, or
# a replacement for GAP's optional json package.
#
# ATLAS short labels are expected to contain printable ASCII, possibly
# with GAP backslashes (e.g. \chi_{1,0}). A non-ASCII byte or a control
# character fails rather than emitting malformed or misleading JSON.
#
# Original label data: ATLAS / CTblLib. This formatting utility: DASHI.

Monster3BSourceJSONQuotedLabel := function(s)
  local c, escaped;
  if not IsString(s) then
    Error("source ATLAS label is not a string");
  fi;
  for c in s do
    if IntChar(c) < 32 or IntChar(c) > 126 then
      Error("source ATLAS label contains a non-printable/non-ASCII byte");
    fi;
  od;
  escaped := ReplacedString(s, "\\", "\\\\");
  escaped := ReplacedString(escaped, "\"", "\\\"");
  return Concatenation("\"", escaped, "\"");
end;

# Exact serialisation of one original GAP cyclotomic source value.
# The mathematical value and CoeffsCyc are owned by GAP/CTblLib, and
# its conductor is retained without approximating to Q(zeta_3).
Monster3BSourceJSONCyclotomic := function(x)
  local n, coeff, rebuilt, out, j;
  n := Conductor(x);
  if not IsInt(n) or n < 1 or n > 4096 then
    Error("cyclotomic source conductor exceeds exact checker limit");
  fi;
  coeff := CoeffsCyc(x,n);
  if coeff = fail or Length(coeff) <> n then
    Error("incomplete exact GAP cyclotomic coordinates");
  fi;
  rebuilt := Sum([1..n], j -> coeff[j] * E(n)^(j-1));
  if rebuilt <> x then
    Error("GAP cyclotomic record did not reconstruct exact source value");
  fi;
  out := Concatenation("{\"conductor\":",String(n),",\"coefficients\":[");
  for j in [1..n] do
    if j > 1 then Append(out,","); fi;
    if not IsRat(coeff[j]) then
      Error("non-rational GAP coefficient in cyclotomic expansion");
    fi;
    Append(out,Monster3BSourceJSONQuotedLabel(String(coeff[j])));
  od;
  Append(out,"]}");
  return out;
end;
