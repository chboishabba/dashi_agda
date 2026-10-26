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
