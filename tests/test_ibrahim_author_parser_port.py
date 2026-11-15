"""Author parser-behaviour synthetic fixture reconstruction, not dump replay."""
from __future__ import annotations
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'scripts'))
import ibrahim_author_parser_port as port

class AuthorPortTests(unittest.TestCase):
    def test_outer_first_link_and_source_span(self):
        text='Plain [[Science|scientific method]], next [[Philosophy]].'
        out=port.reference_first_qualifying_link(text)
        self.assertEqual(out['selected_target'],'Science')
        a,b=out['selected_span'];self.assertEqual(text[a:b],'[[Science|scientific method]]')
    def test_nested_template_parentheses_and_reference_exclusions(self):
        text='{{note|[[TemplateChoice]]}} ([[Parenthetical]]) <ref>[[Reference]]</ref> [[Real]]'
        self.assertEqual(port.reference_first_qualifying_link(text)['selected_target'],'Real')
    def test_false_links_are_substring_based_not_prefix_only(self):
        # This oddity is *in the original producer*; do not silently fix it.
        text='[[Valid|talk: caption]] [[Other]]'
        self.assertEqual(port.reference_first_qualifying_link(text)['selected_target'],'Other')
    def test_exact_author_namespace_blacklist(self):
        text='[[File:Image]] [[Category:Book]] [[Real]]'
        self.assertEqual(port.reference_first_qualifying_link(text)['selected_target'],'Real')
    def test_italics_not_special_in_original_text_parser(self):
        text="''[[Italic]]'' [[Normal]]"
        self.assertEqual(port.reference_first_qualifying_link(text)['selected_target'],'Italic')
    def test_no_qualifying_link_returns_unknown_not_philosophy(self):
        self.assertIsNone(port.reference_first_qualifying_link('{{x|[[Hidden]]}}'))
    def test_div_ref_and_nested_paren(self):
        text='<div>[[Div]]</div> (([[Parenthetical]])) [[After]]'
        self.assertEqual(port.reference_first_qualifying_link(text)['selected_target'],'After')

if __name__=='__main__':unittest.main()
