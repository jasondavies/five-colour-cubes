#!/usr/bin/env python3
"""Generated roots preserve checkpoint text while obeying the source-line cap."""
import unittest
from generate_five_colour_enumeration import case_sources, generate_case


class EnumerationSources(unittest.TestCase):
    def source(self, count=12, padding=4):
        namespace = 'FiveColour.Packed.EnumerationChunks.Case7'
        base = ('module\npublic import FiveColour.EnumerationRoot\n'
                '@[expose] public section\nnamespace ' + namespace + '\n'
                'def points : List Nat := []\n')
        blocks = [f'namespace Part{i}\n' + '-- unchanged proof text\n'*padding +
                  f'end Part{i}\n' for i in range(count)]
        footer = ('/-- Every admissible vector in the original root is covered. -/\n'
                  'theorem covered : True := by trivial\nend ' + namespace + '\n')
        return base + ''.join(blocks) + footer, base, blocks, footer

    def test_small_root_is_byte_identical(self):
        text, _, _, _ = self.source(1)
        self.assertEqual(case_sources(7, text), {'Case7.lean': text})

    def test_split_preserves_blocks_and_public_import_chain(self):
        text, base, blocks, footer = self.source()
        sources = case_sources(7, text, limit=30)
        self.assertGreater(len(sources), 2)
        self.assertEqual(sources['Case7/Base.lean'], base +
                         'end FiveColour.Packed.EnumerationChunks.Case7\n')
        previous = 'FiveColour.EnumerationChunks.Case7.Base'
        for name, source in sources.items():
            self.assertLessEqual(len(source.splitlines()), 30)
            self.assertTrue(source.startswith('module\n'))
            if name.endswith('Base.lean'):
                continue
            self.assertIn('public import ' + previous + '\n', source)
            self.assertIn('set_option maxRecDepth 100000\n', source)
            self.assertIn('set_option maxHeartbeats 0\n', source)
            previous = 'FiveColour.EnumerationChunks.' + name[:-5].replace('/', '.')
        joined = ''.join(sources.values())
        for block in blocks:
            self.assertEqual(joined.count(block), 1)
        self.assertTrue(sources['Case7.lean'].endswith(footer))

    def test_empty_root_split_preserves_exclusion_endpoint(self):
        text, _, blocks, _ = self.source()
        text = text.replace('/-- Every admissible vector in the original root is covered. -/',
                            '/-- All empty-root chunks prove exclusion. -/')
        text = text.replace('theorem covered', 'theorem excludes')
        sources = case_sources(7, text, limit=30)
        self.assertIn('theorem excludes', sources['Case7.lean'])
        for block in blocks:
            self.assertEqual(''.join(sources.values()).count(block), 1)

    def test_nonempty_terminal_list_cannot_use_exclusion(self):
        with self.assertRaisesRegex(ValueError, 'terminal points'):
            generate_case(0, None, 0, [[1]], None, None, None, None, exclude=True)

    def test_unsplittable_checkpoint_is_rejected(self):
        text, _, _, _ = self.source(1, padding=40)
        with self.assertRaisesRegex(ValueError, 'exceed'):
            case_sources(7, text, limit=30)

    def test_nonconsecutive_checkpoints_are_rejected(self):
        text, _, _, _ = self.source()
        text = text.replace('namespace Part2\n', 'namespace Part99\n')
        with self.assertRaisesRegex(ValueError, 'nonconsecutive'):
            case_sources(7, text, limit=30)


if __name__ == '__main__':
    unittest.main()
