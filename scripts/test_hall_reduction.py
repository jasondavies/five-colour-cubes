"""Check preservation of the Hall-failure disjunction when pruning cuts."""
import itertools
import unittest
from generate_five_colour_reduced import undominated


class HallReductionTests(unittest.TestCase):
    def test_subsumption_direction(self):
        cuts = {(0,): 1, (0, 1): 1, (1,): 0}
        retained, witness = undominated(cuts)
        self.assertEqual(set(retained), {(0,), (1,)})
        self.assertEqual(witness[(0, 1)], (0,))
        # Subset alone is insufficient when its RHS is smaller.
        self.assertEqual(set(undominated({(0,): 0, (0, 1): 1})[0]), {(0,), (0, 1)})

    def test_disjunction_and_coverage(self):
        candidates = [(tuple(i for i in range(3) if mask >> i & 1), rhs)
                      for mask in range(8) for rhs in range(3)]
        # Exercise interacting three-cut families and every small assignment.
        for alternatives in itertools.combinations(candidates, 3):
            merged = {}
            for mask, rhs in alternatives:
                merged[mask] = max(rhs, merged.get(mask, -1))
            retained, witnesses = undominated(merged)
            for original, replacement in witnesses.items():
                self.assertIn(replacement, retained)
                self.assertLessEqual(set(replacement), set(original))
                self.assertGreaterEqual(merged[replacement], merged[original])
            for counts in itertools.product(range(4), repeat=3):
                before = any(sum(counts[i] for i in m) <= rhs for m, rhs in alternatives)
                after = any(sum(counts[i] for i in m) <= merged[m] for m in retained)
                self.assertEqual(before, after, (alternatives, counts))

    def test_empty_family(self):
        self.assertEqual(undominated({}), ([], {}))


if __name__ == '__main__':
    unittest.main()
