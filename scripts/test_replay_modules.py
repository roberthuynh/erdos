#!/usr/bin/env python3
"""Check replay enumeration and failure propagation without mathematical execution."""
import subprocess
import unittest
from unittest.mock import Mock, patch

from replay_modules import replay


class ReplayChecks(unittest.TestCase):
    @patch('replay_modules.check_coverage', return_value={'First': None, 'Second': None})
    def test_replays_every_configured_module(self, coverage):
        run = Mock()
        self.assertEqual(replay(run=run), 2)
        self.assertEqual(run.call_count, 2)
        self.assertIn('"First"', run.call_args_list[0].kwargs['input'])
        self.assertIn('"Second"', run.call_args_list[1].kwargs['input'])
        self.assertTrue(all(call.kwargs['check'] for call in run.call_args_list))

    @patch('replay_modules.check_coverage', return_value={'First': None, 'Second': None})
    def test_first_failure_cannot_be_hidden_by_later_success(self, coverage):
        run = Mock(side_effect=[subprocess.CalledProcessError(1, 'lake'), None])
        with self.assertRaises(subprocess.CalledProcessError):
            replay(run=run)
        self.assertEqual(run.call_count, 1)

    @patch('replay_modules.check_coverage', side_effect=ValueError('enumeration failed'))
    def test_enumeration_failure_runs_nothing(self, coverage):
        run = Mock()
        with self.assertRaisesRegex(ValueError, 'enumeration failed'):
            replay(run=run)
        run.assert_not_called()

    @patch('replay_modules.check_coverage', return_value={})
    def test_empty_enumeration_rejected(self, coverage):
        run = Mock()
        with self.assertRaisesRegex(ValueError, 'nonempty'):
            replay(run=run)
        run.assert_not_called()

    @patch('replay_modules.check_coverage', return_value={'First': None, 'Second': None})
    def test_unknown_and_duplicate_selections_rejected(self, coverage):
        for selected in [[], ['Unknown'], ['First', 'First']]:
            run = Mock()
            with self.subTest(selected=selected), self.assertRaises(ValueError):
                replay(selected=selected, run=run)
            run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
