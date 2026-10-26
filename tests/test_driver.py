import contextlib
import io
import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]


class DriverTests(unittest.TestCase):
    def run_driver(self, status=0, extra_args=()):
        with tempfile.TemporaryDirectory() as directory:
            circuit = Path(directory) / "circuit"
            circuit.mkdir()
            (circuit / "meta.zok.template").write_text(
                (ROOT / "zok/meta.zok.template").read_text()
            )
            output = io.StringIO()
            calls = []

            def prover(command, **kwargs):
                calls.append(command)
                # A real, fast-exiting child exercises buffered output after exit.
                return subprocess.Popen(
                    ["/bin/sh", "-c", f"printf 'first\\nlast\\n'; exit {status}"],
                    **kwargs,
                )

            real_popen = subprocess.Popen

            def launch(command, **kwargs):
                with patch("subprocess.Popen", real_popen):
                    return prover(command, **kwargs)

            converted = [
                subprocess.CompletedProcess([], 0, b"1,2,3,4,5,6,7,8,9,10\n", b""),
                subprocess.CompletedProcess([], 0, b"proof inputs", b""),
            ]
            argv = [
                "driver.py", "-e", "input.out", "-c", str(circuit),
                *extra_args, "example",
            ]
            old_cwd = os.getcwd()
            try:
                with patch("sys.argv", argv), patch("subprocess.run", side_effect=converted), \
                     patch("subprocess.Popen", side_effect=launch), \
                     patch("shutil.which", return_value="/tools/bin/circ"), \
                     contextlib.redirect_stdout(output):
                    with self.assertRaises(SystemExit) as result:
                        runpy.run_path(str(ROOT / "driver.py"), run_name="__main__")
                self.assertEqual(
                    (circuit / "example.pin").exists(), "--no-cleanup" in extra_args
                )
                return result.exception.code, output.getvalue(), calls[0]
            finally:
                os.chdir(old_cwd)

    def test_prover_failure_is_propagated(self):
        code, output, _ = self.run_driver(status=7)
        self.assertEqual(code, 7)
        self.assertIn("first\nlast\n", output)

    def test_path_command_and_complete_output(self):
        code, output, command = self.run_driver()
        self.assertEqual(code, 0)
        self.assertEqual(command[0], "/tools/bin/circ")
        self.assertTrue(output.endswith("first\nlast\n"))

    def test_explicit_relative_executable(self):
        expected = os.path.abspath("./build/circ")
        _, _, command = self.run_driver(extra_args=("--circ-exe", "./build/circ"))
        self.assertEqual(command[0], expected)

    def test_no_time_disables_timing(self):
        _, output, _ = self.run_driver(extra_args=("--no-time",))
        self.assertNotIn("Simplify/Export time:", output)

    def test_time_enables_timing(self):
        _, output, _ = self.run_driver(extra_args=("--time",))
        self.assertIn("Simplify/Export time:", output)

    def test_no_cleanup_preserves_inputs(self):
        code, _, _ = self.run_driver(extra_args=("--no-cleanup",))
        self.assertEqual(code, 0)


if __name__ == "__main__":
    unittest.main()
