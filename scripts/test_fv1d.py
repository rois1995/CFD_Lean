"""Black-box checks of the FV1D driver (build fv1d first)."""
import json
import math
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/bin"
WAVE = json.loads((ROOT / "benchmarks/fv1d/euler-density-wave.json").read_text())
SCHEMES = [[], ["--muscl"]] + [
    ["--limiter", name] for name in ("none", "minmod", "mc", "superbee", "vanleer", "vanalbada")
]


def output(*args):
    return subprocess.check_output([BIN / "fv1d", *args], text=True, timeout=30)


def four_cell_rusanov():
    """On this contact wave only density varies. Replay its scalar flux from the pinned initial means."""
    initial, translated = WAVE["snapshots"]
    rho = [q[0] for q in initial["exact_cell_averages"]]
    velocity = WAVE["primitive_solution"]["velocity"]
    gamma_p = WAVE["gamma"] * WAVE["primitive_solution"]["pressure"]
    dx = 1 / len(rho)
    t = initial["time"]
    while t < translated["time"]:
        speeds = [velocity + math.sqrt(gamma_p / r) for r in rho]
        dt = min(translated["time"] - t, .4 * dx / max(speeds))
        flux = []
        for i, right in enumerate(rho):
            left = rho[i-1]
            dissipation = max(speeds[i-1], speeds[i]) * (right-left)
            flux.append((velocity*(left+right) - dissipation) / 2)
        rho = [r - dt/dx*(flux[(i+1) % len(rho)] - flux[i]) for i, r in enumerate(rho)]
        t += dt
    return rho


class DriverTests(unittest.TestCase):
    def test_uniform_burgers_output(self):
        transcript = []
        for args in [[], ["1", "0", ".4", "--dump"]] + [
            ["27", "13", ".12", "--dump", *scheme] for scheme in SCHEMES
        ]:
            command = " ".join(["$ fv1d --model burgers", *args])
            transcript.append(command + "\n" + output("--model", "burgers", *args))
        expected = (ROOT / "benchmarks/fv1d/burgers-uniform.txt").read_text()
        self.assertEqual("\n".join(transcript), expected)

    def test_burgers_widths(self):
        for scheme in SCHEMES:
            with self.subTest(scheme=scheme):
                args = ["4", "3", ".12", "--dump", *scheme]
                def cells(csv):
                    lines = output("--model", "burgers", *args, "--widths", csv).splitlines()
                    return list(map(float, lines[-4:]))

                uniform = map(float, output("--model", "burgers", *args).splitlines()[-4:])
                for got, ref in zip(cells(".25,.25,.25,.25"), uniform, strict=True):
                    self.assertAlmostEqual(got, ref, places=11)
                widths = [.1, .2, .3, .4]
                xs = [sum(widths[:i]) + w / 2 for i, w in enumerate(widths)]
                initial = [.5 + math.sin(math.tau * x) for x in xs]
                final = cells(".1,.2,.3,.4")
                self.assertAlmostEqual(sum(w*(a-b) for w, a, b in zip(widths, initial, final)), 0, places=11)
                self.assertGreater(max(abs(a-b) for a, b in zip(initial, final)), .01)

    def euler_case(self, widths, *mesh_args):
        n = len(widths)
        lines = output("--model", "euler", str(n), *mesh_args, "--dump").splitlines()
        initial, header, totals, errors, *dump = lines
        final_time = WAVE["snapshots"][1]["time"]
        self.assertEqual(float(header.split("time = ")[1]), final_time)
        cells = [list(map(float, line.split())) for line in dump]
        self.assertEqual(len(cells), n)
        if n == WAVE["mesh"]["cells"] and not mesh_args:
            exact = WAVE["snapshots"][1]["exact_cell_averages"]
            for cell, rho in zip(cells, four_cell_rusanov(), strict=True):
                for got, expected in zip(cell, [rho, 2*rho, 1+2*rho], strict=True):
                    self.assertAlmostEqual(got, expected, places=11)
        else:
            exact = []
            left = 0
            for w in widths:
                phase = left - 2 * final_time
                rho = 1 + (math.cos(math.tau * phase) - math.cos(math.tau * (phase+w))) / (16*w)
                exact.append([rho, 2*rho, 1+2*rho])
                left += w
        l1 = []
        for k, (component, reference) in enumerate(zip(WAVE["components"], WAVE["domain_integrals"])):
            with self.subTest(component=component, cells=n):
                for report in (initial, totals):
                    self.assertAlmostEqual(float(report.split(" = ")[1].split()[k]), reference, places=10)
                self.assertAlmostEqual(sum(w*q[k] for w, q in zip(widths, cells)), reference, places=10)
                error = sum(w*abs(q[k]-r[k]) for w, q, r in zip(widths, cells, exact))
                self.assertAlmostEqual(float(errors.split(" = ")[1].split()[k]), error, places=10)
                l1.append(error)
        return l1

    def test_density_wave(self):
        errors = self.euler_case([.25]*4)
        # On the four-cell case a stationary or reversed wave misses this threshold.
        self.assertTrue(0 < errors[0] < .24)
        fine = self.euler_case([1/32]*32)
        self.assertTrue(all(0 < f < c/3 for f, c in zip(fine, errors)))
        graded = self.euler_case([.1, .2, .3, .4], "--widths", ".1,.2,.3,.4")
        self.assertTrue(0 < graded[0] < .2)

    def test_cli_rejects_invalid_input(self):
        for model in ("burgers", "euler"):
            for csv in ("", ".5", "0,1", "-.1,1.1", "nan,1", "inf,1", "9"*400 + ",1", ".1,.2"):
                with self.subTest(model=model, csv=csv):
                    result = subprocess.run([BIN/"fv1d", "--model", model, "2", "--widths", csv],
                                            capture_output=True, text=True, timeout=5)
                    self.assertEqual(result.returncode, 1)
                    self.assertIn("width", result.stderr)
                    self.assertFalse(result.stdout)
        for args in ([], ["--model", "other"], ["--model", "burgers", "0"],
                     ["--model", "euler", "--muscl", "--weno"], ["--model", "euler", "--limiter", "none"]):
            with self.subTest(args=args):
                self.assertEqual(subprocess.run([BIN/"fv1d", *args], capture_output=True).returncode, 1)


if __name__ == "__main__":
    unittest.main()
