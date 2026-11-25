import json
import unittest
from pathlib import Path
from verify import ACCEPTED_BASELINE, M4_ACCEPTED_REVISION, M4A_ACCEPTED_REVISION, M3_ACCEPTED_REVISION, parse_axioms, check_promises, check_result_ids, check_inherited, check_m3_layout, check_m3_inherited, check_m4_layout, check_m4_inherited, check_m5_layout


def record(name, axioms=None):
    return {"name": name, "kind": "theorem", "root": True, "unsafe": False,
            "axioms": axioms or []}


def log(*rows):
    return "\n".join("CFDLEAN_DECL " + json.dumps(row) for row in rows)


class AuditChecks(unittest.TestCase):
    def test_qualified_namespace_collision_and_axiom_free(self):
        rows = parse_axioms(log(record("A.same"), record("B.same", ["propext"])))
        self.assertEqual(set(rows), {"A.same", "B.same"})
        self.assertEqual(rows["A.same"]["axioms"], [])

    def test_multiline_type_is_preserved(self):
        row = record("A.multiline", ["propext", "Quot.sound"])
        row["type"] = "first line\nsecond line"
        self.assertEqual(parse_axioms(log(row))["A.multiline"]["type"], row["type"])

    def test_duplicate_even_if_identical(self):
        for axioms in [[], ["Quot.sound"]]:
            with self.assertRaises(ValueError):
                parse_axioms(log(record("A.same"), record("A.same", axioms)))

    def test_forbidden_and_unsafe(self):
        with self.assertRaises(ValueError):
            parse_axioms(log(record("A.bad", ["sorryAx"])))
        row = record("A.bad")
        row["unsafe"] = True
        with self.assertRaises(ValueError):
            parse_axioms(log(row))

    def test_missing_promise(self):
        contract = {"results": [{"stage": "M2a", "declarations": ["A.required"]}]}
        with self.assertRaises(ValueError):
            check_promises({"A.other": record("A.other")}, contract, "M2a")
        self.assertEqual(check_promises({"A.required": record("A.required")}, contract, "M2a"),
                         ["A.required"])

    def test_prior_stage_and_empty_active_binding(self):
        contract = {"results": [{"stage": "M2a", "declarations": ["A.first"]},
                                {"stage": "M2b", "declarations": ["A.second"]}]}
        with self.assertRaises(ValueError):
            check_promises({"A.second": record("A.second")}, contract, "M2b")
        contract["results"][1]["declarations"] = []
        with self.assertRaises(ValueError):
            check_promises({"A.first": record("A.first")}, contract, "M2b")

    def test_frozen_result_id_coverage(self):
        text = "| M2-J | claim |\n| M2-A | claim |"
        rows = [{"id": "M2-J"}, {"id": "M2-A"}]
        check_result_ids({"results": rows}, text)
        for invalid in [rows[:1], rows + rows[:1]]:
            with self.assertRaises(ValueError):
                check_result_ids({"results": invalid}, text)

    def test_inherited_binding_and_type_are_frozen(self):
        results = [{"id": rid, "stage": stage, "declarations": [rid + ".accepted"]}
                   for rid, stage in [("M2-J", "M2a"), ("M2-A", "M2b"),
                                      ("M2-R", "M2b"), ("M2-L", "M2b"), ("M2-E", "M2c"),
                                      ("M2-D", "M2c"), ("M2-O", "M2c"), ("M2-F1", "M2d"),
                                      ("M2-F2", "M2d"), ("M2-F3", "M2d"), ("M2-F4", "M2d"), ("M2-C", "M2d")]]
        contract = {"current_stage": "M2d", "results": results}
        evidence = {"declarations": {r["declarations"][0]: {"type": "approved " + r["id"]}
                                     for r in results}}
        rows = evidence["declarations"]
        self.assertEqual(len(check_inherited(rows, contract, contract, evidence)), 12)
        for index, result in enumerate(results):
            for field, replacement in [("declarations", ["Other.safeTheorem"]), ("stage", "M3a")]:
                changed = json.loads(json.dumps(contract))
                changed["results"][index][field] = replacement
                with self.assertRaises(ValueError):
                    check_inherited(rows, changed, contract, evidence)
            weakened = dict(rows)
            weakened[result["declarations"][0]] = {"type": "a weaker proposition"}
            with self.assertRaises(ValueError):
                check_inherited(weakened, contract, contract, evidence)

    def test_m3_part_layout_is_frozen(self):
        contract = {"results": [{"id": "M3-C", "parts": [{"stage": "M3a", "declarations": []},
                                                               {"stage": "M3b", "declarations": []}]}]}
        check_m3_layout(contract, contract)
        redirected = json.loads(json.dumps(contract))
        redirected["representation_contract"] = "a different specification"
        with self.assertRaises(ValueError):
            check_m3_layout(redirected, contract)
        changed = json.loads(json.dumps(contract))
        changed["results"][0]["parts"].pop()
        with self.assertRaises(ValueError):
            check_m3_layout(changed, contract)
        changed["results"][0]["parts"][0]["stage"] = "M3b"
        with self.assertRaises(ValueError):
            check_m3_layout(changed, contract)

    def test_m3_conditional_and_concrete_are_separate(self):
        contract = {"results": [{"stage": "M3a", "declarations": ["A.conditional"]},
                                {"stage": "M3b", "declarations": []}]}
        rows = {"A.conditional": record("A.conditional")}
        self.assertEqual(check_promises(rows, contract, "M3a", ("M3a", "M3b")), ["A.conditional"])
        with self.assertRaises(ValueError):
            check_promises(rows, contract, "M3b", ("M3a", "M3b"))
        check_result_ids({"results": [{"id": "M3-C"}]}, "| M3-C | conditional and concrete |", "M3")

    def test_m3a_inheritance_freezes_active_parts_and_types(self):
        accepted = {"current_stage": "M3a", "results": [
            {"id": rid, "parts": [{"stage": "M3a", "declarations": [rid + ".old"]}]} for rid in
            ["M3-I", "M3-R", "M3-O", "M3-C"]]}
        accepted["results"][-1]["parts"].append({"stage": "M3b", "declarations": []})
        rows = {rid + ".old": {"type": "approved " + rid} for rid in ["M3-I", "M3-R", "M3-O", "M3-C"]}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m3_inherited(rows, accepted, accepted, evidence)), 4)
        for i, rid in enumerate(["M3-I", "M3-R", "M3-O", "M3-C"]):
            for key, value in [("declarations", ["Other.safe"]), ("stage", "M3b")]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i]["parts"][0][key] = value
                with self.assertRaises(ValueError):
                    check_m3_inherited(rows, changed, accepted, evidence)
            weakened = dict(rows)
            weakened[rid + ".old"] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m3_inherited(weakened, accepted, accepted, evidence)
        future = json.loads(json.dumps(accepted))
        future["results"][-1]["parts"][-1]["declarations"] = ["New.concrete"]
        check_m3_inherited(rows, future, accepted, evidence)

    def test_full_m3_inheritance_freezes_every_accepted_part_and_type(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M3-results.json").read_text())
        pin = json.loads((root / "specifications/accepted-M3.json").read_text())
        self.assertEqual(M3_ACCEPTED_REVISION, pin["mathematical_commit"])
        self.assertEqual(accepted["current_stage"], "M3b")
        names = [name for r in accepted["results"] for p in r["parts"] for name in p["declarations"]]
        rows = {name: {"type": "accepted type of " + name} for name in names}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m3_inherited(rows, accepted, accepted, evidence)), 51)
        for i, result in enumerate(accepted["results"]):
            for j, part in enumerate(result["parts"]):
                for key, value in [("declarations", ["Other.safe"]),
                                   ("stage", "M3b" if part["stage"] == "M3a" else "M3a")]:
                    changed = json.loads(json.dumps(accepted))
                    changed["results"][i]["parts"][j][key] = value
                    with self.assertRaises(ValueError):
                        check_m3_inherited(rows, changed, accepted, evidence)
        for name in names:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m3_inherited(weakened, accepted, accepted, evidence)

    def test_m4_frozen_algorithm_metadata_and_stage_layout(self):
        root = Path(__file__).resolve().parents[1]
        contract = json.loads((root / "specifications/M4-results.json").read_text())
        check_m4_layout(contract, contract)
        for field in ["contract", "contract_sha256", "precision_contract", "precision_sha256",
                      "reviewed_proposal_revision", "approval_record"]:
            changed = json.loads(json.dumps(contract))
            changed[field] = "redirected"
            with self.assertRaises(ValueError):
                check_m4_layout(changed, contract)
        for i, result in enumerate(contract["results"]):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["stage"] = "M4b" if result["stage"] == "M4a" else "M4a"
            with self.assertRaises(ValueError):
                check_m4_layout(changed, contract)
        check_result_ids(contract, (root / contract["contract"]).read_text(), "M4")

    def test_m4_deferred_composition_cannot_be_claimed_complete(self):
        contract = {"results": [{"id": "M4-W", "stage": "M4a", "declarations": ["W.local"]},
                                {"id": "M4-C", "stage": "M4b", "declarations": []}]}
        rows = {"W.local": record("W.local")}
        self.assertEqual(check_promises(rows, contract, "M4a", ("M4a", "M4b")), ["W.local"])
        with self.assertRaises(ValueError):
            check_promises(rows, contract, "M4b", ("M4a", "M4b"))

    def test_m4a_accepted_records_types_and_future_stage(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M4-results.json").read_text())
        accepted["current_stage"] = "M4a"
        pin = json.loads((root / "specifications/accepted-M4a.json").read_text())
        self.assertEqual(M4A_ACCEPTED_REVISION, pin["mathematical_commit"])
        active = [r for r in accepted["results"] if r["stage"] == "M4a"]
        rows = {name: {"type": "accepted type " + name} for r in active for name in r["declarations"]}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m4_inherited(rows, accepted, accepted, evidence)), 23)
        for i, result in enumerate(accepted["results"]):
            if result["stage"] != "M4a":
                continue
            for key, value in [("stage", "M4b"), ("declarations", ["Other.safe"])]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i][key] = value
                with self.assertRaises(ValueError):
                    check_m4_inherited(rows, changed, accepted, evidence)
        for name in rows:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m4_inherited(weakened, accepted, accepted, evidence)
        future = json.loads(json.dumps(accepted))
        future["current_stage"] = "M4b"
        for r in future["results"]:
            if r["stage"] == "M4b":
                r["declarations"] = ["New." + r["id"]]
        check_m4_inherited(rows, future, accepted, evidence)

    def test_full_m4_preserves_all_records_ordered_bindings_types_and_stage(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M4-results.json").read_text())
        pin = json.loads((root / "specifications/accepted-M4.json").read_text())
        self.assertEqual(ACCEPTED_BASELINE, pin["mathematical_commit"])
        self.assertEqual(M4_ACCEPTED_REVISION, pin["mathematical_commit"])
        self.assertEqual(accepted["current_stage"], "M4b")
        names = [name for r in accepted["results"] for name in r["declarations"]]
        rows = {name: {"type": "accepted type " + name} for name in names}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m4_inherited(rows, accepted, accepted, evidence)), 39)
        for i, result in enumerate(accepted["results"]):
            for key, value in [("stage", "M4b" if result["stage"] == "M4a" else "M4a"),
                               ("declarations", ["Other.safe"]),
                               ("declarations", result["declarations"][::-1])]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i][key] = value
                with self.assertRaises(ValueError):
                    check_m4_inherited(rows, changed, accepted, evidence)
        for name in names:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m4_inherited(weakened, accepted, accepted, evidence)
        rollback = json.loads(json.dumps(accepted))
        rollback["current_stage"] = "M4a"
        with self.assertRaises(ValueError):
            check_m4_inherited(rows, rollback, accepted, evidence)

    def test_m5_frozen_metadata_and_exact_stage_layout(self):
        root = Path(__file__).resolve().parents[1]
        contract = json.loads((root / "specifications/M5-results.json").read_text())
        check_m5_layout(contract, contract)
        for field in ["contract", "contract_sha256", "reviewed_proposal_revision", "approval_record", "current_stage"]:
            changed = json.loads(json.dumps(contract))
            changed[field] = "redirected"
            with self.assertRaises(ValueError):
                check_m5_layout(changed, contract)
        for i in range(len(contract["results"])):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["stage"] = "M4b"
            with self.assertRaises(ValueError):
                check_m5_layout(changed, contract)
        check_result_ids(contract, (root / contract["contract"]).read_text(), "M5")

    def test_m5_all_six_active_ids_require_real_theorems(self):
        results = [{"id": "M5-" + k, "stage": "M5", "declarations": ["Proof." + k]}
                   for k in ["U", "V", "B", "L", "C", "O"]]
        contract = {"results": results}
        rows = {r["declarations"][0]: record(r["declarations"][0]) for r in results}
        self.assertEqual(len(check_promises(rows, contract, "M5", ("M5",))), 6)
        for i, result in enumerate(results):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["declarations"] = []
            with self.assertRaises(ValueError):
                check_promises(rows, changed, "M5", ("M5",))
            invalid = dict(rows)
            name = result["declarations"][0]
            invalid[name] = dict(rows[name], kind="definition")
            with self.assertRaises(ValueError):
                check_promises(invalid, contract, "M5", ("M5",))

    def test_empty_or_malformed_inventory(self):
        for output in ["", "CFDLEAN_DECL {bad}"]:
            with self.assertRaises(ValueError):
                parse_axioms(output)


if __name__ == "__main__":
    unittest.main()


import verify


class PortMapTests(unittest.TestCase):
    def test_pinned_map_loads(self):
        data = (verify.ROOT / verify.MC_PORT_MAP).read_bytes()
        mapping = verify.load_port_map(data)
        self.assertEqual(len(mapping), verify.MC_PORT_COUNT)

    def test_tampered_map_rejected(self):
        data = (verify.ROOT / verify.MC_PORT_MAP).read_bytes() + b" "
        with self.assertRaises(ValueError):
            verify.load_port_map(data)

    def test_type_guard(self):
        mapping = {"a": {"classification": "notation", "accepted_type": "old", "current_type": "new"},
                   "b": {"classification": "other", "accepted_type": "old", "current_type": "new"}}
        self.assertTrue(verify.same_or_ported_type("x", "t", "t", mapping))
        self.assertTrue(verify.same_or_ported_type("a", "old", "new", mapping))
        self.assertFalse(verify.same_or_ported_type("a", "old", "forged", mapping))
        self.assertFalse(verify.same_or_ported_type("b", "old", "new", mapping))
        self.assertFalse(verify.same_or_ported_type("c", "old", "new", mapping))


class MCNTests(unittest.TestCase):
    SPEC = " ".join(f"`{name}`" for name in
                    ["Basic", "LogMean", "Simplex", "Mesh", "Boundary", "PairFlux", "Galerkin", "Production", "Bridge"])

    def setUp(self):
        self.results = [{"id": f"MC-N.X-{i}", "theorem": f"CFDLean.Num.t{i}", "module": "CFDLean.Num.Mesh"}
                        for i in range(verify.MC_N_COUNT)]
        self.rows = {}
        for r in self.results:
            row = record(r["theorem"], ["propext"])
            row["module"] = r["module"]
            self.rows[r["theorem"]] = row

    def check(self, results=None, rows=None, other=()):
        return verify.check_mc_n(self.rows if rows is None else rows,
                                 {"results": self.results if results is None else results}, list(other), self.SPEC)

    def test_all_promised_theorems_accepted(self):
        self.assertEqual(len(self.check()), verify.MC_N_COUNT)

    def test_missing_wrong_kind_or_axiom_rejected(self):
        for mutate in [lambda rows, n: rows.pop(n),
                       lambda rows, n: rows[n].update(kind="definition"),
                       lambda rows, n: rows[n].update(root=False),
                       lambda rows, n: rows[n].update(axioms=["sorryAx"]),
                       lambda rows, n: rows[n].update(module="CFDLean.Num.Bridge")]:
            rows = json.loads(json.dumps(self.rows))
            mutate(rows, "CFDLean.Num.t0")
            with self.assertRaises(ValueError):
                self.check(rows=rows)

    def test_scope_count_ids_and_namespace_frozen(self):
        for results in [self.results[1:], self.results[:-1] + self.results[:1],
                        [dict(self.results[0], theorem="CFDLean.Time.t0")] + self.results[1:],
                        [dict(self.results[0], module="CFDLean.Time.Controls")] + self.results[1:],
                        [dict(self.results[0], id="M5-X")] + self.results[1:]]:
            with self.assertRaises(ValueError):
                self.check(results=results)

    def test_cannot_rebind_m1_m5_theorem(self):
        with self.assertRaises(ValueError):
            self.check(other=["CFDLean.Num.t3"])

    def test_m1_m5_sources_frozen(self):
        base = {"CFDLean/Core/State.lean": b"a", "CFDLean/Time/Controls.lean": b"b"}
        current = dict(base, **{"CFDLean/Num/Mesh.lean": b"new", "CFDLean/Num.lean": b"new"})
        paths = sorted(current)

        def blob(path):
            if path not in base:
                raise verify.subprocess.CalledProcessError(128, "git")
            return base[path]
        self.assertEqual(verify.check_mc_n_sources(paths, current.__getitem__, blob), 2)
        current["CFDLean/Time/Controls.lean"] = b"weakened"
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(paths, current.__getitem__, blob)
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(["CFDLean/Num/Mesh.lean"], current.__getitem__, blob)
