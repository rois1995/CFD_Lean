import json
import unittest
from verify import parse_axioms, check_promises, check_result_ids, check_inherited, check_m3_layout, check_m3_inherited


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

    def test_empty_or_malformed_inventory(self):
        for output in ["", "CFDLEAN_DECL {bad}"]:
            with self.assertRaises(ValueError):
                parse_axioms(output)


if __name__ == "__main__":
    unittest.main()
