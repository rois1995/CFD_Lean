import CFDLean.Papers.JST1.Spec.Addendum2
import CFDLean.Papers.JST1.Spec.Item1
import CFDLean.Papers.JST1.Spec.Item10
import CFDLean.Papers.JST1.Spec.Item11a
import CFDLean.Papers.JST1.Spec.Item11b
import CFDLean.Papers.JST1.Spec.Item11c
import CFDLean.Papers.JST1.Spec.Item12
import CFDLean.Papers.JST1.Spec.Item13
import CFDLean.Papers.JST1.Spec.Item14
import CFDLean.Papers.JST1.Spec.Item15
import CFDLean.Papers.JST1.Spec.Item16
import CFDLean.Papers.JST1.Spec.Item17
import CFDLean.Papers.JST1.Spec.Item18
import CFDLean.Papers.JST1.Spec.Item19
import CFDLean.Papers.JST1.Spec.Item2
import CFDLean.Papers.JST1.Spec.Item20
import CFDLean.Papers.JST1.Spec.Item3
import CFDLean.Papers.JST1.Spec.Item4
import CFDLean.Papers.JST1.Spec.Item5
import CFDLean.Papers.JST1.Spec.Item6
import CFDLean.Papers.JST1.Spec.Item7
import CFDLean.Papers.JST1.Spec.Item8
import CFDLean.Papers.JST1.Spec.Item9
import CFDLean.Papers.JST1.Proofs.Addendum2
import CFDLean.Papers.JST1.Proofs.Addendum2Wall
import CFDLean.Papers.JST1.Proofs.Closure
import CFDLean.Papers.JST1.Proofs.DissGeom
import CFDLean.Papers.JST1.Proofs.DualFacets
import CFDLean.Papers.JST1.Proofs.DualFacets3
import CFDLean.Papers.JST1.Proofs.Geom3
import CFDLean.Papers.JST1.Proofs.Item1
import CFDLean.Papers.JST1.Proofs.Item10
import CFDLean.Papers.JST1.Proofs.Item11a
import CFDLean.Papers.JST1.Proofs.Item11b
import CFDLean.Papers.JST1.Proofs.Item11c
import CFDLean.Papers.JST1.Proofs.Item12Comb
import CFDLean.Papers.JST1.Proofs.Item13
import CFDLean.Papers.JST1.Proofs.Item14
import CFDLean.Papers.JST1.Proofs.Item15
import CFDLean.Papers.JST1.Proofs.Item16
import CFDLean.Papers.JST1.Proofs.Item17
import CFDLean.Papers.JST1.Proofs.Item18
import CFDLean.Papers.JST1.Proofs.Item19
import CFDLean.Papers.JST1.Proofs.Item2Euler
import CFDLean.Papers.JST1.Proofs.Item20
import CFDLean.Papers.JST1.Proofs.Item2Generic
import CFDLean.Papers.JST1.Proofs.Item3
import CFDLean.Papers.JST1.Proofs.Item6
import CFDLean.Papers.JST1.Proofs.Item7
import CFDLean.Papers.JST1.Proofs.Item8
import CFDLean.Papers.JST1.Proofs.Item9
import CFDLean.Papers.JST1.Proofs.MeshAlgebra
import CFDLean.Papers.JST1.Proofs.Simplex
import CFDLean.Papers.JST1.Proofs.Viscous

/-! JST1 solution for `lake comparator` (`Challenges/JST1.comparator.json`): each of the 112 frozen paper-1 statements,
under the name the challenge `Challenges/JST1.lean` gives it, bound to its proof in `CFDLean.JST1.Proofs`. -/

namespace CFDLean.Verification.JST1Verify

theorem p1_1_0 : CFDLean.JST1.Spec.P1_1_0 := CFDLean.JST1.Proofs.p1_1_0
theorem p1_1_1 : CFDLean.JST1.Spec.P1_1_1 := CFDLean.JST1.Proofs.p1_1_1
theorem p1_1_2 : CFDLean.JST1.Spec.P1_1_2 := CFDLean.JST1.Proofs.p1_1_2
theorem p1_1_3 : CFDLean.JST1.Spec.P1_1_3 := CFDLean.JST1.Proofs.p1_1_3
theorem p1_1_4 : CFDLean.JST1.Spec.P1_1_4 := CFDLean.JST1.Proofs.p1_1_4
theorem p1_1_5 : CFDLean.JST1.Spec.P1_1_5 := CFDLean.JST1.Proofs.p1_1_5
theorem p1_1_6 : CFDLean.JST1.Spec.P1_1_6 := CFDLean.JST1.Proofs.p1_1_6
theorem p1_2_0 : CFDLean.JST1.Spec.P1_2_0 := CFDLean.JST1.Proofs.p1_2_0
theorem p1_2_1 : CFDLean.JST1.Spec.P1_2_1 := CFDLean.JST1.Proofs.p1_2_1
theorem p1_2_2 : CFDLean.JST1.Spec.P1_2_2 := CFDLean.JST1.Proofs.p1_2_2
theorem p1_2_3 : CFDLean.JST1.Spec.P1_2_3 := CFDLean.JST1.Proofs.p1_2_3
theorem p1_2_4 : CFDLean.JST1.Spec.P1_2_4 := CFDLean.JST1.Proofs.p1_2_4
theorem p1_2_5 : CFDLean.JST1.Spec.P1_2_5 := CFDLean.JST1.Proofs.p1_2_5
theorem p1_2_6 : CFDLean.JST1.Spec.P1_2_6 := CFDLean.JST1.Proofs.p1_2_6
theorem p1_2_7 : CFDLean.JST1.Spec.P1_2_7 := CFDLean.JST1.Proofs.p1_2_7
theorem p1_3_1 : CFDLean.JST1.Spec.P1_3_1 := CFDLean.JST1.Proofs.p1_3_1
theorem p1_3_2 : CFDLean.JST1.Spec.P1_3_2 := CFDLean.JST1.Proofs.p1_3_2
theorem p1_3_3 : CFDLean.JST1.Spec.P1_3_3 := CFDLean.JST1.Proofs.p1_3_3
theorem p1_3_4 : CFDLean.JST1.Spec.P1_3_4 := CFDLean.JST1.Proofs.p1_3_4
theorem p1_4_0 : CFDLean.JST1.Spec.P1_4_0 := CFDLean.JST1.Proofs.p1_4_0
theorem p1_4_1 : CFDLean.JST1.Spec.P1_4_1 := CFDLean.JST1.Proofs.p1_4_1
theorem p1_4_2 : CFDLean.JST1.Spec.P1_4_2 := CFDLean.JST1.Proofs.p1_4_2
theorem p1_4_3 : CFDLean.JST1.Spec.P1_4_3 := CFDLean.JST1.Proofs.p1_4_3
theorem p1_4_3b : CFDLean.JST1.Spec.P1_4_3b := CFDLean.JST1.Proofs.p1_4_3b
theorem p1_4_4 : CFDLean.JST1.Spec.P1_4_4 := CFDLean.JST1.Proofs.p1_4_4
theorem p1_5_0a : CFDLean.JST1.Spec.P1_5_0a := CFDLean.JST1.Proofs.p1_5_0a
theorem p1_5_0b : CFDLean.JST1.Spec.P1_5_0b := CFDLean.JST1.Proofs.p1_5_0b
theorem p1_5_1 : CFDLean.JST1.Spec.P1_5_1 := CFDLean.JST1.Proofs.p1_5_1
theorem p1_5_2 : CFDLean.JST1.Spec.P1_5_2 := CFDLean.JST1.Proofs.p1_5_2
theorem p1_5_3 : CFDLean.JST1.Spec.P1_5_3 := CFDLean.JST1.Proofs.p1_5_3
theorem p1_5_4 : CFDLean.JST1.Spec.P1_5_4 := CFDLean.JST1.Proofs.p1_5_4
theorem p1_5_4b : CFDLean.JST1.Spec.P1_5_4b := CFDLean.JST1.Proofs.p1_5_4b
theorem p1_5_5 : CFDLean.JST1.Spec.P1_5_5 := CFDLean.JST1.Proofs.p1_5_5
theorem p1_5_6 : CFDLean.JST1.Spec.P1_5_6 := CFDLean.JST1.Proofs.p1_5_6
theorem p1_5_7 : CFDLean.JST1.Spec.P1_5_7 := CFDLean.JST1.Proofs.p1_5_7
theorem p1_5_8 : CFDLean.JST1.Spec.P1_5_8 := CFDLean.JST1.Proofs.p1_5_8
theorem p2_6_1 : CFDLean.JST1.Spec.P2_6_1 := CFDLean.JST1.Proofs.p2_6_1
theorem p2_6_2 : CFDLean.JST1.Spec.P2_6_2 := CFDLean.JST1.Proofs.p2_6_2
theorem p2_6_3 : CFDLean.JST1.Spec.P2_6_3 := CFDLean.JST1.Proofs.p2_6_3
theorem p2_6_4 : CFDLean.JST1.Spec.P2_6_4 := CFDLean.JST1.Proofs.p2_6_4
theorem p2_6_5 : CFDLean.JST1.Spec.P2_6_5 := CFDLean.JST1.Proofs.p2_6_5
theorem p2_6_5b : CFDLean.JST1.Spec.P2_6_5b := CFDLean.JST1.Proofs.p2_6_5b
theorem p2_6_6 : CFDLean.JST1.Spec.P2_6_6 := CFDLean.JST1.Proofs.p2_6_6
theorem p2_6_7 : CFDLean.JST1.Spec.P2_6_7 := CFDLean.JST1.Proofs.p2_6_7
theorem p2_7_1 : CFDLean.JST1.Spec.P2_7_1 := CFDLean.JST1.Proofs.p2_7_1
theorem p2_7_2 : CFDLean.JST1.Spec.P2_7_2 := CFDLean.JST1.Proofs.p2_7_2
theorem p2_7_3 : CFDLean.JST1.Spec.P2_7_3 := CFDLean.JST1.Proofs.p2_7_3
theorem p2_7_4 : CFDLean.JST1.Spec.P2_7_4 := CFDLean.JST1.Proofs.p2_7_4
theorem p2_8_0 : CFDLean.JST1.Spec.P2_8_0 := CFDLean.JST1.Proofs.p2_8_0
theorem p2_8_1 : CFDLean.JST1.Spec.P2_8_1 := CFDLean.JST1.Proofs.p2_8_1
theorem p2_8_2 : CFDLean.JST1.Spec.P2_8_2 := CFDLean.JST1.Proofs.p2_8_2
theorem p2_8_3 : CFDLean.JST1.Spec.P2_8_3 := CFDLean.JST1.Proofs.p2_8_3
theorem p2_8_4 : CFDLean.JST1.Spec.P2_8_4 := CFDLean.JST1.Proofs.p2_8_4
theorem p2_8_5 : CFDLean.JST1.Spec.P2_8_5 := CFDLean.JST1.Proofs.p2_8_5
theorem p2_8_6 : CFDLean.JST1.Spec.P2_8_6 := CFDLean.JST1.Proofs.p2_8_6
theorem p2_9_0 : CFDLean.JST1.Spec.P2_9_0 := CFDLean.JST1.Proofs.p2_9_0
theorem p2_9_1 : CFDLean.JST1.Spec.P2_9_1 := CFDLean.JST1.Proofs.p2_9_1
theorem p2_9_2 : CFDLean.JST1.Spec.P2_9_2 := CFDLean.JST1.Proofs.p2_9_2
theorem p2_9_3 : CFDLean.JST1.Spec.P2_9_3 := CFDLean.JST1.Proofs.p2_9_3
theorem p2_9_4 : CFDLean.JST1.Spec.P2_9_4 := CFDLean.JST1.Proofs.p2_9_4
theorem p2_10_1 : CFDLean.JST1.Spec.P2_10_1 := CFDLean.JST1.Proofs.p2_10_1
theorem p2_10_2 : CFDLean.JST1.Spec.P2_10_2 := CFDLean.JST1.Proofs.p2_10_2
theorem p2_10_3 : CFDLean.JST1.Spec.P2_10_3 := CFDLean.JST1.Proofs.p2_10_3
theorem p2_10_4 : CFDLean.JST1.Spec.P2_10_4 := CFDLean.JST1.Proofs.p2_10_4
theorem p2_10_5 : CFDLean.JST1.Spec.P2_10_5 := CFDLean.JST1.Proofs.p2_10_5
theorem p2_10_6 : CFDLean.JST1.Spec.P2_10_6 := CFDLean.JST1.Proofs.p2_10_6
theorem p2_10_7 : CFDLean.JST1.Spec.P2_10_7 := CFDLean.JST1.Proofs.p2_10_7
theorem p2_10_8 : CFDLean.JST1.Spec.P2_10_8 := CFDLean.JST1.Proofs.p2_10_8
theorem p2_8_0b : CFDLean.JST1.Spec.P2_8_0b := CFDLean.JST1.Proofs.p2_8_0b
theorem p2_9_2b : CFDLean.JST1.Spec.P2_9_2b := CFDLean.JST1.Proofs.p2_9_2b
theorem p2_10_8b : CFDLean.JST1.Spec.P2_10_8b := CFDLean.JST1.Proofs.p2_10_8b
theorem p2_10_8c : CFDLean.JST1.Spec.P2_10_8c := CFDLean.JST1.Proofs.p2_10_8c
theorem p3_11_1 : CFDLean.JST1.Spec.P3_11_1 := CFDLean.JST1.Proofs.p3_11_1
theorem p3_11_2 : CFDLean.JST1.Spec.P3_11_2 := CFDLean.JST1.Proofs.p3_11_2
theorem p3_11_3 : CFDLean.JST1.Spec.P3_11_3 := CFDLean.JST1.Proofs.p3_11_3
theorem p3_12_1 : CFDLean.JST1.Spec.P3_12_1 := CFDLean.JST1.Proofs.p3_12_1
theorem p3_12_2 : CFDLean.JST1.Spec.P3_12_2 := CFDLean.JST1.Proofs.p3_12_2
theorem p3_12_3 : CFDLean.JST1.Spec.P3_12_3 := CFDLean.JST1.Proofs.p3_12_3
theorem p3_12_4 : CFDLean.JST1.Spec.P3_12_4 := CFDLean.JST1.Proofs.p3_12_4
theorem p3_12_5 : CFDLean.JST1.Spec.P3_12_5 := CFDLean.JST1.Proofs.p3_12_5
theorem p3_13_1 : CFDLean.JST1.Spec.P3_13_1 := CFDLean.JST1.Proofs.p3_13_1
theorem p3_13_2 : CFDLean.JST1.Spec.P3_13_2 := CFDLean.JST1.Proofs.p3_13_2
theorem p3_11_2b : CFDLean.JST1.Spec.P3_11_2b := CFDLean.JST1.Proofs.p3_11_2b
theorem p3_11_4 : CFDLean.JST1.Spec.P3_11_4 := CFDLean.JST1.Proofs.p3_11_4
theorem p3_11_4b : CFDLean.JST1.Spec.P3_11_4b := CFDLean.JST1.Proofs.p3_11_4b
theorem p3_11_5 : CFDLean.JST1.Spec.P3_11_5 := CFDLean.JST1.Proofs.p3_11_5
theorem p3_11_6 : CFDLean.JST1.Spec.P3_11_6 := CFDLean.JST1.Proofs.p3_11_6
theorem p3_14_1 : CFDLean.JST1.Spec.P3_14_1 := CFDLean.JST1.Proofs.p3_14_1
theorem p3_14_2 : CFDLean.JST1.Spec.P3_14_2 := CFDLean.JST1.Proofs.p3_14_2
theorem p3_14_3 : CFDLean.JST1.Spec.P3_14_3 := CFDLean.JST1.Proofs.p3_14_3
theorem p3_11_7 : CFDLean.JST1.Spec.P3_11_7 := CFDLean.JST1.Proofs.p3_11_7
theorem p3_11_8 : CFDLean.JST1.Spec.P3_11_8 := CFDLean.JST1.Proofs.p3_11_8
theorem p4_15_1 : CFDLean.JST1.Spec.P4_15_1 := CFDLean.JST1.Proofs.p4_15_1
theorem p4_15_2 : CFDLean.JST1.Spec.P4_15_2 := CFDLean.JST1.Proofs.p4_15_2
theorem p4_15_3 : CFDLean.JST1.Spec.P4_15_3 := CFDLean.JST1.Proofs.p4_15_3
theorem p4_15_4 : CFDLean.JST1.Spec.P4_15_4 := CFDLean.JST1.Proofs.p4_15_4
theorem p4_15_5 : CFDLean.JST1.Spec.P4_15_5 := CFDLean.JST1.Proofs.p4_15_5
theorem p4_15_6 : CFDLean.JST1.Spec.P4_15_6 := CFDLean.JST1.Proofs.p4_15_6
theorem p4_16_1 : CFDLean.JST1.Spec.P4_16_1 := CFDLean.JST1.Proofs.p4_16_1
theorem p4_16_2 : CFDLean.JST1.Spec.P4_16_2 := CFDLean.JST1.Proofs.p4_16_2
theorem p4_16_3 : CFDLean.JST1.Spec.P4_16_3 := CFDLean.JST1.Proofs.p4_16_3
theorem p4_16_4 : CFDLean.JST1.Spec.P4_16_4 := CFDLean.JST1.Proofs.p4_16_4
theorem p4_17_1 : CFDLean.JST1.Spec.P4_17_1 := CFDLean.JST1.Proofs.p4_17_1
theorem p4_18_1 : CFDLean.JST1.Spec.P4_18_1 := CFDLean.JST1.Proofs.p4_18_1
theorem p4_18_2 : CFDLean.JST1.Spec.P4_18_2 := CFDLean.JST1.Proofs.p4_18_2
theorem p5_19_1 : CFDLean.JST1.Spec.P5_19_1 := CFDLean.JST1.Proofs.p5_19_1
theorem p5_19_2 : CFDLean.JST1.Spec.P5_19_2 := CFDLean.JST1.Proofs.p5_19_2
theorem p5_19_3 : CFDLean.JST1.Spec.P5_19_3 := CFDLean.JST1.Proofs.p5_19_3
theorem p5_20_1 : CFDLean.JST1.Spec.P5_20_1 := CFDLean.JST1.Proofs.p5_20_1
theorem p5_20_2 : CFDLean.JST1.Spec.P5_20_2 := CFDLean.JST1.Proofs.p5_20_2
theorem p5_20_3 : CFDLean.JST1.Spec.P5_20_3 := CFDLean.JST1.Proofs.p5_20_3
theorem p5_20_4 : CFDLean.JST1.Spec.P5_20_4 := CFDLean.JST1.Proofs.p5_20_4

end CFDLean.Verification.JST1Verify
