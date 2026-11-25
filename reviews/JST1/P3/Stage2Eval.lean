import Paper1.Spec.Item11b
open Paper1.RefCell Paper1.Spec

/-! Reviewer's evaluation of the finite claims P3-11.5 and P3-11.6 (stage 2), and of variants. -/

-- P3-11.5 components
#eval (hex.splits.all fun s => (hex.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (hex.pull s.1 s.2) f == (if onCellFace hex f then 1 else 2))
#eval (prism.splits.all fun s => (prism.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (prism.pull s.1 s.2) f == (if onCellFace prism f then 1 else 2))
#eval (pyramid.splits.all fun s => (pyramid.pull s.1 s.2).all fun t => (tetFaces t).all fun f =>
    faceCount (pyramid.pull s.1 s.2) f == (if onCellFace pyramid f then 1 else 2))
-- P3-11.6 components
#eval (hex.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (hex.splits.countP fun s => faceCount (hex.pull s.1 s.2) f == 1) == hex.splits.length)
#eval (prism.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (prism.splits.countP fun s => faceCount (prism.pull s.1 s.2) f == 1) == prism.splits.length)
#eval (prism.tris.all fun f => (prism.splits.countP fun s => faceCount (prism.pull s.1 s.2) f == 1) ==
    prism.splits.length)
#eval (pyramid.quads.all fun q => (q.tris false ++ q.tris true).all fun f =>
    2 * (pyramid.splits.countP fun s => faceCount (pyramid.pull s.1 s.2) f == 1) == pyramid.splits.length)
#eval (pyramid.tris.all fun f => (pyramid.splits.countP fun s => faceCount (pyramid.pull s.1 s.2) f == 1) ==
    pyramid.splits.length)
-- sanity: sizes, number of sub-tets per split, all sub-tets have 4 distinct vertices
#eval (hex.splits.map fun s => (hex.pull s.1 s.2).length).eraseDups
#eval (prism.splits.map fun s => (prism.pull s.1 s.2).length).eraseDups
#eval (pyramid.splits.map fun s => (pyramid.pull s.1 s.2).length).eraseDups
#eval hex.splits.all fun s => (hex.pull s.1 s.2).all fun t => t.length == 4 && t.Nodup
-- every split of the hexahedron is genuinely different (no duplicate split up to order)
#eval (hex.splits.map fun s => hex.pull s.1 s.2).length
-- falsification probe: a face triangle that is not used by any split would make P3-11.6 vacuous-looking;
-- count per hex face triangle
#eval hex.quads.map fun q => (q.tris false ++ q.tris true).map fun f =>
    hex.splits.countP fun s => faceCount (hex.pull s.1 s.2) f == 1
-- interior triangles: max faceCount over all triangles of all splits that are not on a cell face
#eval (hex.splits.flatMap fun s => (hex.pull s.1 s.2).flatMap fun t => (tetFaces t).filter
    (fun f => !onCellFace hex f) |>.map fun f => faceCount (hex.pull s.1 s.2) f).eraseDups
