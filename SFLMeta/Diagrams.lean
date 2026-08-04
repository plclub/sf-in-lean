-- Vector diagrams used by the book chapters.
--
-- These live under `SFLMeta` rather than beside the chapter that uses them
-- because they are authoring-framework code: the extracted `.lean` projects
-- drop `SFLMeta` imports (a diagram is replaced there by its ASCII alt text),
-- whereas a module under a volume prefix would be bundled into them verbatim,
-- carrying an `Illuminate` dependency the extracted project does not have.
--
-- The lambda cube is adapted, with only namespace changes, from the earlier
-- port demo (`old/sf-port-demo/port/PLF/Diagrams.lean`); the adaptation was
-- made by Claude.

import Illuminate

open Illuminate

namespace SFLMeta.Diagrams

namespace STLC.Cube

/-- Text style for the cube's annotation labels. -/
private def labelStyle : TextStyle := { fontSize := 12, fontFamily := "text" }

/-- Width of a single cube face, in diagram units. -/
private def faceWidth : Float := 120

/-- Height of a single cube face, in diagram units. -/
private def faceHeight : Float := 120

/-- Horizontal offset of the back face relative to the front face. -/
private def depthX : Float := 38

/-- Vertical offset of the back face relative to the front face. -/
private def depthY : Float := 38

/-- Stroke for front-face and depth edges. -/
private def frontStroke : Stroke := Stroke.ofWidth 1.2

/-- Stroke for back-face edges: lighter and dashed to suggest depth. -/
private def backStroke : Stroke :=
  { color := Color.lightGray, width := 1.0, dash := .dashed }

/-- Radius of the small filled dot drawn at each corner. -/
private def vertexRadius : Float := 2.2

/-- Gap (in diagram units) between a corner and its label text. -/
private def labelGap : Float := 8

/--
Position of cube corner `i` in 2D, where `i`'s three bits encode the corner's
axes: bit 0 = right (x), bit 1 = up (y), bit 2 = back (z).
-/
private def cornerPos (i : Nat) : Vec2 :=
  let right := i &&& 1 == 1
  let up    := i &&& 2 == 2
  let back  := i &&& 4 == 4
  ⟨(if right then faceWidth  else 0) + (if back then depthX else 0),
   (if up    then faceHeight else 0) + (if back then depthY else 0)⟩

/-- A small filled dot at the given position, marking a cube corner. -/
private def dot (p : Vec2) : Diagram SVG :=
  Diagram.transform (Matrix.translate p.x p.y)
    (Diagram.circle vertexRadius (fill := .solid Color.black) (stroke := { width := 0 }))

/-- A label placed at the given offset from a corner, with the given horizontal text anchor. -/
private def labelAt (corner : Vec2) (offset : Vec2) (anchor : TextAnchor) (txt : String) :
    Diagram SVG :=
  let pos := corner + offset
  Diagram.transform (Matrix.translate pos.x pos.y)
    (Diagram.text txt { labelStyle with anchor := anchor })

/--
The five SF-style labels: each is `(corner, offset, anchor, text)`, where `corner` is
a 3-bit corner index in the same encoding as `cornerPos`.
-/
private def labelSpecs : List (Nat × Vec2 × TextAnchor × String) :=
  [(0b000, ⟨0, -labelGap⟩, .middle, "STLC"),
   (0b001, ⟨labelGap, 0⟩,  .start,  "dependent types"),
   (0b010, ⟨-labelGap, 0⟩, .«end»,  "polymorphism"),
   (0b110, ⟨-labelGap, 0⟩, .«end»,  "type operators"),
   (0b111, ⟨0, labelGap⟩,  .middle, "Calculus of Constructions")]

end STLC.Cube

open STLC.Cube in
/--
The Barendregt lambda cube as an Illuminate diagram, in the layout used by
*Software Foundations*: a wireframe cube with a filled dot at each corner and
five labels — STLC at the front-bottom-left, the three dependency axes
(polymorphism, dependent types, type operators) at the three adjacent corners,
and the Calculus of Constructions at the opposite back-top-right corner.

The eight corners are indexed `0..7`; corners `i` and `j` are connected exactly
when `i XOR j ∈ {1, 2, 4}` (Hamming distance 1).
-/
def lambdaCubeDiagram : Diagram SVG :=
  let corners := List.range 8
  let dots := corners.foldl (init := .empty) fun d i =>
    d.compose (dot (cornerPos i))
  let edges := corners.foldl (init := dots) fun d i =>
    (List.range i).foldl (init := d) fun d j =>
      let diff := i.xor j
      if diff == 1 || diff == 2 || diff == 4 then
        -- Corner 4 (back-bottom-left) is hidden behind the front face;
        -- the three edges meeting it are drawn dashed.
        let hidden := i == 4 || j == 4
        let stroke := if hidden then backStroke else frontStroke
        Diagram.compose d (Diagram.line (cornerPos j) (cornerPos i) stroke)
      else d
  labelSpecs.foldl (init := edges) fun d (i, off, anc, txt) =>
    Diagram.compose d (labelAt (cornerPos i) off anc txt)

end SFLMeta.Diagrams
