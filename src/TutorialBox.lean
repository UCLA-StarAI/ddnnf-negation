import Lean

/-!
# The `tutorial_box` attribute

`@[tutorial_box "<label>"]` records which paper statement a declaration
formalizes. A result has one theorem; a definition may have several
corresponding definitions. The research correspondence audit reads these
attributes to check the paper's tags and declaration locations.

The attribute stores metadata only. This module is a separate library
target with no proof content.
-/

open Lean

namespace TutorialBox

/-- `@[tutorial_box "<label>"]`: this declaration states the tutorial box
whose `\label` is `<label>`. -/
syntax (name := tutorialBox) "tutorial_box " str : attr

/-- The environment extension behind `@[tutorial_box "<label>"]`: for a
declaration name, the label of the tutorial box it states. -/
initialize tutorialBoxAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `tutorialBox
    descr := "the \\label of the tutorial-proof box that this declaration states"
    getParam := fun _ stx =>
      match stx with
      | `(attr| tutorial_box $label:str) => pure label.getString
      | _ => throwError "tutorial_box: expected the \\label of a tutorial box as a string literal"
  }

end TutorialBox
