import DDNNFNegationCorollaries

-- Check the six corollaries in the paper and their axiom dependencies.
open Lean Elab Command

def corollaryEndpoints : List (String × Name × String) := [
  ("cor:paper-internal-negation", ``DDNNFNegation.internal_negation_separation, "InternalNegation"),
  ("cor:paper-uobdd", ``DDNNFNegation.unambiguous_obdd_separation, "UnambiguousOBDD"),
  ("cor:paper-grammar", ``DDNNFNegation.grammar_complementation, "GrammarComplementation"),
  ("cor:paper-generating", ``DDNNFNegation.missing_monomials, "MissingMonomials"),
  ("cor:paper-dpda", ``DDNNFNegation.dpda_size_separation, "PushdownAutomata"),
  ("cor:paper-probabilistic", ``DDNNFNegation.probabilistic_subtraction, "ProbabilisticSubtraction")]

run_cmd do
  let env ← getEnv
  for i in [0:env.header.moduleNames.size] do
    if (env.header.moduleNames[i]!).toString.startsWith "DDNNFNegationCorollaries." then
      for (_, tag) in TutorialBox.tutorialBoxAttr.ext.getModuleEntries env i do
        unless corollaryEndpoints.any (fun entry => entry.1 == tag) do
          throwError "An endpoint outside the paper was exported: {tag}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut lines : Array String := #[]
  for (label, root, module) in corollaryEndpoints do
    let some (.thmInfo _) := env.find? root
      | throwError "The paper endpoint {root} is not a proved theorem"
    let mut tagged : Array Name := #[]
    for i in [0:env.header.moduleNames.size] do
      for (decl, tag) in TutorialBox.tutorialBoxAttr.ext.getModuleEntries env i do
        if tag == label then tagged := tagged.push decl
    unless tagged == #[root] do
      throwError "The paper box {label} must correspond to exactly its endpoint: {tagged}"
    let axioms ← liftCoreM (collectAxioms root)
    for ax in axioms do
      unless allowed.contains ax do
        throwError "The paper endpoint {root} depends on an unapproved axiom: {ax}"
    lines := lines.push s!"REF {label} {module} {root}"
  lines := lines.push "AXIOMS only propext, Classical.choice, Quot.sound"
  logInfo (String.intercalate "\n" lines.toList)
