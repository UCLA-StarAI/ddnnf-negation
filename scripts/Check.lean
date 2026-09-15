import DDNNFNegation

-- Fail if the final theorem's axiom list changes, including an unfinished proof.
/-- info: 'DDNNFNegation.dDNNF_not_closed_under_negation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DDNNFNegation.dDNNF_not_closed_under_negation
