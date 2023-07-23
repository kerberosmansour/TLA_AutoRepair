# TLA_AutoRepair
A TLA+ AutoRepair System For Formal Specification with GPT-4
Given a TLA+ Spec (.tla file) and a model to check (.cfg) The Application will go through earch error, send ot GPT-4 (or specificed model) and fix all errors, Finally it will document the code to make it more readable.
Example Command: python3 autorepair.py tla_tests/Spec1.tla --model=gpt-4

# Rational - Looking at code at a higher level
As LLMs are helping improve developer productivity, it might make sense to look at code at a higher level.
The chellege is TLA+ and formal specifications have a steep lurning curve, this can help aid getting the most out of it at the start.

# CLI Arguments
* spec_name "The name of the TLA+ spec to check"
* --revert "Revert the spec to its previous state"
* --model "The name of the GPT model to use"
* --confirm "Ask for confirmation before each change"
