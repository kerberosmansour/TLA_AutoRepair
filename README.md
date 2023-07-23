# TLA_AutoRepair

A TLA+ is a language for formal specification. It can help formally verify algorithms and math theorms. Companies like AWS Use it for verifing mission critical parts of systems like S3.

TLA+ AutoRepair is used to repair/self-heal formal specification with GPT-4 in a loop with or without human intervention.

Given a TLA+ Spec (.tla file) and a model to check (.cfg) The Application will go through earch error, send ot GPT-4 (or specificed model) and fix all errors, Finally it will document the code to make it more readable.

Example Command: python3 autorepair.py tla_tests/Spec1.tla --model=gpt-4

# Rational - Looking at code at a higher level
As LLMs are helping improve developer productivity, it might make sense to look at code at a higher level.
The chellege is TLA+ and formal specifications have a steep lurning curve, this can help aid getting the most out of it at the start.

# Getting Started
1. Clone the repo e.g. git clone https://github.com/kerberosmansour/TLA_AutoRepair.git
2. Create a .env fil in the folder and add your OpenAI Key
3. Run AutoRepair on a TLA+ Spec Example Command: python3 autorepair.py tla_tests/Spec1.tla --model=gpt-4
4. NOTE: There is a folder with TLA+ Specs that need repair
5. NOTE: The code by default will search if TLA+ is installed on your system - if not it will try to install it for you in these locations:
	* "Windows": "C:/Program Files/TLA+",
	* "Darwin/MacOS": "/Users/Shared/TLA+",
	* "Linux": "/usr/local/share/TLA+",
6. NOTE: TLA+ Requres Java

# CLI Arguments
* spec_name "The name of the TLA+ spec to check"
* --revert "Revert the spec to its previous state"
* --model "The name of the GPT model to use"
* --confirm "Ask for confirmation before each change"
