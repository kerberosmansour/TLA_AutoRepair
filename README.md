# TLA+ AutoRepair

TLA+ is a language for formal specification. It can be used to formally verify algorithms and mathematical theorems. Companies like AWS use it for verifying mission-critical parts of systems like S3.

TLA+ AutoRepair is used to repair/self-heal formal specifications with GPT-4 in a loop, with or without human intervention.

Given a TLA+ specification (.tla file) and a model to check (.cfg), the application will go through each error, send it to GPT-4 (or specified model), and fix all errors. Finally, it will document the code to make it more readable.

Example Command: python3 autorepair.py Test_Specs/Counter.tla --model=gpt-4

# Rationale - Looking at Code at a Higher Level
As Language Learning Models (LLMs) are helping improve developer productivity, it might make sense to look at code from a higher perspective. The challenge is that TLA+ and formal specifications have a steep learning curve. This tool can aid in overcoming this obstacle at the outset.

# Getting Started
1. Clone the repo e.g. git clone https://github.com/kerberosmansour/TLA_AutoRepair.git
2. Create a .env file in the folder and add your OpenAI Key.
3. Run AutoRepair on a TLA+ Spec. Example Command: python3 autorepair.py Test_Specs/Counter.tla --model=gpt-4
4. NOTE: There is a folder with TLA+ specifications that need repair.
5. NOTE: The code, by default, will check if TLA+ is installed on your system. If not, it will attempt to install it for you in these locations:
	* "Windows": "C:/Program Files/TLA+",
	* "Darwin/MacOS": "/Users/Shared/TLA+",
	* "Linux": "/usr/local/share/TLA+",
6. NOTE: TLA+ requires Java.

# CLI Arguments
* spec_name "The name of the TLA+ specification to check"
* --revert "Revert the specification to its previous state"
* --model "The name of the GPT model to use"
* --confirm "Ask for confirmation before each change"
