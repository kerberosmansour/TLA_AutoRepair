----------------------------- MODULE Counter -----------------------------
EXTENDS Naturals
VARIABLES x

Init == 
    x = 0

Next == 
    IF x < 5
    THEN x' = x + 1
    ELSE x' = x

InvariantViolation == 
    x > 6 \* This will cause an invariant violation as x will never be > 6

SYNTAX_ERROR_HERE \* This is an intentional syntax error
=============================================================================
