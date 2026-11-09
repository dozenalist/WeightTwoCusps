module

public meta import Lean

public meta section

/- Close the scopes of an extracted solution before its public statement.
This permits keeping the proof and its statement in one source module. -/
open Lean Elab Command in
elab "flt_end_scopes" : command => do
  let scopes ← getScopes
  for scope in scopes.dropLast do
    if scope.header.isEmpty then
      elabCommand (← `(end))
    else
      elabCommand (← `(end $(mkIdent (.mkSimple scope.header))))
