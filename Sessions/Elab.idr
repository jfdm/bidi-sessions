module Sessions.Elab

import Sessions.Types.Local
import Sessions.Types.Local.Subset
import Sessions.Types.Local.Merge.Synthesis
import Sessions.AST

import Sessions.Elab.Expr
import Sessions.Elab.Local


namespace Check
  export
  unique : Check rs fs ts a tm
        -> Check rs fs ts b tm
        -> a === b


namespace Session
  public export
  data Check : (rs : SnocList Role)
            -> (ts : SnocList (String,Base))
            -> (tm : Session.AST)
                  -> Type
    where
      Session : Local rs Lin tmty tyExp
             -> Synth rs Lin ts tm tySyn
             -> Subset tySyn tyExp
             -> Check rs ts (Session tmty tm)
             -- here we can do projection...



-- [ EOF ]
