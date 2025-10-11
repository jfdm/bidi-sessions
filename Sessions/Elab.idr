module Sessions.Elab

import Sessions.Types.Local

import Sessions.AST

import Sessions.Elab.Sessions
import Sessions.Terms.Process
import Sessions.Terms.Sessions

%default total

public export
data WellTyped : (rs : Role.Context)
              -> (ast : Session.AST)
                    -> Type
  where
    WT : (type  : Local rs Lin)
      -> (prf   : SynAck rs ast type)
      -> (term  : Session rs type)
               -> WellTyped rs ast


export
typeCheck : (rs : Role.Context)
         -> (ast : Session.AST)
                -> Dec (WellTyped rs ast)
typeCheck rs ast with (check rs ast)
  typeCheck rs ast | (Yes (type ** prf)) with (toTerm prf)
    typeCheck rs ast | (Yes (type ** prf)) | s
      = Yes $ WT type prf s
  typeCheck rs ast | (No no)
    = No $ \case (WT type prf term) => no (type ** prf)

-- [ EOF ]
