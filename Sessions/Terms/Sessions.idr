module Sessions.Terms.Sessions

import public Sessions.Types.Local
import        Sessions.Types.Local.Subset

import public Sessions.Types.Global
import public Sessions.Types.Global.Projection
import public Sessions.Types.Global.WellFormed


import Sessions.Terms.Expr
import Sessions.Terms.Process

%default total

public export
data Session : (rs   : SnocList Role)
            -> (type : Local rs Lin)
                  -> Type
  where
    MkSession : Process rs Lin tm type
             -> Session rs        type
