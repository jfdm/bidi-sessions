module Sessions.AST

import Sessions.Types.Base
import Sessions.Types.Common

mutual
  namespace Expr
    namespace Synth
      public export
      data Expr = True | False | N Nat | V String | The Base Check.Expr

    namespace Check
      public export
      data Expr = Switch Synth.Expr

mutual
  namespace Synth

    namespace Type
      public export
      data Local = End
                 | Call String
                 | Rec String Local
                 | Comm CTy String (List (String, Base, Local))

    public export
    data AST = Stop
             | Call String
             | Loop String Synth.AST
             | Send String String Base Synth.AST
             | Recv String (List (String, String, Base, Synth.AST))
             | If Check.Expr Synth.AST Synth.AST
             | The Local Check.AST

  namespace Check

    public export
    data AST = Switch Synth.AST


  namespace Session
    public export
    data AST = Session Local Synth.AST
-- [ EOF ]
