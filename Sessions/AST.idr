module Sessions.AST

import Sessions.Types.Base
import Sessions.Types.Common

%default total

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
                 | Call Nat
                 | Rec Local
                 | Comm CTy Nat (List (String, Base, Local))

    namespace Protocol
      public export
      data Global = End
                  | Call Nat
                  | Rec Global
                  | Choice Nat Nat (List (String, Base, Global))

    public export
    data AST = Stop
             | Call Nat
             | Loop Synth.AST
             | Send Nat String Synth.Expr Synth.AST
             | Recv Nat (List (String, String, Base, Synth.AST))
             | If Check.Expr Synth.AST Synth.AST
             | The Local Check.AST

  namespace Check

    public export
    data AST = Switch Synth.AST


  namespace Session
    public export
    data AST = Session Global Nat Synth.AST

-- [ EOF ]
