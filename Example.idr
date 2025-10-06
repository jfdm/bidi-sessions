module Example

import Sessions.Types.Local
import Sessions.Types.Local
import Sessions.Types.Local.Merge.Synthesis
import Sessions.Types.Local.Merge.Projection

import Sessions.AST
import Sessions.Elab

left : Local [< MkRole "Alice", MkRole "Bob"] Lin
left = Comm SEND (H Refl)
     [ B "foo" NAT Stop
     , B "baz" BOOL Stop
     ]

left' : Local [< MkRole "Alice", MkRole "Bob"] Lin
left' = Comm SEND (H Refl)
     [ B "foo" NAT Stop
     , B "baz" BOOL Stop
     ]

right : Local [< MkRole "Alice", MkRole "Bob"] Lin
right = Comm SEND (H Refl)
     [ B "bar" NAT Stop
     , B "bat" NAT Stop
     ]


export
huzzah : Session.AST
huzzah
  = Session
    (Comm SEND 0
    [ ("foo", NAT, End)
    , ("baz", BOOL, End)
    , ("bar", BOOL, End)
    ])
    $ If (Switch True)
      (Send 0 "foo" (N 1) Stop)
      (Send 0 "bar" True  Stop)


-- [ EOF ]
