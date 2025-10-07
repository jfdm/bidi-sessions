module Example

import Sessions.Types.Local
import Sessions.Types.Local
import Sessions.Types.Local.Merge.Synthesis
import Sessions.Types.Local.Merge.Projection

import Sessions.AST
import Sessions.Elab

%default total

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

huzzah : Session.AST
huzzah
  = Session
    (Choice 0 1
            [ ("foo", NAT, End)
            , ("baz", BOOL, End)
            , ("bar", BOOL, End)
            , ("sup", NAT, End)
            ])
    0
    (If (Switch True)
      (Send 1 "foo" (N 1) Stop)
      (Send 1 "bar" True  Stop))

test : Synth.AST
test
  = If (Switch True)
       (Send 1 "foo" (N 1) (Recv 1 [ ("a", "x", BOOL, Stop)
                                  , ("b", "x",NAT, Stop)]))
       (Send 1 "foo" (N 2) (Recv 1 [ ("a", "x",BOOL, Stop)
                                  , ("b", "x",NAT, Stop)]
       ))

-- [ EOF ]
