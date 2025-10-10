module Example


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
       (Send 1 "foo" (N 1) (Recv 1 (SUM [("a",NAT), ("b", BOOL)])
                                   [ ("a", "x", Stop)
                                   , ("b", "x", Stop)]))
       (Send 1 "foo" (N 2) (Recv 1 (SUM [("a",NAT), ("b", BOOL)])
                                   [ ("a", "x",Stop)
                                  , ("b", "x",Stop)]
       ))

test1 : Synth.AST
test1
  = Match
    (The (SUM [("foo", BOOL), ("bar", NAT), ("ting", (SUM [("new", BOOL)]))]) (Tag "foo" False))
    [ ("foo", "x",
        Send 1 "bat" (V "x") Stop
        )
    , ("bar", "x",
        Send 1 "baz" True Stop
        )
    , ("ting", "x",
        Send 1 "tang" False Stop)
    ]

test2 : Session.AST
test2
  = Session
    (Choice 0 1
      [("foo", NAT, (Choice 1 0
            [ ("foo", NAT, End)
            , ("baz", BOOL, End)
            , ("bar", BOOL, End)
            , ("sup", NAT, End)
            ]))])
    0
    (If (Switch True)
       (Send 1 "foo" (N 1) (Recv 1 (SUM [("foo",NAT), ("baz", BOOL)])
                                   [ ("foo", "x", Stop)
                                   , ("baz", "x", Stop)]))
       (Send 1 "foo" (N 2) (Recv 1 (SUM [("foo",NAT), ("baz", BOOL)])
                                   [ ("foo", "x",Stop)
                                  , ("baz", "x",Stop)]
       )))


paperTerm : Synth.AST
paperTerm
  =  Loop
     $ If (Switch True)
          (Send 0 "This" (N 1)
           $ Recv 0 (SUM [("Quit", NAT)])
                         [ ("Quit", "x", Stop)])
          (Send 0 "That" True
           $ Recv 0 (SUM [("Loop", BOOL)])
                         [ ("Loop", "x", Call 0)])

paperType : Global
paperType
  = Rec
    $ Choice 1 0
      [ ("This", NAT,  Choice 0 1 [("Quit", NAT, End)])
      , ("That", BOOL, Choice 0 1 [("Loop", BOOL, Call 0)])
      ]

paper : Session.AST
paper
  = Session
    paperType
    1
    paperTerm

-- [ EOF ]
