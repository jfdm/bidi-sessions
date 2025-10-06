module Example

import Sessions.Types.Local
import Sessions.Types.Local.Merge.Synthesis
import Sessions.Types.Local.Merge.Projection


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

-- [ EOF ]
