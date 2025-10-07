module Sessions.Types.Base

import Decidable.Equality

%default total

public export
data Base = NAT | BOOL

noSR : NAT = BOOL -> Void
noSR Refl impossible

decEq : (x,y : Base) -> Dec (x = y)
decEq NAT NAT = Yes Refl
decEq NAT BOOL = No noSR
decEq BOOL NAT = No (negEqSym noSR)
decEq BOOL BOOL = Yes Refl

export
DecEq Base where
  decEq = Base.decEq
