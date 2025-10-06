module Sessions.Types.Common

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

namespace CTy
  public export
  data CTy = SEND | RECV

  noSR : SEND = RECV -> Void
  noSR Refl impossible

  decEq : (x,y : CTy) -> Dec (x = y)
  decEq SEND SEND = Yes Refl
  decEq SEND RECV = No noSR
  decEq RECV SEND = No (negEqSym noSR)
  decEq RECV RECV = Yes Refl

  export
  DecEq CTy where
    decEq = CTy.decEq

namespace Role
  public export
  data Role = MkRole String

  decEq : (x,y : Role) -> Dec (x = y)
  decEq (MkRole x) (MkRole y) with (decEq x y)
    decEq (MkRole x) (MkRole x) | (Yes Refl) = Yes Refl
    decEq (MkRole x) (MkRole y) | (No contra) = No (\case Refl => contra Refl)

  export
  DecEq Role where
    decEq = Role.decEq


  public export
  Context : Type
  Context = SnocList Role


namespace Fix
--  public export
--  data Fix  = MkFix String
--
--  decEq : (x,y : Fix) -> Dec (x = y)
--  decEq (MkFix x) (MkFix y) with (decEq x y)
--    decEq (MkFix x) (MkFix x) | (Yes Refl) = Yes Refl
--    decEq (MkFix x) (MkFix y) | (No contra) = No (\case Refl => contra Refl)
--
--  export
--  DecEq Fix where
--    decEq = Fix.decEq

  public export
  data Fix = MkFix

  export
  DecEq Fix where
    decEq MkFix MkFix = Yes Refl

  public export
  Context : Type
  Context = SnocList Fix
