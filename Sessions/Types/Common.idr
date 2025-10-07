module Sessions.Types.Common

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

%default total


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
  decEq (MkRole x) (MkRole y) with (Equality.decEq x y)
    decEq (MkRole x) (MkRole x) | (Yes Refl) = Yes Refl
    decEq (MkRole x) (MkRole y) | (No contra) = No (\case Refl => contra Refl)

  export
  DecEq Role where
    decEq = Role.decEq


  public export
  Context : Type
  Context = SnocList Role

  public export
  data Involved : (rs : Role.Context)
               -> (p : AtIndex a rs x)
               -> (s : AtIndex b rs y)
               -> (r : AtIndex c rs z)
                    -> Type
    where
      Sends : (prfS : role = s)
                   -> Involved rs role s r

      Recvs : (prfR : role = r)
                   -> Involved rs role s r

      Skips : (prfSNot : EqualNot role s)
           -> (prfRNot : EqualNot role r)
                      -> Involved rs role s r

  export
  involved : (p : AtIndex a rs x)
          -> (s : AtIndex b rs y)
          -> (r : AtIndex c rs z)
               -> Involved rs p s r
  involved p s r with (decEqAlt' p s)
    involved p s r | (Left noS) with (decEqAlt' p r)
      involved p s r | (Left noS) | (Left noR)
        = Skips noS noR
      involved p s p | (Left noS) | (Right Refl)
        = Recvs Refl

    involved s s r | (Right Refl)
      = Sends Refl

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
