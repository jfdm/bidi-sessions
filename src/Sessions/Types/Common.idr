module Sessions.Types.Common

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base

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

public export
data Branch : (ktype : Role.Context -> Fix.Context -> Type)
           -> (rs    : Role.Context)
           -> (fs    : Fix.Context)
                    -> Type
  where
    B : (l : String)
     -> (t : Base)
     -> (k : kont rs fs)
          -> Branch kont rs fs

namespace Protocol
  public export
  data Kind = GLOBAL | LOCAL

  public export
  data Protocol : (k  : Kind)
               -> (rs : Role.Context)
               -> (fs : Fix.Context)
                     -> Type
    where
      Stop : Protocol kind rs fs
      Call : {n : _}
          -> AtIndex MkFix fs n
          -> Protocol kind rs fs
      Rec : Protocol kind rs (fs :< MkFix)
         -> Protocol kind rs fs
      Comm : (dir  : CTy)
          -> (whom : AtIndex r rs n)
          -> (ks   : List (Branch (Protocol LOCAL) rs fs))
          -> Protocol LOCAL rs fs

      Choice : {s,r : _}
            -> (x : AtIndex s rs n)
            -> (y : AtIndex r rs m)
            -> EqualNot x y
            -> List (Branch (Protocol GLOBAL) rs fs)
            -> Protocol GLOBAL rs fs


mutual
  namespace Branch
    export
    decEq : (f : (x,y : how rs fs) -> Dec (x === y))
         -> (x,y : Branch how rs fs)
                -> Dec (x === y)
    decEq f (B lx tx kx) (B ly ty ky) with (Equality.decEq lx ly)
      decEq f (B lx tx kx) (B lx ty ky) | (Yes Refl) with (decEq tx ty)
        decEq f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) with (f kx ky)
          decEq f (B lx tx kx) (B lx tx kx) | (Yes Refl) | (Yes Refl) | (Yes Refl)
            = Yes Refl
          decEq f (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (No no)
            = No $ \case Refl => no Refl
        decEq f (B lx tx kx) (B lx ty ky) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq f (B lx tx kx) (B ly ty ky) | (No no)
        = No $ \case Refl => no Refl

  namespace Branches

    export
    decEq : (f   : (x,y : how rs fs) -> Dec (x === y))
         -> (x,y : List $ Branch how rs fs)
                -> Dec (x === y)
    decEq _ [] [] = Yes Refl
    decEq _ [] (x :: xs)
      = No rightHeavy
    decEq _ (x :: xs) []
      = No leftHeavy
    decEq f (x :: xs) (y :: ys) with (decEq f x y)
      decEq f (x :: xs) (x :: ys) | (Yes Refl) with (decEq f xs ys)
        decEq f (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq _ (x :: xs) (x :: ys) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq _ (x :: xs) (y :: ys) | (No no)
        = No $ \case Refl => no Refl

  namespace Protocol
    stopCall : Stop = Call x -> Void
    stopCall Refl impossible

    stopRec : Stop = Rec x -> Void
    stopRec Refl impossible

    stopComm : Stop = Comm x y xs -> Void
    stopComm Refl impossible

    stopChoice : Stop = Choice a b c d -> Void
    stopChoice Refl impossible

    callRec : Call y = Rec x -> Void
    callRec Refl impossible

    callComm : Call a = Comm x y xs -> Void
    callComm Refl impossible

    callChoice : Call x = Choice a b c d -> Void
    callChoice Refl impossible

    recComm : Rec a = Comm x y xs -> Void
    recComm Refl impossible

    recChoice : Rec a = Choice x b c d -> Void
    recChoice Refl impossible

    export
    decEq : (x,y : Protocol k rs fs) -> Dec (x === y)
    decEq Stop Stop
      = Yes Refl

    decEq Stop (Call x)
      = No stopCall
    decEq Stop (Rec x)
      = No stopRec
    decEq Stop (Comm x y xs)
      = No stopComm
    decEq Stop (Choice z x y xs)
      = No stopChoice

    decEq (Call x) Stop
      = No (negEqSym stopCall)
    decEq (Call x) (Call y) with (decEq x y)
      decEq (Call x) (Call x) | (Yes Refl)
        = Yes Refl
      decEq (Call x) (Call y) | (No no)
        = No $ \case Refl => no Refl

    decEq (Call x) (Rec y)
      = No callRec
    decEq (Call x) (Comm y z xs)
      = No callComm
    decEq (Call x) (Choice z a y xs)
      = No callChoice

    decEq (Rec x) Stop
      = No (negEqSym stopRec)
    decEq (Rec x) (Call y)
      = No (negEqSym callRec)
    decEq (Rec x) (Rec y) with (decEq x y)
      decEq (Rec x) (Rec x) | (Yes Refl)
        = Yes Refl
      decEq (Rec x) (Rec y) | (No no)
        = No $ \case Refl => no Refl

    decEq (Rec x) (Comm y z xs)
      = No (recComm)
    decEq (Rec x) (Choice a y z xs)
      = No (recChoice)

    decEq (Comm _ _ _) Stop
      = No (negEqSym stopComm)
    decEq (Comm _ _ _) (Call x)
      = No $ negEqSym callComm
    decEq (Comm _ _ _) (Rec _)
      = No $ negEqSym recComm

    decEq {k=LOCAL} (Comm cx rx xs) (Comm cy ry ys) with (decEq cx cy)
      decEq (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) with (decEq rx ry)
        decEq (Comm cx rx xs) (Comm cx rx ys) | (Yes Refl) | (Yes Refl) with (decEq decEq xs ys)
          decEq (Comm cx rx xs) (Comm cx rx xs) | (Yes Refl) | (Yes Refl) | (Yes Refl)
            = Yes Refl
          decEq (Comm cx rx xs) (Comm cx rx ys) | (Yes Refl) | (Yes Refl) | (No no)
            = No $ \case Refl => no Refl
        decEq (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq (Comm cx rx xs) (Comm cy ry ys) | (No no)
        = No $ \case Refl => no Refl

    decEq (Choice _ _ _ _) Stop
      = No (negEqSym stopChoice)
    decEq (Choice _ _ _ _) (Call x)
      = No $ negEqSym callChoice
    decEq (Choice _ _ _ _) (Rec _)
      = No $ negEqSym recChoice

    decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sy ry srny ys) with (decEq sx sy)
      decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx ry srny ys) | (Yes Refl) with (decEq rx ry)
        decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx rx srny ys) | (Yes Refl) | (Yes Refl) with (decEq srnx srny)
          decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx rx srnx ys) | (Yes Refl) | (Yes Refl) | Refl with (decEq decEq xs ys)
            decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx rx srnx xs) | (Yes Refl) | (Yes Refl) | Refl | (Yes Refl) = Yes Refl
            decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx rx srnx ys) | (Yes Refl) | (Yes Refl) | Refl | (No contra)
              = No $ \case Refl => contra Refl

        decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sx ry srny ys) | (Yes Refl) | (No contra)
          = No $ \case Refl => contra Refl
      decEq {k=GLOBAL} (Choice sx rx srnx xs) (Choice sy ry srny ys) | (No contra)
        = No $ \case Refl => contra Refl

-- [ EOF ]
