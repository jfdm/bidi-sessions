module Sessions.Types.Local

import public Decidable.Equality

import public Data.SnocList
import public Data.SnocList.Elem

import public Extra

import public Sessions.Types.Base
import public Sessions.Types.Common

%default total

mutual
  public export
  data Branch : Role.Context -> Fix.Context -> Type
    where
      B : (l : String)
       -> (t : Base)
       -> (k : Local rs fs)
            -> Branch rs fs

  public export
  data Local : Role.Context
            -> Fix.Context
            -> Type
    where
      Stop : Local rs fs
      Call : {n : _}
          -> AtIndex MkFix fs n
          -> Local rs fs
      Rec : Local rs (fs :< MkFix)
         -> Local rs fs
      Comm : CTy
          -> AtIndex r rs n
          -> List (Branch rs fs)
          -> Local rs fs


mutual
  namespace Branch
    export
    decEq : (x,y : Branch rs fs) -> Dec (x === y)
    decEq (B lx tx kx) (B ly ty ky) with (Equality.decEq lx ly)
      decEq (B lx tx kx) (B lx ty ky) | (Yes Refl) with (decEq tx ty)
        decEq (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) with (decEq kx ky)
          decEq (B lx tx kx) (B lx tx kx) | (Yes Refl) | (Yes Refl) | (Yes Refl)
            = Yes Refl
          decEq (B lx tx kx) (B lx tx ky) | (Yes Refl) | (Yes Refl) | (No no)
            = No $ \case Refl => no Refl
        decEq (B lx tx kx) (B lx ty ky) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq (B lx tx kx) (B ly ty ky) | (No no)
        = No $ \case Refl => no Refl

  namespace Branches

    export
    decEq : (x,y : List $ Branch rs fs) -> Dec (x === y)
    decEq [] [] = Yes Refl
    decEq [] (x :: xs)
      = No rightHeavy
    decEq (x :: xs) []
      = No leftHeavy
    decEq (x :: xs) (y :: ys) with (decEq x y)
      decEq (x :: xs) (x :: ys) | (Yes Refl) with (decEq xs ys)
        decEq (x :: xs) (x :: xs) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (x :: xs) (x :: ys) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq (x :: xs) (y :: ys) | (No no)
        = No $ \case Refl => no Refl

  stopCall : Stop = Call x -> Void
  stopCall Refl impossible

  stopRec : Stop = Rec x -> Void
  stopRec Refl impossible

  stopComm : Stop = Comm x y xs -> Void
  stopComm Refl impossible

  callRec : Call y = Rec x -> Void
  callRec Refl impossible

  callComm : Call a = Comm x y xs -> Void
  callComm Refl impossible

  recComm : Rec a = Comm x y xs -> Void
  recComm Refl impossible

  export
  decEq : (x,y : Local rs fs) -> Dec (x === y)
  decEq Stop Stop
    = Yes Refl

  decEq Stop (Call x)
    = No stopCall
  decEq Stop (Rec x)
    = No stopRec
  decEq Stop (Comm x y xs)
    = No stopComm

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

  decEq (Comm _ _ _) Stop
    = No (negEqSym stopComm)
  decEq (Comm _ _ _) (Call x)
    = No $ negEqSym callComm
  decEq (Comm _ _ _) (Rec _)
    = No $ negEqSym recComm

  decEq (Comm cx rx xs) (Comm cy ry ys) with (decEq cx cy)
    decEq (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) with (decEq rx ry)
      decEq (Comm cx rx xs) (Comm cx rx ys) | (Yes Refl) | (Yes Refl) with (decEq xs ys)
        decEq (Comm cx rx xs) (Comm cx rx xs) | (Yes Refl) | (Yes Refl) | (Yes Refl)
          = Yes Refl
        decEq (Comm cx rx xs) (Comm cx rx ys) | (Yes Refl) | (Yes Refl) | (No no)
          = No $ \case Refl => no Refl
      decEq (Comm cx rx xs) (Comm cx ry ys) | (Yes Refl) | (No no)
        = No $ \case Refl => no Refl
    decEq (Comm cx rx xs) (Comm cy ry ys) | (No no)
      = No $ \case Refl => no Refl
-- [ EOF ]
