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


namespace Branch

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
